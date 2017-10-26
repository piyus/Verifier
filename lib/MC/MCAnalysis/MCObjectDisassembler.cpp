//===- lib/MC/MCObjectDisassembler.cpp ------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "X86GenInstrInfo.h"
#include "llvm/MC/MCObjectDisassembler.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/Twine.h"
#include "llvm/MC/MCAnalysis/MCAtom.h"
#include "llvm/MC/MCAnalysis/MCFunction.h"
#include "llvm/MC/MCAnalysis/MCModule.h"
#include "llvm/MC/MCDisassembler/MCDisassembler.h"
#include "llvm/MC/MCInstrAnalysis.h"
#include "llvm/MC/MCObjectSymbolizer.h"
#include "llvm/Object/MachO.h"
#include "llvm/Object/ObjectFile.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/MachO.h"
#include "llvm/Support/MemoryObject.h"
//#include "llvm/Support/StringRefMemoryObject.h"
#include "llvm/Support/raw_ostream.h"
#include <map>

using namespace llvm;
using namespace object;

#define DEBUG_TYPE "mc"

const uint64_t UnknownAddressOrSize = ~0ULL;

#define _ERROR(x)   { if (errorToErrorCode(x.takeError())) { outs() << "error--\n"; } }



MCObjectDisassembler::MCObjectDisassembler(const ObjectFile &Obj,
                                           const MCDisassembler &Dis,
                                           const MCInstrAnalysis &MIA)
    : Obj(Obj), Dis(Dis), MIA(MIA), MOS(nullptr) {}

uint64_t MCObjectDisassembler::getEntrypoint() {
  for (const SymbolRef &Symbol : Obj.symbols()) {
    Expected<StringRef> _Name = Symbol.getName();
	_ERROR(_Name);
	if (_Name->empty())
	{
		continue;
	}
	StringRef Name = *_Name;
	//outs() << "SYM: " << Name << "\n";
    if (Name == "main" || Name == "_main") {
      Expected<uint64_t> _Entrypoint = Symbol.getAddress();
		_ERROR(_Entrypoint);
	  uint64_t Entrypoint = *_Entrypoint;
      return getEffectiveLoadAddr(Entrypoint);
    }
  }
  return 0;
}

ArrayRef<uint64_t> MCObjectDisassembler::getStaticInitFunctions() {
  return ArrayRef<uint64_t>();
}

ArrayRef<uint64_t> MCObjectDisassembler::getStaticExitFunctions() {
  return ArrayRef<uint64_t>();
}

MemoryObject *MCObjectDisassembler::getRegionFor(uint64_t Addr) {
  // FIXME: Keep track of object sections.
  return FallbackRegion.get();
}

uint64_t MCObjectDisassembler::getEffectiveLoadAddr(uint64_t Addr) {
  return Addr;
}

uint64_t MCObjectDisassembler::getOriginalLoadAddr(uint64_t Addr) {
  return Addr;
}

MCModule *MCObjectDisassembler::buildEmptyModule() {
  MCModule *Module = new MCModule;
  Module->Entrypoint = getEntrypoint();
  return Module;
}

MCModule *MCObjectDisassembler::buildModule(bool withCFG, int start) {
  MCModule *Module = buildEmptyModule();

 buildSectionAtoms(Module);
  if (withCFG)
    buildCFG(Module, start);
  return Module;
}

static const uint8_t PublicRetCfiVal[]
= {
	0x49, 0xBB, 0x6F, 0x6F, 0x6F, 0x6F,
	0x6F, 0x6F, 0x6F, 0x6F,
	0x49, 0xF7, 0xD3,
	0x4D, 0x39, 0x1A,
	0x75, 0x9,
	0x41, 0x5B,
	0x49, 0x83, 0xC2, 0x08,
	0x41, 0xFF, 0xE2,
	0xCC
  };

static bool IsIndirectRet(const uint8_t *buf)
{
	size_t len = sizeof(PublicRetCfiVal);
	size_t i;

	for (i = 0; i < len; i++)
	{
		if (PublicRetCfiVal[i] != buf[i])
		{
			return false;
		}
	}
	return true;
}


void MCObjectDisassembler::buildSectionAtoms(MCModule *Module) {
  for (const SectionRef &Section : Obj.sections()) 
  {
    bool isText;
    isText = Section.isText();
    bool isData;
    isData = Section.isData();

    if (!isData && !isText)
	{
      continue;
	}
    Expected<uint64_t> _StartAddr = Section.getAddress();
	_ERROR(_StartAddr);
	uint64_t StartAddr = *_StartAddr;
    Expected<uint64_t> _SecSize = Section.getSize();
	_ERROR(_SecSize);
	uint64_t SecSize = *_SecSize;
    if (StartAddr == UnknownAddressOrSize || SecSize == UnknownAddressOrSize)
      continue;

    StringRef Contents;
    Section.getContents(Contents);
	ArrayRef<uint8_t> memoryObject(reinterpret_cast<const uint8_t *>(Contents.data()),
                                   Contents.size());

    StringRef SecName;
	Section.getName(SecName);
    if (Contents.size() != SecSize || !SecSize)
	{
      continue;
	}

	if (isText)
	{
		MCTextAtom *Text = nullptr;

		uint64_t InstSize;
		bool foundFunc = false;
		uint64_t lastSeenBranch = 0;
		uint8_t tag = 0;
		const char *data = Contents.data();
		bool lastInstWasCall = false;
		bool debugThisFunc = false;
		uint64_t entryAddr = 0;


		for (uint64_t Index = 0; Index < SecSize; Index += InstSize)
		{
			const uint64_t CurAddr = StartAddr + Index;
			MCInst Inst;


			if (foundFunc)
			{
				if (lastInstWasCall)
				{
					assert(Text);
					assert(((uint64_t*)(&data[Index]))[0] == 0x9090909090909090);
					Inst.setOpcode(X86::CFI_INSTRUCTION);
					InstSize = 8;
					Text->addInst(Inst, InstSize);
					lastInstWasCall = false;
					continue;
				}
				if (IsIndirectRet((const uint8_t*)&data[Index]))
				{
					Inst.setOpcode(X86::RET);
					InstSize = sizeof(PublicRetCfiVal) - 1;
					Text->addInst(Inst, InstSize);
					continue;
				}
			}

			if (*(uint64_t*)(&data[Index]) == 0x9A9A9A9A9A9A9A9A)
			{
				foundFunc = true;
				lastInstWasCall = false;
				InstSize = 16;
				tag = data[Index + 8];
				Text = nullptr;
				//debugThisFunc = (CurAddr + InstSize == 0x180032990);
				entryAddr = CurAddr + InstSize;
			}
			else
			{
				if (!foundFunc)
				{
					InstSize = 1;
				}
				else if (Dis.getInstruction(Inst, InstSize, memoryObject.slice(Index), CurAddr, nulls(),
					nulls()))
				{

					if (foundFunc)
					{
						uint64_t Target;
						if (!Text)
						{
							Text = Module->createTextAtom(CurAddr, CurAddr + InstSize - 1);
							Text->setName(SecName);
							Text->setSignature(tag);
						}

						if (MIA.isIndirectBranch(Inst))
						{
							if (debugThisFunc)
							{
								printf("found indirect branch at: %llx\n", CurAddr);
							}
							Inst.setOpcode(X86::CFI_INSTRUCTION);
							Text->addInst(Inst, InstSize);
							/* if next instruction is ret it is a stub*/
							/* FIXME */
							if ((uint8_t)data[Index + InstSize] != 0xC3)
							{
								printf("inst: %hhx InstSize:%zd addr:%llx\n", data[Index + InstSize], InstSize, CurAddr);
							}
							assert((uint8_t)data[Index + InstSize] == 0xC3);
							assert(CurAddr >= lastSeenBranch);
							foundFunc = false;
							Text = nullptr;
							continue;
						}

						Text->addInst(Inst, InstSize);

						if (!MIA.isCall(Inst) && MIA.evaluateBranch(Inst, CurAddr, InstSize, Target))
						{
							if (Target < entryAddr)
							{
								printf("Jumping before function %llx %llx\n", entryAddr, Target);
								assert(0);
							}
							if (lastSeenBranch < Target)
							{
								lastSeenBranch = Target;
							}
						}

						lastInstWasCall = MIA.isCall(Inst);

						if (lastInstWasCall)
						{
							assert(Inst.getOpcode() == X86::CALL64pcrel32 || Inst.getOpcode() == X86::CALL64r);
						}

						assert(!MIA.isReturn(Inst));
						if (MIA.isUnconditionalBranch(Inst) || Inst.getOpcode() == X86::INT3)
						{
							if (CurAddr >= lastSeenBranch)
							{
								if (debugThisFunc)
								{
									printf("found unconditional branch at: %llx lastSeenBranch:%llx\n", 
											CurAddr, lastSeenBranch);
								}
								foundFunc = false;
								Text = nullptr;

							}
						}
					}
				}
				else
				{
					assert(InstSize && "getInstruction() consumed no bytes");
					Text = nullptr;
				}
			} // end for loop
		} // end if
	}
  } // end for
}

namespace {
  struct BBInfo;
  typedef SmallPtrSet<BBInfo*, 2> BBInfoSetTy;
  struct BBInfo {
    MCTextAtom *Atom;
    MCBasicBlock *BB;
    BBInfoSetTy Succs;
    BBInfoSetTy Preds;
    MCObjectDisassembler::AddressSetTy SuccAddrs;

    BBInfo() : Atom(nullptr), BB(nullptr) {}

    void addSucc(BBInfo &Succ) {
      Succs.insert(&Succ);
      Succ.Preds.insert(this);
    }
  };
}

static void RemoveDupsFromAddressVector(MCObjectDisassembler::AddressSetTy &V) {
  std::sort(V.begin(), V.end());
  V.erase(std::unique(V.begin(), V.end()), V.end());
}

void MCObjectDisassembler::buildCFG(MCModule *Module, int start) {
  typedef std::map<uint64_t, BBInfo> BBInfoByAddrTy;
  BBInfoByAddrTy BBInfos;
  AddressSetTy Splits;
  AddressSetTy Calls;
  AddressSetTy Funcs;

  for (const SymbolRef &Symbol : Obj.symbols()) {
    Expected<SymbolRef::Type> _SymType = Symbol.getType();
	_ERROR(_SymType);
	SymbolRef::Type SymType = *_SymType;
    if (SymType == SymbolRef::ST_Function) {
      Expected<uint64_t> _SymAddr = Symbol.getAddress();
	  _ERROR(_SymAddr);
	  uint64_t SymAddr = *_SymAddr;
      SymAddr = getEffectiveLoadAddr(SymAddr);
      Calls.push_back(SymAddr);
      Splits.push_back(SymAddr);
    }
  }

  assert(Module->func_begin() == Module->func_end()
         && "Module already has a CFG!");

  for (MCModule::atom_iterator AI = Module->atom_begin(),
                               AE = Module->atom_end();
       AI != AE; ++AI) {
    MCTextAtom *TA = dyn_cast<MCTextAtom>(*AI);
    if (!TA) continue;

    Calls.push_back(TA->getBeginAddr());
    BBInfos[TA->getBeginAddr()].Atom = TA;
  }


  const size_t MaxFuncSize = (16 << 12); // 16 pages
  int iter = -1;
  uint64_t totalSize = 0, curSize;
  bool debugThisFunc = false;

  // First, determine the basic block boundaries and call targets.
  for (MCModule::atom_iterator AI = Module->atom_begin(),
                               AE = Module->atom_end();
       AI != AE; ++AI) {
    MCTextAtom *TA = dyn_cast<MCTextAtom>(*AI);
    if (!TA) continue;
	iter++;
	if (iter < start)
	{
		continue;
	}

	if (debugThisFunc)
	{
		break;
	}
	//debugThisFunc = (TA->getBeginAddr() == 0x1800C9CB0);
	if (debugThisFunc && totalSize)
	{
		debugThisFunc = false;
		break;
	}

	curSize = TA->getEndAddr() - TA->getBeginAddr();
	if (curSize > MaxFuncSize)
	{
		printf("Single very large function! %llx -> %lld\n", 
			   TA->getBeginAddr(), curSize);
		continue;
	}
	totalSize += curSize;
	if (totalSize > MaxFuncSize)
	{
		break;
	}

	Funcs.push_back(TA->getBeginAddr());

    for (MCTextAtom::const_iterator II = TA->begin(), IE = TA->end();
         II != IE; ++II) 
	{
	  MCAtom *A;
	  
	  if (debugThisFunc == true)
	  {
		  printf("inst: %llx\n", II->Address);
	  }
      if (MIA.isTerminator(II->Inst) || II->Inst.getOpcode() == X86::INT3)
	  {
		  if (II->Address + II->Size < TA->getEndAddr())
		  {
			  A = Module->findAtomContaining(II->Address + II->Size);
			  if (!A || !isa<MCTextAtom>(A))
			  {
				  II->Inst.dump_pretty(outs());
				  printf("\nUnable to fetch target2: %llx -- %llx,%llx\n", 
					  II->Address + II->Size, TA->getBeginAddr(), TA->getEndAddr());
				  continue;
			  }
			  Splits.push_back(II->Address + II->Size);
			  if (debugThisFunc)
			  {
				  printf("Splits terminator : %llx \n", II->Address + II->Size);
			  }
		  }
	  }
	  if (MIA.isCall(II->Inst))
	  {
			  if (debugThisFunc)
			  {
				  printf("Splits calls : %llx\n", II->Address + II->Size);
			  }
		  Splits.push_back(II->Address + II->Size);
	  }
      uint64_t Target;
      if (MIA.evaluateBranch(II->Inst, II->Address, II->Size, Target)) {
        if (MIA.isCall(II->Inst))
		{
          Calls.push_back(Target);
		}
        Splits.push_back(Target);
		if (debugThisFunc)
		{
		    printf("Splits branch : %llx\n", Target);
		}

    	A = Module->findAtomContaining(Target);
		if (!A || !isa<MCTextAtom>(A))
		{
			II->Inst.dump_pretty(outs());
			printf("\nUnable to fetch target3: %llx  -- %llx\n", Target, TA->getBeginAddr());
			continue;
		}

      }
    }
  }

  RemoveDupsFromAddressVector(Splits);
  RemoveDupsFromAddressVector(Calls);

  // Split text atoms into basic block atoms.
  for (AddressSetTy::const_iterator SI = Splits.begin(), SE = Splits.end();
       SI != SE; ++SI) {
    MCAtom *A = Module->findAtomContaining(*SI);
	if (!A || !isa<MCTextAtom>(A))
	{
		printf("Unable to fetch target: %llx\n", *SI);
		continue;
	}

    MCTextAtom *TA = cast<MCTextAtom>(A);
    if (TA->getBeginAddr() == *SI)
      continue;

	if (debugThisFunc)
	{
	    printf("Creating SPLIT for : %llx\n", *SI);
	}

    MCTextAtom *NewAtom = TA->split(*SI);
    BBInfos[NewAtom->getBeginAddr()].Atom = NewAtom;
    StringRef BBName = TA->getName();
    BBName = BBName.substr(0, BBName.find_last_of(':'));
    NewAtom->setName((BBName + ":" + utohexstr(*SI)).str());
  }

  // Compute succs/preds.
  for (MCModule::atom_iterator AI = Module->atom_begin(),
                               AE = Module->atom_end();
                               AI != AE; ++AI) {
    MCTextAtom *TA = dyn_cast<MCTextAtom>(*AI);
    if (!TA) continue;
    BBInfo &CurBB = BBInfos[TA->getBeginAddr()];
    const MCDecodedInst &LI = TA->back();

	if (MIA.isCall(LI.Inst))
	{
    	uint64_t Target;

    	if (MIA.evaluateBranch(LI.Inst, LI.Address, LI.Size, Target))
	  	{
			MCTextAtom *CallA = BBInfos[Target].Atom;
			assert(CallA && "call traget doesn't have an atom!");
			CurBB.Atom->setCallTag(CallA->getSignature());
	  	}
	}

    if (MIA.isBranch(LI.Inst)) {
      uint64_t Target;

      if (MIA.evaluateBranch(LI.Inst, LI.Address, LI.Size, Target))
	  {
		if (debugThisFunc)
		{
	    	printf("Adding Successor %llx : %llx\n", LI.Address, Target);
		}
        CurBB.addSucc(BBInfos[Target]);
	  }
      if (MIA.isConditionalBranch(LI.Inst))
	  {
		if (debugThisFunc)
		{
	    	printf("Adding coditional Successor : %llx\n", LI.Address + LI.Size);
		}
        CurBB.addSucc(BBInfos[LI.Address + LI.Size]);
	  }
    }
	else if (!MIA.isTerminator(LI.Inst) && LI.Inst.getOpcode() != X86::INT3)
	{
		if (debugThisFunc)
		{
	    	printf("Adding non-term Successor : %llx\n", LI.Address + LI.Size);
		}
      CurBB.addSucc(BBInfos[LI.Address + LI.Size]);
	}
  }

  // Create functions and basic blocks.
  for (AddressSetTy::const_iterator CI = Funcs.begin(), CE = Funcs.end();
       CI != CE; ++CI) {
    BBInfo &BBI = BBInfos[*CI];
    if (!BBI.Atom) continue;

    MCFunction &MCFN = *Module->createFunction(BBI.Atom->getName());

    // Create MCBBs.
    SmallSetVector<BBInfo*, 16> Worklist;
    Worklist.insert(&BBI);
    for (size_t wi = 0; wi < Worklist.size(); ++wi) {
      BBInfo *BBI = Worklist[wi];
      if (!BBI->Atom)
	  {
		if (debugThisFunc)
		{
			printf("no ATOM found -- for BBI %p\n", BBI);
		}
        continue;
	  }
	  if (debugThisFunc)
	  {
	  	printf("Atom going ON: %llx\n", BBI->Atom->getBeginAddr());
	  }
      BBI->BB = &MCFN.createBlock(*BBI->Atom);
      // Add all predecessors and successors to the worklist.
      for (BBInfoSetTy::iterator SI = BBI->Succs.begin(), SE = BBI->Succs.end();
                                 SI != SE; ++SI)
	  {
        Worklist.insert(*SI);
	  }
      for (BBInfoSetTy::iterator PI = BBI->Preds.begin(), PE = BBI->Preds.end();
                                 PI != PE; ++PI)
	  {
        Worklist.insert(*PI);
	  }
    }

    // Set preds/succs.
    for (size_t wi = 0; wi < Worklist.size(); ++wi) {
      BBInfo *BBI = Worklist[wi];
      MCBasicBlock *MCBB = BBI->BB;
      if (!MCBB)
        continue;
      for (BBInfoSetTy::iterator SI = BBI->Succs.begin(), SE = BBI->Succs.end();
           SI != SE; ++SI)
        if ((*SI)->BB)
          MCBB->addSuccessor((*SI)->BB);
      for (BBInfoSetTy::iterator PI = BBI->Preds.begin(), PE = BBI->Preds.end();
           PI != PE; ++PI)
        if ((*PI)->BB)
          MCBB->addPredecessor((*PI)->BB);
    }
  }
}

// Basic idea of the disassembly + discovery:
//
// start with the wanted address, insert it in the worklist
// while worklist not empty, take next address in the worklist:
// - check if atom exists there
//   - if middle of atom:
//     - split basic blocks referencing the atom
//     - look for an already encountered BBInfo (using a map<atom, bbinfo>)
//       - if there is, split it (new one, fallthrough, move succs, etc..)
//   - if start of atom: nothing else to do
//   - if no atom: create new atom and new bbinfo
// - look at the last instruction in the atom, add succs to worklist
// for all elements in the worklist:
// - create basic block, update preds/succs, etc..
//
MCBasicBlock *MCObjectDisassembler::getBBAt(MCModule *Module, MCFunction *MCFN,
                                            uint64_t BBBeginAddr,
                                            AddressSetTy &CallTargets,
                                            AddressSetTy &TailCallTargets) {
  typedef std::map<uint64_t, BBInfo> BBInfoByAddrTy;
  typedef SmallSetVector<uint64_t, 16> AddrWorklistTy;
  BBInfoByAddrTy BBInfos;
  AddrWorklistTy Worklist;

  Worklist.insert(BBBeginAddr);
  for (size_t wi = 0; wi < Worklist.size(); ++wi) {
    const uint64_t BeginAddr = Worklist[wi];
    BBInfo *BBI = &BBInfos[BeginAddr];

    MCTextAtom *&TA = BBI->Atom;
    assert(!TA && "Discovered basic block already has an associated atom!");

    // Look for an atom at BeginAddr.
    if (MCAtom *A = Module->findAtomContaining(BeginAddr)) {
      // FIXME: We don't care about mixed atoms, see above.
      TA = cast<MCTextAtom>(A);

      // The found atom doesn't begin at BeginAddr, we have to split it.
      if (TA->getBeginAddr() != BeginAddr) {
        // FIXME: Handle overlapping atoms: middle-starting instructions, etc..
        MCTextAtom *NewTA = TA->split(BeginAddr);

        // Look for an already encountered basic block that needs splitting
        BBInfoByAddrTy::iterator It = BBInfos.find(TA->getBeginAddr());
        if (It != BBInfos.end() && It->second.Atom) {
          BBI->SuccAddrs = It->second.SuccAddrs;
          It->second.SuccAddrs.clear();
          It->second.SuccAddrs.push_back(BeginAddr);
        }
        TA = NewTA;
      }
      BBI->Atom = TA;
    } else {
      // If we didn't find an atom, then we have to disassemble to create one!

      MemoryObject *Region = getRegionFor(BeginAddr);
      if (!Region)
        llvm_unreachable(("Couldn't find suitable region for disassembly at " +
                          utostr(BeginAddr)).c_str());

      uint64_t InstSize;
      uint64_t EndAddr = Region->getExtent();

      // We want to stop before the next atom and have a fallthrough to it.
      if (MCTextAtom *NextAtom =
              cast_or_null<MCTextAtom>(Module->findFirstAtomAfter(BeginAddr)))
        EndAddr = std::min(EndAddr, NextAtom->getBeginAddr());

	  uint64_t sz = EndAddr - BeginAddr;
	  uint8_t *_buf = (uint8_t*)malloc(sz);
	  Region->readBytes(_buf, sz, BeginAddr);
      ArrayRef<uint8_t> _bufref(_buf, sz);


      for (uint64_t Addr = BeginAddr; Addr < EndAddr; Addr += InstSize) {
        MCInst Inst;
        if (Dis.getInstruction(Inst, InstSize, _bufref.slice(BeginAddr), Addr, nulls(),
                               nulls())) {
          if (!TA)
		  {
			 // outs() << __FUNCTION__ << " : " << __LINE__ << "\n";
            TA = Module->createTextAtom(Addr, Addr);
		  }
          TA->addInst(Inst, InstSize);
        } else {
          // We don't care about splitting mixed atoms either.
          llvm_unreachable("Couldn't disassemble instruction in atom.");
        }

        uint64_t BranchTarget;
        if (MIA.evaluateBranch(Inst, Addr, InstSize, BranchTarget)) {
          if (MIA.isCall(Inst))
            CallTargets.push_back(BranchTarget);
        }

        if (MIA.isTerminator(Inst) || Inst.getOpcode() == X86::INT3)
          break;
      }
	  free(_buf);
      BBI->Atom = TA;
    }

    assert(TA && "Couldn't disassemble atom, none was created!");
    assert(TA->begin() != TA->end() && "Empty atom!");

    MemoryObject *Region = getRegionFor(TA->getBeginAddr());
    assert(Region && "Couldn't find region for already disassembled code!");
    uint64_t EndRegion = Region->getExtent();

    // Now we have a basic block atom, add successors.
    // Add the fallthrough block.
    if ((MIA.isConditionalBranch(TA->back().Inst) ||
         !(MIA.isTerminator(TA->back().Inst) || 
		   TA->back().Inst.getOpcode() == X86::INT3)) &&
        (TA->getEndAddr() + 1 < EndRegion)) {
      BBI->SuccAddrs.push_back(TA->getEndAddr() + 1);
      Worklist.insert(TA->getEndAddr() + 1);
    }

    // If the terminator is a branch, add the target block.
    if (MIA.isBranch(TA->back().Inst)) {
      uint64_t BranchTarget;
      if (MIA.evaluateBranch(TA->back().Inst, TA->back().Address,
                             TA->back().Size, BranchTarget)) {
        StringRef ExtFnName;
        if (MOS)
          ExtFnName =
              MOS->findExternalFunctionAt(getOriginalLoadAddr(BranchTarget));
        if (!ExtFnName.empty()) {
          TailCallTargets.push_back(BranchTarget);
          CallTargets.push_back(BranchTarget);
        } else {
          BBI->SuccAddrs.push_back(BranchTarget);
          Worklist.insert(BranchTarget);
        }
      }
    }
  }

  for (size_t wi = 0, we = Worklist.size(); wi != we; ++wi) {
    const uint64_t BeginAddr = Worklist[wi];
    BBInfo *BBI = &BBInfos[BeginAddr];

    assert(BBI->Atom && "Found a basic block without an associated atom!");

    // Look for a basic block at BeginAddr.
    BBI->BB = MCFN->find(BeginAddr);
    if (BBI->BB) {
      // FIXME: check that the succs/preds are the same
      continue;
    }
    // If there was none, we have to create one from the atom.
    BBI->BB = &MCFN->createBlock(*BBI->Atom);

	/*if (BBI->hasTag())
	{
	    BBI->BB->setTag(BBI->getTag());
	}*/
  }

  for (size_t wi = 0, we = Worklist.size(); wi != we; ++wi) {
    const uint64_t BeginAddr = Worklist[wi];
    BBInfo *BBI = &BBInfos[BeginAddr];
    MCBasicBlock *BB = BBI->BB;

	/*if (BBI->hasTag())
	{
		assert(BB->hasTag());
	    //BBI->BB->setTag(BBI->getTag());
	}*/

    RemoveDupsFromAddressVector(BBI->SuccAddrs);
    for (AddressSetTy::const_iterator SI = BBI->SuccAddrs.begin(),
         SE = BBI->SuccAddrs.end();
         SE != SE; ++SI) {
      MCBasicBlock *Succ = BBInfos[*SI].BB;
      BB->addSuccessor(Succ);
      Succ->addPredecessor(BB);
    }
  }

  assert(BBInfos[Worklist[0]].BB &&
         "No basic block created at requested address?");

  return BBInfos[Worklist[0]].BB;
}

MCFunction *
MCObjectDisassembler::createFunction(MCModule *Module, uint64_t BeginAddr,
                                     AddressSetTy &CallTargets,
                                     AddressSetTy &TailCallTargets) {
  // First, check if this is an external function.
  StringRef ExtFnName;
  if (MOS)
    ExtFnName = MOS->findExternalFunctionAt(getOriginalLoadAddr(BeginAddr));
  if (!ExtFnName.empty())
    return Module->createFunction(ExtFnName);

  // If it's not, look for an existing function.
  for (MCModule::func_iterator FI = Module->func_begin(),
                               FE = Module->func_end();
       FI != FE; ++FI) {
    if ((*FI)->empty())
      continue;
    // FIXME: MCModule should provide a findFunctionByAddr()
    if ((*FI)->getEntryBlock()->getInsts()->getBeginAddr() == BeginAddr)
      return FI->get();
  }

  // Finally, just create a new one.
  MCFunction *MCFN = Module->createFunction("");
  getBBAt(Module, MCFN, BeginAddr, CallTargets, TailCallTargets);
  return MCFN;
}

#if 0
// MachO MCObjectDisassembler implementation.

MCMachOObjectDisassembler::MCMachOObjectDisassembler(
    const MachOObjectFile &MOOF, const MCDisassembler &Dis,
    const MCInstrAnalysis &MIA, uint64_t VMAddrSlide,
    uint64_t HeaderLoadAddress)
    : MCObjectDisassembler(MOOF, Dis, MIA), MOOF(MOOF),
      VMAddrSlide(VMAddrSlide), HeaderLoadAddress(HeaderLoadAddress) {

  for (const SectionRef &Section : MOOF.sections()) {
    StringRef Name;
    Section.getName(Name);
    // FIXME: We should use the S_ section type instead of the name.
    if (Name == "__mod_init_func") {
      DEBUG(dbgs() << "Found __mod_init_func section!\n");
      Section.getContents(ModInitContents);
    } else if (Name == "__mod_exit_func") {
      DEBUG(dbgs() << "Found __mod_exit_func section!\n");
      Section.getContents(ModExitContents);
    }
  }
}

// FIXME: Only do the translations for addresses actually inside the object.
uint64_t MCMachOObjectDisassembler::getEffectiveLoadAddr(uint64_t Addr) {
  return Addr + VMAddrSlide;
}

uint64_t
MCMachOObjectDisassembler::getOriginalLoadAddr(uint64_t EffectiveAddr) {
  return EffectiveAddr - VMAddrSlide;
}

uint64_t MCMachOObjectDisassembler::getEntrypoint() {
  uint64_t EntryFileOffset = 0;

  // Look for LC_MAIN.
  {
    uint32_t LoadCommandCount = MOOF.getHeader().ncmds;
    MachOObjectFile::LoadCommandInfo Load = MOOF.getFirstLoadCommandInfo();
    for (unsigned I = 0;; ++I) {
      if (Load.C.cmd == MachO::LC_MAIN) {
        EntryFileOffset =
            ((const MachO::entry_point_command *)Load.Ptr)->entryoff;
        break;
      }

      if (I == LoadCommandCount - 1)
        break;
      else
        Load = MOOF.getNextLoadCommandInfo(Load);
    }
  }

  // If we didn't find anything, default to the common implementation.
  // FIXME: Maybe we could also look at LC_UNIXTHREAD and friends?
  if (EntryFileOffset)
    return MCObjectDisassembler::getEntrypoint();

  return EntryFileOffset + HeaderLoadAddress;
}

ArrayRef<uint64_t> MCMachOObjectDisassembler::getStaticInitFunctions() {
  // FIXME: We only handle 64bit mach-o
  assert(MOOF.is64Bit());

  size_t EntrySize = 8;
  size_t EntryCount = ModInitContents.size() / EntrySize;
  return ArrayRef<uint64_t>(
      reinterpret_cast<const uint64_t *>(ModInitContents.data()), EntryCount);
}

ArrayRef<uint64_t> MCMachOObjectDisassembler::getStaticExitFunctions() {
  // FIXME: We only handle 64bit mach-o
  assert(MOOF.is64Bit());

  size_t EntrySize = 8;
  size_t EntryCount = ModExitContents.size() / EntrySize;
  return ArrayRef<uint64_t>(
      reinterpret_cast<const uint64_t *>(ModExitContents.data()), EntryCount);
}
#endif
