//===- MCModuleYAML.h - MCModule YAMLIO implementation ----------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// \brief This file declares classes for handling the YAML representation
/// of MCModule.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_MC_MCANALYSIS_MCMODULEYAML_H
#define LLVM_MC_MCANALYSIS_MCMODULEYAML_H

#include "llvm/ADT/StringRef.h"
#include "llvm/MC/MCAnalysis/MCModule.h"
#include "llvm/Support/raw_ostream.h"

#define LLVM_DELETED_FUNCTION
namespace llvm {

class MCInstrInfo;
class MCRegisterInfo;

/// \brief Dump a YAML representation of the MCModule \p MCM to \p OS.
/// \returns The empty string on success, an error message on failure.
StringRef mcmodule2yaml(raw_ostream &OS, const MCModule &MCM,
                        const MCInstrInfo &MII, const MCRegisterInfo &MRI);

/// \brief Creates a new module and returns it in \p MCM.
/// \returns The empty string on success, an error message on failure.
StringRef yaml2mcmodule(std::unique_ptr<MCModule> &MCM, StringRef YamlContent,
                        const MCInstrInfo &MII, const MCRegisterInfo &MRI);

} // end namespace llvm

#endif
