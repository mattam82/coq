(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Export Corelib.Init.Notations.
Require Export Corelib.Init.Types.
Require Export Corelib.Init.Tactics.Ltac.
Require Export Corelib.Init.Tactics.Tauto.

Declare ML Module "rocq-runtime.plugins.cc_core".
Declare ML Module "rocq-runtime.plugins.cc".
Declare ML Module "rocq-runtime.plugins.firstorder_core".
Declare ML Module "rocq-runtime.plugins.firstorder".
