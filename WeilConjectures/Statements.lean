/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module  -- shake: keep-all

public import WeilConjectures.Statements.AbelianVarieties
public import WeilConjectures.Statements.AlgebraicGroupsLieAlgebras
public import WeilConjectures.Statements.CurveEstimates
public import WeilConjectures.Statements.DeligneLaumonAffineLine
public import WeilConjectures.Statements.DeligneLaumonGeneral
public import WeilConjectures.Statements.FourierTransform
public import WeilConjectures.Statements.NagataCompactification
public import WeilConjectures.Statements.PicardFramework
public import WeilConjectures.Statements.PoincareDuality
public import WeilConjectures.Statements.ProperBaseChange
public import WeilConjectures.Statements.PurityRealSheaves
public import WeilConjectures.Statements.SixFunctors
public import WeilConjectures.Statements.SmoothBaseChange
public import WeilConjectures.Statements.SmoothPurity
public import WeilConjectures.Statements.TraceFormula
public import WeilConjectures.Statements.ZetaWeil

@[expose] public section

/-!
# Statements of the blueprint blocks

This file imports the sixteen `WeilConjectures.Statements.*` modules, one per blueprint
block. Each declaration in those files formalises the sketch statement of one subsection
of its block, with `sorry` for the proof.
-/
