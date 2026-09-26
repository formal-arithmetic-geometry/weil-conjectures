/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module  -- shake: keep-all

public import WeilConjectures.Blueprint.AbelianVarieties
public import WeilConjectures.Blueprint.AlgebraicGroupsLieAlgebras
public import WeilConjectures.Blueprint.CurveEstimates
public import WeilConjectures.Blueprint.DeligneLaumonAffineLine
public import WeilConjectures.Blueprint.DeligneLaumonGeneral
public import WeilConjectures.Blueprint.FourierTransform
public import WeilConjectures.Blueprint.NagataCompactification
public import WeilConjectures.Blueprint.PicardFramework
public import WeilConjectures.Blueprint.PoincareDuality
public import WeilConjectures.Blueprint.ProperBaseChange
public import WeilConjectures.Blueprint.PurityRealSheaves
public import WeilConjectures.Blueprint.SixFunctors
public import WeilConjectures.Blueprint.SmoothBaseChange
public import WeilConjectures.Blueprint.SmoothPurity
public import WeilConjectures.Blueprint.TraceFormula
public import WeilConjectures.Blueprint.ZetaWeil

/-!
# Statements of the sketch blueprint blocks

This file imports the `WeilConjectures.Blueprint.*` modules. There is one such module per
block of the sketch blueprint, the repository
`formal-arithmetic-geometry/weil-conjectures-blueprint`, named after its block:
`WeilConjectures.Blueprint.AbelianVarieties` is `sec-abelian-varieties`, and so on. The
module docstrings say which block a module is for and what mathematics is in it.

Every subsection of a block that states a definition or a result has a corresponding
`def` or `theorem` in its module, and theorem proofs are `sorry` until they are filled
in. Subsections that are pure remarks (`sk-rem-*`, `sk-audit-*`) carry no declaration,
and neither does one whose statement is already formalized elsewhere in this repository:
a module docstring names the existing development instead, and the module builds on it
rather than restating it.

The `sec-*` names are blocks of that repository. They are not labels of the LaTeX
blueprint in `blueprint/src`, which is what the per-declaration `(blueprint: ...)` tags
elsewhere in this repository refer to.
-/
