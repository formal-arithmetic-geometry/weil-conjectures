/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.CategoryTheory.StageSystem.PbcQbarCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCommonStageCones

/-!
# Ordinary middle extension on a smooth curve

Source: blueprint, sec-purity-real-sheaves, sk-i-real-boundary,
`def-wf-middle-extension`; Weil II (1.1.1) b)--d).
(blueprint: def-wf-middle-extension)

Finite-level ordinary direct images are transported to the pro-etale site and
completed coefficients. Their inverse limit is an ordinary module sheaf, placed
in degree zero and rationalized at its original coefficient stage. In particular,
no right-derived direct image is used in this construction.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The geometric hypotheses of the middle-extension definition, bundled without
any extra connectedness, nonemptiness, or geometric irreducibility requirement.
Source: blueprint def-wf-middle-extension (blueprint: def-wf-middle-extension). -/
structure MiddleExtensionCurve (D : WeilConjectures.FiniteFieldDatum.{u}) where
  U : Over (Spec (CommRingCat.of D.k₀))
  C : Over (Spec (CommRingCat.of D.k₀))
  j : U ⟶ C
  [finiteU : LocallyOfFiniteType U.hom]
  [quasiCompactU : QuasiCompact U.hom]
  [finiteC : LocallyOfFiniteType C.hom]
  [quasiCompactC : QuasiCompact C.hom]
  [separatedU : IsSeparated U.hom]
  [separatedC : IsSeparated C.hom]
  [openImmersion : IsOpenImmersion j.left]
  dense : DenseRange j.left.base
  [smooth : Smooth C.hom]
  pureDimension : C.left.IsPureDimension 1

attribute [instance] MiddleExtensionCurve.finiteU MiddleExtensionCurve.finiteC
  MiddleExtensionCurve.quasiCompactU MiddleExtensionCurve.quasiCompactC
  MiddleExtensionCurve.separatedU MiddleExtensionCurve.separatedC
  MiddleExtensionCurve.openImmersion MiddleExtensionCurve.smooth

variable (l : ℕ) [Fact l.Prime] (Qbar : Type (u + 1)) [Field Qbar]
  [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]

end AlgebraicGeometry.Scheme
