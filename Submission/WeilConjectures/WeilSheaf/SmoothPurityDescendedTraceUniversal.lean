/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Submission.WeilConjectures.SmoothPurity.Defs
public import Submission.WeilConjectures.WeilSheaf.SmoothPurityFieldTrace
public import Submission.WeilConjectures.WeilSheaf.SmoothPurityTraceDescent

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# The smooth trace after a change of the base field (A1')

Let `f : X ⟶ Y` be a smooth morphism of pure relative dimension `d` of separated `k₁`-schemes of
finite type, `f' : X' ⟶ Y'` a morphism of `k₂`-schemes with maps `πX : X' ⟶ X`, `πY : Y' ⟶ Y`
(in practice `k₂ = k̄₁` and `f'` the base change of `f` to the geometric fibres), and let
`bc : Rf_! ⋙ πY^* ≅ πX^* ⋙ Rf'_!` be a compact-support base change isomorphism. The smooth trace
`Tr_f : Rf_! ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y` chosen over `k₁` pulls back to a trace
`baseChangedSmoothTrace : Rf'_! πX^* ℚ̄_ℓ,X(d)[2d] ⟶ ℚ̄_ℓ,Y'` over `k₂`. Its transpose under
`Rf'_! ⊣ Rf'^!` is the pulled-back orientation `πX^* γ_f` followed by the exceptional base change
map `smoothUnitBaseChange : πX^* Rf^! ℚ̄_ℓ ⟶ Rf'^! ℚ̄_ℓ` (the mate of `bc`, as in
`CategoryTheory.Adjunction.unitBaseChange`); so the pulled-back trace is universal exactly when
this exceptional base change map is an isomorphism
(`isIso_homEquiv_baseChangedSmoothTrace_of_isIso`).

In `AlgebraicGeometry.WeilComplex`, this is the finite-field input of
`exists_forget_upperShriek_adicConstant_iso_comm_derivedStrIso_of_descendedTrace`
(`DescendedSmoothTraceUniversal`): the equivariance of the descended trace is automatic, and
universality of its carrier reduces to the invertibility of `smoothUnitBaseChange`.

## Status of the remaining input

`IsIso (smoothUnitBaseChange ...)` is the compatibility of `Rf^!` with the change of base field
for a *non-proper* smooth `f` (blueprint `sk-prop-sp-purity-bc` across a field extension, SGA 4½
Th. finitude). The library proves it

* for smooth **proper** `f` along a weakly étale change of base
  (`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_smooth_of_weaklyEtale`, where
  `bc` is proper base change and the mate is `upperShriekBaseChangeOfMap`);
* for an arbitrary proper `f` over a point and the unit
  (`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_unit_point`);
* for same-field cartesian squares with `f` smooth and the base map a closed immersion
  (`ProEtale.CondensedRing.isIso_upperShriekBaseChange_of_smooth_of_isClosedImmersion`).

The relative non-proper smooth case over `k₁ ⟶ k̄₁` is not in the library (this is why K4's
route B closes only the absolute case `Y = Spec k₀`).
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (f' : X' ⟶ Y')
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}
  (bc : boundedConstructibleLowerShriek l f ⋙ boundedConstructibleUpperStarOfMap l πY ≅
    boundedConstructibleUpperStarOfMap l πX ⋙ boundedConstructibleLowerShriek l f')
  (e : (boundedConstructibleUpperStarOfMap l πY).obj (𝟙_ _) ⟶ 𝟙_ _)
  (d : ℕ) [SmoothOfRelativeDimension d f.left]

/-- **The exceptional base change map at the unit** `πX^* Rf^! ℚ̄_ℓ,Y ⟶ Rf'^! ℚ̄_ℓ,Y'`: the mate of
the compact-support base change `bc` under `Rf_! ⊣ Rf^!` and `Rf'_! ⊣ Rf'^!`, followed by
`Rf'^!(e)`. For `f` proper and `bc` proper base change this is
`ProEtale.CondensedRing.upperShriekBaseChangeOfMap` at the unit. -/
abbrev smoothUnitBaseChange :
    (boundedConstructibleUpperStarOfMap l πX).obj
        ((boundedConstructibleUpperShriek l f).obj (𝟙_ _)) ⟶
      (boundedConstructibleUpperShriek l f').obj (𝟙_ _) :=
  Adjunction.unitBaseChange (boundedConstructibleUpperShriekAdjunction l f)
    (boundedConstructibleUpperShriekAdjunction l f') bc.hom e

end AlgebraicGeometry.ProEtale.CondensedRing
