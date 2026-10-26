/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructible
public import WeilConjectures.TraceFormula.Specialization.DefectCentreMap

/-!

# The smooth exchange of nearby cycles for the deformation to the normal cone

For a smooth morphism `f : X ⟶ Y` of separated `k`-schemes of finite type and `J = f⁻¹ I`, the
morphism of deformation models `f̃ : 𝒟_J X ⟶ 𝒟_I Y` is the base change of `f`, hence smooth
(`ProEtale.CondensedRing.smooth_deformationTotalMap`), and its square of geometric generic fibres is
cartesian. By smooth base change, its pullback exchange `α_{f̃} : Lf_s^* Ψ_Y ⟶ Ψ_X Lf^*` is an
isomorphism on bounded constructible `ℚ̄_ℓ`-complexes
(`ProEtale.CondensedRing.isIso_pullbackExchange_deformationModel_app_of_smooth`).

## Sorried input

`ProEtale.CondensedRing.isIso_pullbackExchange_deformationModel_app_of_smooth` is the smooth half
of blueprint `det-sp-nearby-cycles-exchanges` (1), a node of the subsection
`sk-lem-tf-sp-constant-family`, applied to the smooth morphism of deformation models of blueprint
`det-sp-dnc-base-change` (3); it is `sorry`ed, to be proved with that node (smooth base change
`sbc-thm-bounded-derived-smooth-base-change` along the inclusion of the geometric generic fibre).

-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (k' : Type u) [Field k'] [Algebra k k'] [IsSepClosed k']
  [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **The smooth exchange of nearby cycles** (blueprint `det-sp-nearby-cycles-exchanges` (1),
smooth case, for the morphism of deformation models of blueprint `det-sp-dnc-base-change` (3);
SGA 7 XIII 2.1.7.1): for a morphism `φ : 𝒟_J X ⟶ 𝒟_I Y` of deformation models whose morphism of
total spaces is smooth and whose square of geometric generic fibres is cartesian (for instance the
deformation of a smooth `f` with `J = f⁻¹ I`), the pullback exchange `α_φ : Lg_s^* Ψ_Y ⟶ Ψ_X Lg^*`
is an isomorphism on bounded constructible `ℚ̄_ℓ`-complexes, by smooth base change along the
inclusion `j` of the geometric generic fibre. -/
theorem isIso_pullbackExchange_deformationModel_app_of_smooth {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    {I : Y.left.IdealSheafData} {J : X.left.IdealSheafData} {g : X.left ⟶ Y.left}
    {g' : (deformationSpecialFibre X J k').left ⟶ (deformationSpecialFibre Y I k').left}
    (φ : (deformationModel X J k').Hom (deformationModel Y I k') g g') [Smooth φ.total]
    (hj : IsPullback φ.generic (deformationModel X J k').j (deformationModel Y I k').j φ.total)
    {K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y.left))}
    (hK : boundedConstructible _ K) :
    IsIso ((φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app K) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
