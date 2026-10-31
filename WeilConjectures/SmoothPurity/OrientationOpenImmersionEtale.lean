/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineSpace
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientation
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion

/-!
# The finite orientation of an open immersion

Let `j : U ⟶ X` be a quasi-compact separated open immersion, smooth of relative dimension `0`,
and `Λ` a finite coefficient ring with invertible exponent and a normalized Kummer class. The
orientation `Rj^! Λ_X ≅ Λ_U(0)[0]` of the diagonal argument
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`, blueprint
`thm-pur-diagonal-dualizing-object`) is expected to be the canonical identification
`Rj^! Λ_X ≅ j^* Λ_X ≅ Λ_U ≅ Λ_U(0)[0]`
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_of_isOpenImmersion`): for `j`
the diagonal `U ⟶ U ×_X U` is an isomorphism, the base change map of the dualizing complexes is
the canonical one, and the fundamental class of an isomorphism in codimension `0` is `1`
(the class restricting to the trivial frame classes). This is the finite step of
`ProEtale.CondensedRing.isIntegralSmoothOrientation_integralOpenImmersionOrientation`
(blueprint `det-sp-trace-basic`, part 3: for étale `f` the orientation is the identity).

The statement is deduced from two `sorry`ed inputs:
`AlgebraicGeometry.Etale.sectionInvariantTwistShiftIsoOfSection_of_isOpenImmersion` (the
fundamental class of a section in codimension `0` is `1`) and
`AlgebraicGeometry.Etale.sectionInvariantDiagonalIso_of_isOpenImmersion` (the base change of the
dualizing complex of an open immersion is the canonical one).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [SmoothOfRelativeDimension 0 j] [HasCompactification j] [IsSeparated j] [QuasiCompact j]
  [HasInvertibleExponent Λ U]

/-- The canonical identification of the dualizing complex of a quasi-compact open immersion `g`,
`ω_g = Rg^! Λ_B ≅ D(g^*) Λ_B ≅ Lg^* Λ_B ≅ Λ_V`. -/
noncomputable def dualizingComplexIsoOfIsOpenImmersion {V B : Scheme.{u}} (g : V ⟶ B)
    [IsOpenImmersion g] [HasCompactification g] [QuasiCompact g] :
    dualizingComplex Λ g ≅ constantComplex Λ V :=
  (rightDerivedUpperShriekIsoOfIsOpenImmersion Λ g).app _ ≪≫
    (leftDerivedUpperStarIsoMapDerivedCategory _ g).symm.app _ ≪≫
    leftDerivedUpperStarConstantComplexIso Λ g

/-- The canonical identification `𝒞(g, s) = Ls^* ω_g ≅ Ls^* Λ_V ≅ Λ_B` of the section invariant
of a section `s` of a quasi-compact open immersion `g`, through
`dualizingComplexIsoOfIsOpenImmersion`. -/
noncomputable def sectionInvariantIsoOfIsOpenImmersion {V B : Scheme.{u}} (g : V ⟶ B)
    [IsOpenImmersion g] [HasCompactification g] [QuasiCompact g] (s : B ⟶ V) :
    sectionInvariant Λ g s ≅ constantComplex Λ B :=
  (L((s)^*[ModuleCat.{u + 1} Λ])).mapIso (dualizingComplexIsoOfIsOpenImmersion Λ g) ≪≫
    leftDerivedUpperStarConstantComplexIso Λ s

/-- **The fundamental class of a section in codimension `0` is `1`**: for a section `s` of a
quasi-compact open immersion `g` (smooth of relative dimension `0`, so that `g` is an
isomorphism with inverse `s`), the identification `𝒞(g, s) ≅ Λ_B(0)[0]` of the diagonal argument
(`sectionInvariantTwistShiftIsoOfSection`) is the canonical one: in codimension `0` the frame
classes are the unit classes, so the purity of the section is the canonical
`Rs^! Λ_V ≅ s^* Λ_V ≅ Λ_B`. -/
theorem sectionInvariantTwistShiftIsoOfSection_of_isOpenImmersion {V B : Scheme.{u}} (g : V ⟶ B)
    [SmoothOfRelativeDimension 0 g] [HasCompactification g] [IsOpenImmersion g] [QuasiCompact g]
    (s : B ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) {k : Type u} [Field k]
    (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
    [HasInvertibleExponent Λ V] [HasInvertibleExponent Λ B] :
    sectionInvariantTwistShiftIsoOfSection Λ 0 g s hs aB =
      sectionInvariantIsoOfIsOpenImmersion Λ g s ≪≫ (twistShiftZeroIso Λ B rfl _).symm :=
  sorry

/-- **Base change of the dualizing complex of an open immersion is canonical**: for a
quasi-compact open immersion `j`, the identification `𝒞(p₁, Δ) ≅ ω_j` of the diagonal argument
(`sectionInvariantDiagonalIso`, the inverse of the base change map `Lp₂^* ω_j ⟶ ω_{p₁}` pulled
back along the diagonal) is the canonical identification
`𝒞(p₁, Δ) ≅ Λ_U ≅ ω_j` through `sectionInvariantIsoOfIsOpenImmersion` and
`dualizingComplexIsoOfIsOpenImmersion`. -/
theorem sectionInvariantDiagonalIso_of_isOpenImmersion [QuasiSeparatedSpace X] :
    sectionInvariantDiagonalIso Λ j 0 =
      sectionInvariantIsoOfIsOpenImmersion Λ (pullback.fst j j) (pullback.diagonal j) ≪≫
        (dualizingComplexIsoOfIsOpenImmersion Λ j).symm :=
  sorry

/-- Blueprint `det-sp-trace-basic`, part 3, for an open immersion: **the diagonal orientation of
an open immersion `j` is the canonical identification**
`Rj^! Λ_X ≅ D(j^*) Λ_X ≅ Lj^* Λ_X ≅ Λ_U ≅ Λ_U(0)[0]`. -/
theorem dualizingComplexTwistShiftIso_of_isOpenImmersion {k : Type u} [Field k]
    (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX] :
    dualizingComplexTwistShiftIso Λ j 0 aX =
      (rightDerivedUpperShriekIsoOfIsOpenImmersion Λ j).app _ ≪≫
        (leftDerivedUpperStarIsoMapDerivedCategory _ j).symm.app _ ≪≫
        leftDerivedUpperStarConstantComplexIso Λ j ≪≫ (twistShiftZeroIso Λ U rfl _).symm := by
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated aX
  have : HasInvertibleExponent Λ (pullback j j) := .of_hom (pullback.fst j j)
  rw [dualizingComplexTwistShiftIso, sectionInvariantDiagonalIso_of_isOpenImmersion,
    sectionInvariantTwistShiftIsoOfSection_of_isOpenImmersion]
  rw [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.symm_self_id_assoc,
    dualizingComplexIsoOfIsOpenImmersion, Iso.trans_assoc, Iso.trans_assoc]
  rfl

end AlgebraicGeometry.Etale
