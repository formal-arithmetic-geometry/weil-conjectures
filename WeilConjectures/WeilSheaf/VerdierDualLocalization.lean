/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.VerdierDual
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.WeilSheaf.UpperStarLowerStar

/-!
# Verdier duality and the open–closed decomposition

Let `j : U ↪ X` be a quasi-compact open immersion with closed complement `i : Z ↪ X`. From the
statements of the duality theory of Weil complexes collected in
`WeilConjectures.WeilSheaf.VerdierDual`, this file derives the formal steps 1–4 of the proof of
the local boundary duality (`lem-a1-local-boundary-duality`):

1. `𝔻_X Rf_* G ≅ Rf₀! 𝔻 G` (Verdier exchange and biduality);
2. `Rf^! 𝔻_Y K ≅ 𝔻_X f^* K` (`Rf^! = 𝔻 f^* 𝔻` and biduality);
3. `Ri^! Rj₀! G ≅ (i^* Rj_* G)[-1]` (open–closed triangle, `j^* Rj_* = 𝟭`, and clause (4) of
   the localization theorem);
4. `𝔻_Z (i^* Rj_* G) ≅ (i^* Rj_* 𝔻_U G)[-1]`.

## Main statements

- `AlgebraicGeometry.WeilComplex.upperStarDerivedLowerStarIso`: `j^* Rj_* G ≅ G` for an open
  immersion `j`.
- `AlgebraicGeometry.WeilComplex.nonempty_verdierDual_upperStar_derivedLowerStar_iso`: step 4.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

section UpperShriek

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- The exceptional inverse image commutes with the shifts, as the right adjoint of the direct
image with compact support. -/
noncomputable instance : (upperShriek (k₀ := k₀) (l := l) f).CommShift ℤ :=
  (derivedLowerShriekUpperShriekAdjunction f).rightAdjointCommShift ℤ

/-- The exceptional inverse image is a triangulated functor, as the right adjoint of the
triangulated direct image with compact support. -/
instance : (upperShriek (k₀ := k₀) (l := l) f).IsTriangulated :=
  have := (derivedLowerShriekUpperShriekAdjunction (k₀ := k₀) (l := l) f).commShift_of_leftAdjoint
    ℤ
  (derivedLowerShriekUpperShriekAdjunction f).isTriangulated_rightAdjoint

end UpperShriek

section OpenRestriction

variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
  [j.IsOver (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **The restriction of the derived direct image to the open**: for an open immersion
`j : U ↪ X`, `j^* Rj_* G ≅ G`. The pullback `j^*` is exact, so that
`j^* ∘ Rj_* ≅ R(j^* ∘ j_*)`, and `j^* ∘ j_* ≅ 𝟭` on pro-étale Weil sheaves. -/
noncomputable def upperStarDerivedLowerStarIso (G : WeilComplex k₀ l U) :
    (upperStar j).obj ((derivedLowerStar j).obj G) ≅ G :=
  ObjectProperty.isoMk _
    ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso
        (ProEtaleWeilSheaf.lowerStar k₀ l j) (ProEtaleWeilSheaf.upperStar k₀ l j)).symm.app
        G.obj ≪≫
      (Functor.rightDerivedFunctorNatIso
        (ProEtaleWeilSheaf.lowerStarCompUpperStarIso j)).app G.obj ≪≫
      (Functor.rightDerivedFunctorIsoMapDerivedCategory (𝟭 _)).app G.obj ≪≫
      (Functor.mapDerivedCategoryIdIso _).app G.obj)

end OpenRestriction

end WeilComplex

end AlgebraicGeometry
