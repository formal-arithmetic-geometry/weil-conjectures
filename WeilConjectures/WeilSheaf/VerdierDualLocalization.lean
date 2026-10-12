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

section Exchange

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

/-- **Step 1: the dual of a direct image** (blueprint: `lem-a1-local-boundary-duality`, step 1):
`𝔻_Y Rf_* G ≅ Rf₀! 𝔻_X G`. The Verdier exchange applied to `M = 𝔻_X G` and biduality on `X`
give `𝔻_Y Rf₀! 𝔻_X G ≅ Rf_* G`; applying `𝔻_Y` and biduality on `Y` gives the claim. -/
theorem nonempty_verdierDual_derivedLowerStar_iso (G : WeilComplex k₀ l X) :
    Nonempty ((verdierDual k₀ l Y).obj (op ((derivedLowerStar f).obj G)) ≅
      (derivedLowerShriek k₀ l f).obj ((verdierDual k₀ l X).obj (op G))) := by
  obtain ⟨e⟩ := nonempty_verdierDual_derivedLowerShriek_iso f ((verdierDual k₀ l X).obj (op G))
  obtain ⟨bX⟩ := nonempty_iso_verdierDual_rightOp_comp_verdierDual k₀ l X
  obtain ⟨bY⟩ := nonempty_iso_verdierDual_rightOp_comp_verdierDual k₀ l Y
  let e' : (verdierDual k₀ l Y).obj
      (op ((derivedLowerShriek k₀ l f).obj ((verdierDual k₀ l X).obj (op G)))) ≅
        (derivedLowerStar f).obj G :=
    e ≪≫ (derivedLowerStar f).mapIso (bX.app G).symm
  exact ⟨(verdierDual k₀ l Y).mapIso e'.op ≪≫ (bY.app _).symm⟩

variable [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- **Step 2: the exceptional inverse image of a dual** (blueprint:
`lem-a1-local-boundary-duality`, step 2): `Rf^! 𝔻_Y K ≅ 𝔻_X f^* K`, from `Rf^! = 𝔻_X f^* 𝔻_Y`
and biduality on `Y`. -/
theorem nonempty_upperShriek_verdierDual_iso (K : WeilComplex k₀ l Y) :
    Nonempty ((upperShriek f).obj ((verdierDual k₀ l Y).obj (op K)) ≅
      (verdierDual k₀ l X).obj (op ((upperStar f).obj K))) := by
  obtain ⟨e⟩ := nonempty_upperShriek_obj_iso f ((verdierDual k₀ l Y).obj (op K))
  obtain ⟨bY⟩ := nonempty_iso_verdierDual_rightOp_comp_verdierDual k₀ l Y
  exact ⟨e ≪≫ (verdierDual k₀ l X).mapIso ((upperStar f).mapIso (bY.app K)).op⟩

end Exchange

section Localization

variable {U X Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] [Z.Over (Spec (CommRingCat.of k₀))]
  (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
  (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]

/-- **Step 3: the exceptional restriction of an extension by zero** (blueprint:
`lem-a1-local-boundary-duality`, step 3): for complementary immersions `j` and `i`,
`Ri^! Rj₀! G ≅ (i^* Rj_* G)[-1]`. Apply the triangulated functor `Ri^!` to the open–closed
triangle `Rj₀! j^* Rj_* G ⟶ Rj_* G ⟶ Ri_* i^* Rj_* G ⟶` of `Rj_* G`: the middle term becomes
`Ri^! Rj_* G = 0`, so the third arrow becomes an isomorphism, and the closed unit
`Q ≅ Ri^! Ri₀! Q` with `Ri₀! ≅ Ri_*` identifies the third term with `i^* Rj_* G`. -/
theorem nonempty_upperShriek_derivedLowerShriek_iso
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) (G : WeilComplex k₀ l U) :
    Nonempty ((upperShriek i).obj ((derivedLowerShriek k₀ l j).obj G) ≅
      ((upperStar i).obj ((derivedLowerStar j).obj G))⟦(-1 : ℤ)⟧) := by
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    exists_distTriang_openClosed j i hij ((derivedLowerStar j).obj G)
  have hT' := (upperShriek i).map_distinguished T hT
  have h₂ : IsZero ((upperShriek i).obj T.obj₂) :=
    (isZero_upperShriek_obj_derivedLowerStar_obj j i hij G).of_iso ((upperShriek i).mapIso e₂)
  have := (Triangle.isZero₂_iff_isIso₃ _ hT').1 h₂
  let E : (upperShriek i).obj T.obj₃ ≅ ((upperShriek i).obj T.obj₁)⟦(1 : ℤ)⟧ :=
    asIso ((upperShriek i).mapTriangle.obj T).mor₃
  let Q := (upperStar i).obj ((derivedLowerStar j).obj G)
  have := isIso_derivedLowerShriekUpperShriekAdjunction_unit_app (k₀ := k₀) (l := l) i Q
  let v : Q ≅ (upperShriek i).obj ((derivedLowerShriek k₀ l i).obj Q) :=
    asIso ((derivedLowerShriekUpperShriekAdjunction i).unit.app Q)
  let e₃' : T.obj₃ ≅ (derivedLowerShriek k₀ l i).obj Q :=
    e₃ ≪≫ (derivedLowerShriekObjIsoDerivedLowerStar i Q).symm
  let e₁' : T.obj₁ ≅ (derivedLowerShriek k₀ l j).obj G :=
    e₁ ≪≫ (derivedLowerShriek k₀ l j).mapIso (upperStarDerivedLowerStarIso j G)
  let F₁ : ((upperShriek i).obj ((derivedLowerShriek k₀ l j).obj G))⟦(1 : ℤ)⟧ ≅ Q :=
    (shiftFunctor _ (1 : ℤ)).mapIso ((upperShriek i).mapIso e₁'.symm) ≪≫ E.symm ≪≫
      (upperShriek i).mapIso e₃' ≪≫ v.symm
  exact ⟨(shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by norm_num)).symm.app _ ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso F₁⟩

variable [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))] [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- **Step 4: the dual of the boundary complex** (blueprint: `lem-a1-local-boundary-duality`,
step 4): for complementary immersions `j` and `i` and a Weil complex `G` on `U`,
`𝔻_Z (i^* Rj_* G) ≅ (i^* Rj_* 𝔻_U G)[-1]`. -/
theorem nonempty_verdierDual_upperStar_derivedLowerStar_iso
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) (G : WeilComplex k₀ l U) :
    Nonempty ((verdierDual k₀ l Z).obj (op ((upperStar i).obj ((derivedLowerStar j).obj G))) ≅
      ((upperStar i).obj ((derivedLowerStar j).obj ((verdierDual k₀ l U).obj (op G))))⟦(-1 : ℤ)⟧)
    := by
  obtain ⟨e₂⟩ := nonempty_upperShriek_verdierDual_iso i ((derivedLowerStar j).obj G)
  obtain ⟨e₁⟩ := nonempty_verdierDual_derivedLowerStar_iso j G
  obtain ⟨e₃⟩ := nonempty_upperShriek_derivedLowerShriek_iso j i hij
    ((verdierDual k₀ l U).obj (op G))
  exact ⟨e₂.symm ≪≫ (upperShriek i).mapIso e₁ ≪≫ e₃⟩

end Localization

end WeilComplex

end AlgebraicGeometry
