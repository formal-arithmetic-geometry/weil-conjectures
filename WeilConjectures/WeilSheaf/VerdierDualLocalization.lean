/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.VerdierDual
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.WeilSheaf.Localization

/-!
# Verdier duality and the open–closed decomposition

Let `j : U ↪ X` be a quasi-compact open immersion with closed complement `i : Z ↪ X`. From the
statements of the duality theory of Weil complexes collected in
`WeilConjectures.WeilSheaf.VerdierDual`, this file derives the formal steps 1–4 of the proof of
the local boundary duality (`lem-a1-local-boundary-duality`):

1. `𝔻_X Rf_* G ≅ Rf₀! 𝔻 G` (Verdier exchange and biduality);
2. `Ri^! 𝔻_X K ≅ 𝔻_Z i^* K` (`Ri^! = 𝔻 i^* 𝔻` and biduality);
3. `Ri^! Rj₀! G ≅ (i^* Rj_* G)[-1]` (open–closed triangle, `j^* Rj_* = 𝟭`, and the localization
   theorem: `Ri^! Rj_* = 0` and `Ri^! Ri_* = 𝟭`);
4. `𝔻_Z (i^* Rj_* G) ≅ (i^* Rj_* 𝔻_U G)[-1]`.

Here `Ri^!` is the right adjoint `AlgebraicGeometry.WeilComplex.closedUpperShriek` of `Ri_*`
constructed in `WeilConjectures.WeilSheaf.Localization`, whose adjunction and localization
properties are proved there. The clause `Ri^! ≅ 𝔻_Z i^* 𝔻_X` of the Verdier duality theorem
(`thm-coef-qbar-verdier`) is stated here with `sorry`
(`AlgebraicGeometry.WeilComplex.nonempty_closedUpperShriek_obj_iso`).

## Main statements

- `AlgebraicGeometry.WeilComplex.nonempty_verdierDual_upperStar_derivedLowerStar_iso`: step 4.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

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

/-- The exceptional inverse image `Ri^!` along a closed immersion commutes with the shifts, as
the right adjoint of the direct image `Ri_*`. -/
noncomputable instance (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    (closedUpperShriek (k₀ := k₀) (l := l) i j hij).CommShift ℤ :=
  (closedUpperShriekAdjunction i j hij).rightAdjointCommShift ℤ

/-- The exceptional inverse image `Ri^!` along a closed immersion is a triangulated functor, as
the right adjoint of the triangulated direct image `Ri_*`. -/
instance (hij : IsCompl (Set.range i.base) (Set.range j.base)) :
    (closedUpperShriek (k₀ := k₀) (l := l) i j hij).IsTriangulated :=
  have := (closedUpperShriekAdjunction (k₀ := k₀) (l := l) i j hij).commShift_of_leftAdjoint ℤ
  (closedUpperShriekAdjunction i j hij).isTriangulated_rightAdjoint

omit [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))] in
/-- **Step 3: the exceptional restriction of an extension by zero** (blueprint:
`lem-a1-local-boundary-duality`, step 3): for complementary immersions `j` and `i`,
`Ri^! Rj₀! G ≅ (i^* Rj_* G)[-1]`. Apply the triangulated functor `Ri^!` to the open–closed
triangle `Rj₀! j^* Rj_* G ⟶ Rj_* G ⟶ Ri_* i^* Rj_* G ⟶` of `Rj_* G`: the middle term becomes
`Ri^! Rj_* G = 0` (`AlgebraicGeometry.WeilComplex.isZero_closedUpperShriek_obj`), so the third
arrow becomes an isomorphism, and the closed unit `Q ≅ Ri^! Ri_* Q` identifies the third term
with `i^* Rj_* G`; the first is `Ri^! Rj₀! G` since `j^* Rj_* G ≅ G`. -/
theorem nonempty_closedUpperShriek_derivedLowerShriek_iso
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) (G : WeilComplex k₀ l U) :
    Nonempty ((closedUpperShriek i j hij.symm).obj ((derivedLowerShriek k₀ l j).obj G) ≅
      ((upperStar i).obj ((derivedLowerStar j).obj G))⟦(-1 : ℤ)⟧) := by
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ :=
    exists_distTriang_openClosed j i hij ((derivedLowerStar j).obj G)
  let S := closedUpperShriek (k₀ := k₀) (l := l) i j hij.symm
  have hT' := S.map_distinguished T hT
  have h₂ : IsZero (S.obj T.obj₂) :=
    (isZero_closedUpperShriek_obj i j hij.symm G).of_iso (S.mapIso e₂)
  have := (Triangle.isZero₂_iff_isIso₃ _ hT').1 h₂
  let E : S.obj T.obj₃ ≅ (S.obj T.obj₁)⟦(1 : ℤ)⟧ := asIso (S.mapTriangle.obj T).mor₃
  let Q := (upperStar i).obj ((derivedLowerStar j).obj G)
  let v : Q ≅ S.obj ((derivedLowerStar i).obj Q) :=
    asIso ((closedUpperShriekAdjunction i j hij.symm).unit.app Q)
  let e₁' : T.obj₁ ≅ (derivedLowerShriek k₀ l j).obj G :=
    e₁ ≪≫ (derivedLowerShriek k₀ l j).mapIso
      (asIso ((upperStarDerivedLowerStarAdjunction j).counit.app G))
  let F₁ : (S.obj ((derivedLowerShriek k₀ l j).obj G))⟦(1 : ℤ)⟧ ≅ Q :=
    (shiftFunctor _ (1 : ℤ)).mapIso (S.mapIso e₁'.symm) ≪≫ E.symm ≪≫ S.mapIso e₃ ≪≫ v.symm
  exact ⟨(shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by norm_num)).symm.app _ ≪≫
    (shiftFunctor _ (-1 : ℤ)).mapIso F₁⟩

variable [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- **The exceptional inverse image as a conjugate of the pullback, along a closed immersion**
(blueprint: `thm-coef-qbar-verdier`, "`Rf^! = D_X f^* D_Y`", for a closed immersion `f = i`):
`Ri^! L ≅ 𝔻_Z i^* 𝔻_X L`. Here `Ri^!` is the right adjoint
`AlgebraicGeometry.WeilComplex.closedUpperShriek` of `Ri_*`, which is also the right adjoint of
`Ri₀! ≅ Ri_*`, so this is the clause of `thm-coef-qbar-verdier` for `f = i`. -/
theorem nonempty_closedUpperShriek_obj_iso
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (L : WeilComplex k₀ l X) :
    Nonempty ((closedUpperShriek i j hij).obj L ≅
      (verdierDual k₀ l Z).obj (op ((upperStar i).obj ((verdierDual k₀ l X).obj (op L))))) :=
  sorry

/-- **Step 2: the exceptional inverse image of a dual** (blueprint:
`lem-a1-local-boundary-duality`, step 2): for a closed immersion `i` with open complement `j`,
`Ri^! 𝔻_X K ≅ 𝔻_Z i^* K`, from `Ri^! = 𝔻_Z i^* 𝔻_X` and biduality on `X`. -/
theorem nonempty_closedUpperShriek_verdierDual_iso
    (hij : IsCompl (Set.range i.base) (Set.range j.base)) (K : WeilComplex k₀ l X) :
    Nonempty ((closedUpperShriek i j hij).obj ((verdierDual k₀ l X).obj (op K)) ≅
      (verdierDual k₀ l Z).obj (op ((upperStar i).obj K))) := by
  obtain ⟨e⟩ := nonempty_closedUpperShriek_obj_iso j i hij ((verdierDual k₀ l X).obj (op K))
  obtain ⟨bX⟩ := nonempty_iso_verdierDual_rightOp_comp_verdierDual k₀ l X
  exact ⟨e ≪≫ (verdierDual k₀ l Z).mapIso ((upperStar i).mapIso (bX.app K)).op⟩

variable [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]

/-- **Step 4: the dual of the boundary complex** (blueprint: `lem-a1-local-boundary-duality`,
step 4): for complementary immersions `j` and `i` and a Weil complex `G` on `U`,
`𝔻_Z (i^* Rj_* G) ≅ (i^* Rj_* 𝔻_U G)[-1]`. -/
theorem nonempty_verdierDual_upperStar_derivedLowerStar_iso
    (hij : IsCompl (Set.range j.base) (Set.range i.base)) (G : WeilComplex k₀ l U) :
    Nonempty ((verdierDual k₀ l Z).obj (op ((upperStar i).obj ((derivedLowerStar j).obj G))) ≅
      ((upperStar i).obj ((derivedLowerStar j).obj ((verdierDual k₀ l U).obj (op G))))⟦(-1 : ℤ)⟧)
    := by
  obtain ⟨e₂⟩ := nonempty_closedUpperShriek_verdierDual_iso j i hij.symm
    ((derivedLowerStar j).obj G)
  obtain ⟨e₁⟩ := nonempty_verdierDual_derivedLowerStar_iso j G
  obtain ⟨e₃⟩ := nonempty_closedUpperShriek_derivedLowerShriek_iso j i hij
    ((verdierDual k₀ l U).obj (op G))
  exact ⟨e₂.symm ≪≫ (closedUpperShriek i j hij.symm).mapIso e₁ ≪≫ e₃⟩

end Localization

section SmoothLisse

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The tensor product of a lisse Weil sheaf `L` with a Weil sheaf `G` placed in degree zero is
the tensor product sheaf `L ⊗ G` placed in degree zero: the internal hom out of the lisse
`L^∨` is exact. -/
noncomputable def tensorLisseToComplexIso (L : WeilSheaf k₀ l X) (hL : L.IsLisse)
    (G : WeilSheaf k₀ l X) :
    (tensorLisse L hL).obj (WeilSheaf.toComplex.obj G) ≅
      WeilSheaf.toComplex.obj (L.tensorObj G hL) :=
  have := ProEtaleWeilSheaf.preservesFiniteColimits_ihomFunctor (L.dual hL).obj hL.dual
  ObjectProperty.isoMk _
    ((ProEtaleWeilSheaf.ihomFunctor k₀ l X (L.dual hL).obj).singleFunctorCompRightDerivedFunctorIso
      |>.app G.obj)

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

/-- **The Verdier dual of a lisse sheaf on a smooth scheme** (blueprint:
`lem-a1-local-boundary-duality`, "`𝔻_U F ≅ F^∨(1)[2]`"): if `X` is smooth of pure dimension `d`
over `k₀` and `P` is a lisse Weil sheaf on `X`, then `𝔻_X P ≅ (P^∨ ⊗ (ℚ̄_ℓ(d) ⊗ ℚ̄_ℓ))[2d]`,
from `ω_X ≅ ℚ̄_ℓ(d)[2d]` and `RHom(P, N) ≅ P^∨ ⊗ N`. -/
theorem nonempty_verdierDual_toComplex_iso_of_isLisse (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))]
    (P : WeilSheaf k₀ l X) (hP : P.IsLisse) :
    Nonempty ((verdierDual k₀ l X).obj (op (WeilSheaf.toComplex.obj P)) ≅
      (WeilSheaf.toComplex.obj ((P.dual hP).tensorObj
        ((WeilSheaf.tateTwistSheaf k₀ l X d).tensorObj (WeilSheaf.adicConstant k₀ l X)
          (WeilSheaf.isLisse_tateTwistSheaf k₀ l X d)) hP.dual))⟦(2 * d : ℤ)⟧) := by
  obtain ⟨e₁⟩ := nonempty_tensorLisse_dual_iso_derivedHom P hP (dualizingComplex k₀ l X)
  obtain ⟨e₂⟩ := nonempty_dualizingComplex_iso (k₀ := k₀) (l := l) (X := X) d
  let T := tensorLisse (P.dual hP) hP.dual
  let E₁ : (verdierDual k₀ l X).obj (op (WeilSheaf.toComplex.obj P)) ≅
      T.obj (dualizingComplex k₀ l X) :=
    ObjectProperty.isoMk _ e₁.symm
  exact ⟨E₁ ≪≫ T.mapIso e₂ ≪≫ (T.commShiftIso (2 * d : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 * d : ℤ)).mapIso
      (T.mapIso (tensorLisseToComplexIso (WeilSheaf.tateTwistSheaf k₀ l X d)
        (WeilSheaf.isLisse_tateTwistSheaf k₀ l X d) _) ≪≫ tensorLisseToComplexIso _ _ _)⟩

end SmoothLisse

end WeilComplex

end AlgebraicGeometry
