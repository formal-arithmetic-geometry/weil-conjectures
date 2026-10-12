/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius

/-!
# Additivity of the trace formula along open-closed decompositions

For a Weil complex `(K, φ)` on `X` over `s = Spec Ω`, a closed immersion `i : Z ⟶ X` and the
complementary open immersion `j : U ⟶ X`, both stable under the Frobenius, the trace formula
for `X` follows from the trace formulas for the restricted Weil complexes on `U` and `Z`: the
traces of the global operators add up by `trace_globalOperator_eq_trace_add_trace`, and the
fixed points of `X` are the disjoint union of those of `U` and `Z`, with the same stalk traces.
This is the localization step (Step 5) of the proof of blueprint
`thm-trf-coefficient-morphism-trace-formula`.

## Main definitions

- `AlgebraicGeometry.ProEtale.WeilComplex.TraceFormula`: the statement of the trace formula
  for a Weil complex in degree `m`.

## Main results

- `AlgebraicGeometry.ProEtale.trace_globalOperator_eq_trace_add_trace`: additivity of the
  trace of the global operator along an open-closed decomposition.
- `AlgebraicGeometry.ProEtale.WeilComplex.trace_stalkFrobenius_upperStarPull`: the stalk
  Frobenius of a restricted Weil complex is the stalk Frobenius of the original one.
- `AlgebraicGeometry.ProEtale.WeilComplex.traceFormula_of_isCompl`: the trace formula on `X`
  follows from the trace formulas on `U` and `Z`.

## Implementation notes

In `trace_globalOperator_eq_trace_add_trace` the restrictions of the Frobenius to the open
and closed pieces are data `Φ_U`, `Φ_Z`, and the restricted Weil complexes are
`WeilComplex.upperStarPull`, whose coefficient morphisms are the canonical
`WeilComplex.upperStarPullCoeff`.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA] {s X : Scheme.{u}}

/-- Compact trace additivity: for a closed immersion `i : Z ⟶ X` and its open complement
`j : U ⟶ X`, the Frobenius coefficient morphisms induced on the functorial compact
localization triangle satisfy

`tr_A(F_{c,m}, RΓ_c(X, K)) = tr_A(F_{c,m}, RΓ_c(U, j^* K)) + tr_A(F_{c,m}, RΓ_c(Z, i^* K))`.

Invertibility of the coefficient morphism is unnecessary, so the statement is for plain
`WeilComplex`es (blueprint: `prop-trf-trace-additivity-open-closed`, subsection
`sk-i-global-additivity`). -/
theorem trace_globalOperator_eq_trace_add_trace (G : GeometricOperations A s)
    {U Z : Scheme.{u}} {aX : X ⟶ s} {aU : U ⟶ s} {aZ : Z ⟶ s}
    [IsGeometric aX] [IsGeometric aU] [IsGeometric aZ]
    [HasCompactification aX] [HasCompactification aU] [HasCompactification aZ]
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    (hj : j ≫ aX = aU) (hi : i ≫ aX = aZ)
    (hcompl : IsCompl (Set.range j.base) (Set.range i.base))
    (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj) (frobU : U ⟶ U) (frobZ : Z ⟶ Z)
    (sqU : CommSq frobU j j (W.frobeniusIterate 1))
    (sqZ : CommSq frobZ i i (W.frobeniusIterate 1))
    (m : ℕ)
    [IsProper (W.graph G hW m).snd]
    [IsProper ((W.upperStarPull j hj frobU sqU).graph G
      (G.ctf_upperStar j (.mk hj) hW) m).snd]
    [IsProper ((W.upperStarPull i hi frobZ sqZ).graph G
      (G.ctf_upperStar i (.mk hi) hW) m).snd]
    [HasRightDual ((rightDerivedLowerShriek A aX).obj W.obj)]
    [HasRightDual ((rightDerivedLowerShriek A aU).obj (W.upperStarPull j hj frobU sqU).obj)]
    [HasRightDual ((rightDerivedLowerShriek A aZ).obj (W.upperStarPull i hi frobZ sqZ).obj)] :
    MonoidalCategory.trace (Correspondence.globalOperator G (W.graph G hW m) hW) =
      MonoidalCategory.trace
          (Correspondence.globalOperator G
            ((W.upperStarPull j hj frobU sqU).graph G (G.ctf_upperStar j (.mk hj) hW) m)
            (G.ctf_upperStar j (.mk hj) hW)) +
        MonoidalCategory.trace
          (Correspondence.globalOperator G
            ((W.upperStarPull i hi frobZ sqZ).graph G (G.ctf_upperStar i (.mk hi) hW) m)
            (G.ctf_upperStar i (.mk hi) hW)) :=
  sorry

section Coherence

variable {T Y : Scheme.{u}}

omit [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A] in
/-- The component of the inverse of `leftDerivedUpperStarSquareIso`:
`Lg'^* Lf^* K ≃ L(g' ≫ f)^* K = L(f' ≫ g)^* K ≃ Lf'^* Lg^* K`. -/
lemma leftDerivedUpperStarSquareIso_inv_app {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (leftDerivedUpperStarSquareIso A sq).inv.app K =
      (leftDerivedUpperStarComp A g' f).inv.app K ≫
        (leftDerivedUpperStarCongr A sq.w).hom.app K ≫
        (leftDerivedUpperStarComp A f' g).hom.app K := by
  simp only [leftDerivedUpperStarSquareIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Category.assoc]
  rw [leftDerivedUpperStarCongr_inv_app]

omit [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A] in
/-- The unit step for the pulled back coefficient morphisms: along the square
`𝟙 ≫ f = f ≫ 𝟙`, the pullback of `L(𝟙 X)^* K ≃ K` is `L(𝟙 Y)^* Lf^* K ≃ Lf^* K`. -/
lemma leftDerivedUpperStarId_hom_app_eq_squareIso {f : Y ⟶ X} (sq : CommSq (𝟙 Y) f f (𝟙 X))
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (leftDerivedUpperStarId A Y).hom.app (((upperStar A f).leftDerivedFunctor).obj K) =
      (leftDerivedUpperStarSquareIso A sq).inv.app K ≫
        ((upperStar A f).leftDerivedFunctor).map ((leftDerivedUpperStarId A X).hom.app K) := by
  rw [leftDerivedUpperStarSquareIso_inv_app, Category.assoc, Category.assoc,
    leftDerivedUpperStarComp_id_right_app, leftDerivedUpperStarCongr_hom_app_trans,
    ← cancel_epi ((leftDerivedUpperStarComp A (𝟙 Y) f).hom.app K), Iso.hom_inv_id_app_assoc,
    leftDerivedUpperStarComp_id_left_app]

omit [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A] in
/-- The successor step for the pulled back coefficient morphisms: for endomorphisms with
`G = g ≫ G_m`, `Φ_1 = Φ`, `Φ_S = Φ ≫ Φ_m` intertwined by `f`, and coefficient maps
`φ_1 = φ` and `φ_S = φ ∘ LΦ^* φ_m`, pulling back `φ_m` and `φ_1` along `f` and composing them
gives the pullback of `φ_S`. -/
lemma upperStarPullCoeff_succ_aux {f : Y ⟶ X} {g G Gm : Y ⟶ Y} {Φ Φ₁ Φm ΦS : X ⟶ X}
    (eG : G = g ≫ Gm) (e₁ : Φ₁ = Φ) (eS : ΦS = Φ ≫ Φm) (sqm : CommSq Gm f f Φm)
    (sq₁ : CommSq g f f Φ₁) (sqS : CommSq G f f ΦS)
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (φm : ((upperStar A Φm).leftDerivedFunctor).obj K ⟶ K)
    (φ₁ : ((upperStar A Φ₁).leftDerivedFunctor).obj K ⟶ K)
    (φS : ((upperStar A ΦS).leftDerivedFunctor).obj K ⟶ K)
    (φ : ((upperStar A Φ).leftDerivedFunctor).obj K ⟶ K)
    (h₁ : φ₁ = (leftDerivedUpperStarCongr A e₁).hom.app K ≫ φ)
    (hS : φS = (leftDerivedUpperStarCongr A eS).hom.app K ≫
      (leftDerivedUpperStarComp A Φ Φm).hom.app K ≫
      ((upperStar A Φ).leftDerivedFunctor).map φm ≫ φ) :
    (leftDerivedUpperStarCongr A eG).hom.app (((upperStar A f).leftDerivedFunctor).obj K) ≫
        (leftDerivedUpperStarComp A g Gm).hom.app (((upperStar A f).leftDerivedFunctor).obj K) ≫
        ((upperStar A g).leftDerivedFunctor).map
          ((leftDerivedUpperStarSquareIso A sqm).inv.app K ≫
            ((upperStar A f).leftDerivedFunctor).map φm) ≫
        (leftDerivedUpperStarSquareIso A sq₁).inv.app K ≫
          ((upperStar A f).leftDerivedFunctor).map φ₁ =
      (leftDerivedUpperStarSquareIso A sqS).inv.app K ≫
        ((upperStar A f).leftDerivedFunctor).map φS := by
  subst eG e₁ eS h₁ hS
  simp only [leftDerivedUpperStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    leftDerivedUpperStarSquareIso_inv_app, Functor.map_comp, Category.assoc]
  rw [← cancel_epi ((leftDerivedUpperStarComp A (g ≫ Gm) f).hom.app K),
    Iso.hom_inv_id_app_assoc, leftDerivedUpperStarComp_assoc_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    leftDerivedUpperStarComp_hom_app_congr_right_assoc,
    leftDerivedUpperStarCongr_hom_app_trans_assoc,
    ← leftDerivedUpperStarCongr_hom_app_trans_assoc
      ((Category.assoc g Gm f).trans ((congrArg (g ≫ ·) sqm.w).trans (Category.assoc g f Φm).symm))
      (Category.assoc g f Φm), ← leftDerivedUpperStarComp_assoc_app_assoc,
    ← leftDerivedUpperStarComp_hom_naturality_assoc, Iso.hom_inv_id_app_assoc,
    leftDerivedUpperStarCongr_hom_naturality_assoc,
    leftDerivedUpperStarComp_hom_app_congr_left_assoc,
    leftDerivedUpperStarComp_hom_naturality_assoc, leftDerivedUpperStarComp_assoc_app_assoc,
    leftDerivedUpperStarCongr_hom_app_trans_assoc, leftDerivedUpperStarCongr_hom_app_trans_assoc]

omit [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A] in
/-- The stalk of a pulled back coefficient morphism: for `y : T ⟶ Y` fixed by `G_m` and
`f : Y ⟶ X` intertwining `G_m` and `Φ_m`, the endomorphism of `Ly^* Lf^* K` induced by the
pullback of `φ_m` is conjugate, along `L(y ≫ f)^* K ≃ Ly^* Lf^* K`, to the endomorphism of
`L(y ≫ f)^* K` induced by `φ_m`. -/
lemma leftDerivedUpperStarComp_stalk_squareIso_aux {y : T ⟶ Y} {f : Y ⟶ X} {Gm : Y ⟶ Y}
    {Φm : X ⟶ X} (sq : CommSq Gm f f Φm) (hy : y ≫ Gm = y) (hyf : (y ≫ f) ≫ Φm = y ≫ f)
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (φm : ((upperStar A Φm).leftDerivedFunctor).obj K ⟶ K) :
    ((leftDerivedUpperStarCongr A hyf).inv.app K ≫
        (leftDerivedUpperStarComp A (y ≫ f) Φm).hom.app K ≫
        ((upperStar A (y ≫ f)).leftDerivedFunctor).map φm) ≫
        (leftDerivedUpperStarComp A y f).hom.app K =
      (leftDerivedUpperStarComp A y f).hom.app K ≫
        ((leftDerivedUpperStarCongr A hy).inv.app (((upperStar A f).leftDerivedFunctor).obj K) ≫
          (leftDerivedUpperStarComp A y Gm).hom.app
            (((upperStar A f).leftDerivedFunctor).obj K) ≫
          ((upperStar A y).leftDerivedFunctor).map
            ((leftDerivedUpperStarSquareIso A sq).inv.app K ≫
              ((upperStar A f).leftDerivedFunctor).map φm)) := by
  simp only [leftDerivedUpperStarCongr_inv_app, leftDerivedUpperStarSquareIso_inv_app,
    Functor.map_comp, Category.assoc]
  rw [leftDerivedUpperStarComp_hom_app_congr_left_assoc,
    leftDerivedUpperStarComp_assoc_app_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    leftDerivedUpperStarComp_hom_app_congr_right_assoc,
    leftDerivedUpperStarCongr_hom_app_trans_assoc, leftDerivedUpperStarCongr_hom_app_trans_assoc]
  conv_rhs => rw [← leftDerivedUpperStarCongr_hom_app_trans_assoc hyf.symm (Category.assoc y f Φm)]
  rw [← leftDerivedUpperStarComp_assoc_app_assoc, ← leftDerivedUpperStarComp_hom_naturality]

end Coherence

namespace WeilComplex

section Restriction

variable {Y : Scheme.{u}} {aX : X ⟶ s} (W : WeilComplex (A := A) aX) (f : Y ⟶ X) {aY : Y ⟶ s}
  (hf : f ≫ aX = aY) (g : Y ⟶ Y) (sq : CommSq g f f (W.frobeniusIterate 1))

/-- The iterates of the Frobenius of a restricted Weil complex are the restrictions of the
iterates: `Φ_{Y,m} ≫ f = f ≫ Φ_{X,m}`. -/
lemma commSq_frobeniusIterate_upperStarPull (m : ℕ) :
    CommSq ((W.upperStarPull f hf g sq).frobeniusIterate m) f f (W.frobeniusIterate m) := by
  induction m with
  | zero => exact ⟨by simp⟩
  | succ n ih =>
    refine ⟨?_⟩
    rw [frobeniusIterate_succ, frobeniusIterate_succ, Category.assoc, ih.w, ← Category.assoc,
      ← Category.assoc, ← W.frobeniusIterate_one, ← sq.w]
    rfl

/-- The iterates of the coefficient morphism of a restricted Weil complex are the restrictions
of the iterates: `(f^* φ)_m = f^* φ_m`, read through the square `Φ_{Y,m} ≫ f = f ≫ Φ_{X,m}`. -/
lemma coeffIterate_upperStarPull (m : ℕ) :
    (W.upperStarPull f hf g sq).coeffIterate m =
      W.upperStarPullCoeff m (W.commSq_frobeniusIterate_upperStarPull f hf g sq m) := by
  induction m with
  | zero => exact leftDerivedUpperStarId_hom_app_eq_squareIso _ W.obj
  | succ n ih =>
    rw [coeffIterate_succ, ih]
    exact upperStarPullCoeff_succ_aux ((W.upperStarPull f hf g sq).frobeniusIterate_succ n)
      W.frobeniusIterate_one (W.frobeniusIterate_succ n) _ sq _ _ _ _ _ W.coeffIterate_one
      (W.coeffIterate_succ n)

/-- If a point `y` of `Y` is fixed by `Φ_{Y,m}`, then `f ∘ y` is fixed by `Φ_{X,m}`. -/
lemma comp_frobeniusIterate_of_upperStarPull (m : ℕ) {T : Scheme.{u}} (y : T ⟶ Y)
    (hy : y ≫ (W.upperStarPull f hf g sq).frobeniusIterate m = y) :
    (y ≫ f) ≫ W.frobeniusIterate m = y ≫ f := by
  rw [Category.assoc, ← (W.commSq_frobeniusIterate_upperStarPull f hf g sq m).w,
    ← Category.assoc, hy]

/-- A point `y` of `Y` is fixed by `Φ_{Y,m}` if and only if `f ∘ y` is fixed by `Φ_{X,m}`,
when `f` is a monomorphism. -/
lemma comp_frobeniusIterate_upperStarPull_iff [Mono f] (m : ℕ) {T : Scheme.{u}} (y : T ⟶ Y) :
    y ≫ (W.upperStarPull f hf g sq).frobeniusIterate m = y ↔
      (y ≫ f) ≫ W.frobeniusIterate m = y ≫ f := by
  refine ⟨W.comp_frobeniusIterate_of_upperStarPull f hf g sq m y, fun h ↦ ?_⟩
  rw [← cancel_mono f, Category.assoc, (W.commSq_frobeniusIterate_upperStarPull f hf g sq m).w,
    ← Category.assoc, h]

/-- The stalk Frobenius of the restricted Weil complex `Lf^* K` at a point `y` is the stalk
Frobenius of `K` at `f ∘ y`: they are conjugate along `Ly^* Lf^* K ≃ L(y ≫ f)^* K`, so they
have the same trace. -/
theorem trace_stalkFrobenius_upperStarPull (m : ℕ) (y : s ⟶ Y)
    (hy : y ≫ (W.upperStarPull f hf g sq).frobeniusIterate m = y)
    [HasRightDual (((upperStar A y).leftDerivedFunctor).obj
      (W.upperStarPull f hf g sq).obj)]
    [HasRightDual (((upperStar A (y ≫ f)).leftDerivedFunctor).obj W.obj)] :
    MonoidalCategory.trace ((W.upperStarPull f hf g sq).stalkFrobenius m y hy) =
      MonoidalCategory.trace (W.stalkFrobenius m (y ≫ f)
        (W.comp_frobeniusIterate_of_upperStarPull f hf g sq m y hy)) := by
  refine (trace_eq_of_iso
    (X' := ((upperStar A y).leftDerivedFunctor).obj (W.upperStarPull f hf g sq).obj)
    ((leftDerivedUpperStarComp A y f).app W.obj) _ _ ?_).symm
  rw [stalkFrobenius, stalkFrobenius, coeffIterate_upperStarPull]
  exact leftDerivedUpperStarComp_stalk_squareIso_aux _ hy _ (W.coeffIterate m)

/-- A section `y` of `a_Y` fixed by `Φ_{Y,m}` gives the section `f ∘ y` of `a_X` fixed by
`Φ_{X,m}`. -/
def compFixedPoint (m : ℕ)
    (y : {y : s ⟶ Y // y ≫ aY = 𝟙 s ∧ y ≫ (W.upperStarPull f hf g sq).frobeniusIterate m = y}) :
    {x : s ⟶ X // x ≫ aX = 𝟙 s ∧ x ≫ W.frobeniusIterate m = x} :=
  ⟨y.1 ≫ f, by rw [Category.assoc, hf, y.2.1],
    W.comp_frobeniusIterate_of_upperStarPull f hf g sq m y.1 y.2.2⟩

/-- Composition with a monomorphism `f` is injective on fixed sections. -/
lemma compFixedPoint_injective [Mono f] (m : ℕ) :
    Function.Injective (W.compFixedPoint f hf g sq m) :=
  fun _ _ h ↦ Subtype.ext ((cancel_mono f).mp (congrArg Subtype.val h))

end Restriction

/-- The trace formula in degree `m` for a Weil complex `W` on `a_X : X ⟶ s`: for every choice
of duals of `RΓ_c(X, K)` and of the geometric stalks, and finiteness of the fixed points of
`Φ_m`,

`tr_A(F_{c,m}(φ) ∣ RΓ_c(X, K)) = ∑_{x ∈ Fix(Φ_m)} tr_A(φ_{m, x} ∣ K_x)`.

This is the identity `TF(X₀, K, φ, m)` of the proof of blueprint
`thm-trf-coefficient-morphism-trace-formula`. -/
def TraceFormula (G : GeometricOperations A s) {aX : X ⟶ s} [IsGeometric aX]
    [HasCompactification aX] (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj) (m : ℕ)
    [IsProper (W.graph G hW m).snd] : Prop :=
  ∀ [HasRightDual ((rightDerivedLowerShriek A aX).obj W.obj)]
    [∀ x : s ⟶ X, HasRightDual (((upperStar A x).leftDerivedFunctor).obj W.obj)]
    [Fintype {x : s ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x}],
    MonoidalCategory.trace (Correspondence.globalOperator G (W.graph G hW m) hW) =
      ∑ x : {x : s ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x},
        MonoidalCategory.trace (W.stalkFrobenius m x.1 x.2.2)

/-- A morphism out of the spectrum of a field whose unique point lands in `S` has its whole
range in `S`. -/
lemma _root_.AlgebraicGeometry.range_subset_of_base_mem {Ω : Type u} [Field Ω] {X : Scheme.{u}}
    (x : Spec (.of Ω) ⟶ X) {S : Set X} (p : Spec (.of Ω)) (h : x.base p ∈ S) :
    Set.range x.base ⊆ S := by
  rintro _ ⟨q, rfl⟩
  rwa [Subsingleton.elim q p]

/-- A morphism from a reduced scheme whose range is contained in the range of a closed
immersion factors through it. -/
lemma _root_.AlgebraicGeometry.IsClosedImmersion.exists_lift_of_range_subset
    {X Y Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (x : Y ⟶ X) [IsReduced Y]
    (h : Set.range x.base ⊆ Set.range i.base) : ∃ y : Y ⟶ Z, y ≫ i = x := by
  have : Surjective (pullback.snd i x) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, Set.preimage_eq_univ_iff]
    exact h⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd i x)
  exact ⟨inv (pullback.snd i x) ≫ pullback.fst i x,
    by rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

/-- For a closed immersion `i : Z ⟶ X` with open complement `j : U ⟶ X`, every fixed section of
`Φ_{X,m}` comes from a unique fixed section of `U` or of `Z`. -/
lemma bijective_sumElim_compFixedPoint {Ω : Type u} [Field Ω] {U Z : Scheme.{u}}
    {aX : X ⟶ Spec (.of Ω)} {aU : U ⟶ Spec (.of Ω)} {aZ : Z ⟶ Spec (.of Ω)}
    (W : WeilComplex (A := A) aX) (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j]
    [IsClosedImmersion i] (hj : j ≫ aX = aU) (hi : i ≫ aX = aZ)
    (hcompl : IsCompl (Set.range j.base) (Set.range i.base)) (frobU : U ⟶ U) (frobZ : Z ⟶ Z)
    (sqU : CommSq frobU j j (W.frobeniusIterate 1))
    (sqZ : CommSq frobZ i i (W.frobeniusIterate 1)) (m : ℕ) :
    Function.Bijective (Sum.elim (W.compFixedPoint j hj frobU sqU m)
      (W.compFixedPoint i hi frobZ sqZ m)) := by
  obtain ⟨p⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  refine ⟨fun a b hab ↦ ?_, fun x ↦ ?_⟩
  · rcases a with a | a <;> rcases b with b | b
    · rw [W.compFixedPoint_injective j hj frobU sqU m hab]
    · refine (Set.disjoint_left.mp hcompl.disjoint ⟨a.1.base p, rfl⟩ ?_).elim
      have := congrArg (fun x ↦ x.1.base p) hab
      exact ⟨b.1.base p, this.symm⟩
    · refine (Set.disjoint_left.mp hcompl.disjoint ⟨b.1.base p, rfl⟩ ?_).elim
      have := congrArg (fun x ↦ x.1.base p) hab
      exact ⟨a.1.base p, this⟩
    · rw [W.compFixedPoint_injective i hi frobZ sqZ m hab]
  · have hp : x.1.base p ∈ Set.range j.base ∪ Set.range i.base :=
      Set.eq_univ_iff_forall.mp hcompl.sup_eq_top _
    rcases hp with hp | hp
    · have hx := range_subset_of_base_mem x.1 p hp
      refine ⟨.inl ⟨IsOpenImmersion.lift j x.1 hx, ?_, ?_⟩, Subtype.ext ?_⟩
      · rw [← hj, ← Category.assoc, IsOpenImmersion.lift_fac, x.2.1]
      · rw [W.comp_frobeniusIterate_upperStarPull_iff j hj frobU sqU m,
          IsOpenImmersion.lift_fac, x.2.2]
      · exact IsOpenImmersion.lift_fac j x.1 hx
    · obtain ⟨y, hy⟩ := IsClosedImmersion.exists_lift_of_range_subset i x.1
        (range_subset_of_base_mem x.1 p hp)
      refine ⟨.inr ⟨y, ?_, ?_⟩, Subtype.ext hy⟩
      · rw [← hi, ← Category.assoc, hy, x.2.1]
      · rw [W.comp_frobeniusIterate_upperStarPull_iff i hi frobZ sqZ m, hy, x.2.2]

/-- Step 5 of the proof of blueprint `thm-trf-coefficient-morphism-trace-formula`, the
localization step: for a closed immersion `i : Z ⟶ X` with open complement `j : U ⟶ X`, both
stable under the Frobenius, the trace formula for `X` follows from the trace formulas for the
restricted Weil complexes `Lj^* K` on `U` and `Li^* K` on `Z`, by additivity of the trace
(`trace_globalOperator_eq_trace_add_trace`) and since the fixed points of `X` are the disjoint
union of those of `U` and `Z`. -/
theorem traceFormula_of_isCompl {Ω : Type u} [Field Ω]
    (G : GeometricOperations A (Spec (.of Ω))) {U Z : Scheme.{u}} {aX : X ⟶ Spec (.of Ω)}
    {aU : U ⟶ Spec (.of Ω)} {aZ : Z ⟶ Spec (.of Ω)}
    [IsGeometric aX] [IsGeometric aU] [IsGeometric aZ]
    [HasCompactification aX] [HasCompactification aU] [HasCompactification aZ]
    (j : U ⟶ X) (i : Z ⟶ X) [IsOpenImmersion j] [IsClosedImmersion i]
    (hj : j ≫ aX = aU) (hi : i ≫ aX = aZ)
    (hcompl : IsCompl (Set.range j.base) (Set.range i.base))
    (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj) (frobU : U ⟶ U) (frobZ : Z ⟶ Z)
    (sqU : CommSq frobU j j (W.frobeniusIterate 1))
    (sqZ : CommSq frobZ i i (W.frobeniusIterate 1))
    (m : ℕ)
    [IsProper (W.graph G hW m).snd]
    [IsProper ((W.upperStarPull j hj frobU sqU).graph G
      (G.ctf_upperStar j (.mk hj) hW) m).snd]
    [IsProper ((W.upperStarPull i hi frobZ sqZ).graph G
      (G.ctf_upperStar i (.mk hi) hW) m).snd]
    [HasRightDual ((rightDerivedLowerShriek A aU).obj (W.upperStarPull j hj frobU sqU).obj)]
    [HasRightDual ((rightDerivedLowerShriek A aZ).obj (W.upperStarPull i hi frobZ sqZ).obj)]
    (hU : (W.upperStarPull j hj frobU sqU).TraceFormula G (G.ctf_upperStar j (.mk hj) hW) m)
    (hZ : (W.upperStarPull i hi frobZ sqZ).TraceFormula G (G.ctf_upperStar i (.mk hi) hW) m) :
    W.TraceFormula G hW m := by
  intro _ _ _
  have hbij := W.bijective_sumElim_compFixedPoint j i hj hi hcompl frobU frobZ sqU sqZ m
  have (y : Spec (.of Ω) ⟶ U) :
      HasRightDual (((upperStar A y).leftDerivedFunctor).obj
        (W.upperStarPull j hj frobU sqU).obj) :=
    { rightDual := HasRightDual.rightDual (((upperStar A (y ≫ j)).leftDerivedFunctor).obj W.obj)
      exact := exactPairingCongrLeft ((leftDerivedUpperStarComp A y j).app W.obj).symm }
  have (z : Spec (.of Ω) ⟶ Z) :
      HasRightDual (((upperStar A z).leftDerivedFunctor).obj
        (W.upperStarPull i hi frobZ sqZ).obj) :=
    { rightDual := HasRightDual.rightDual (((upperStar A (z ≫ i)).leftDerivedFunctor).obj W.obj)
      exact := exactPairingCongrLeft ((leftDerivedUpperStarComp A z i).app W.obj).symm }
  have := Fintype.ofInjective _ (W.compFixedPoint_injective j hj frobU sqU m)
  have := Fintype.ofInjective _ (W.compFixedPoint_injective i hi frobZ sqZ m)
  rw [trace_globalOperator_eq_trace_add_trace G j i hj hi hcompl W hW frobU frobZ sqU sqZ m, hU,
    hZ]
  have key := Fintype.sum_sum_type (Sum.elim
    (fun y : {y : Spec (.of Ω) ⟶ U // y ≫ aU = 𝟙 _ ∧
        y ≫ (W.upperStarPull j hj frobU sqU).frobeniusIterate m = y} ↦ MonoidalCategory.trace
      ((W.upperStarPull j hj frobU sqU).stalkFrobenius m y.1 y.2.2))
    fun z : {z : Spec (.of Ω) ⟶ Z // z ≫ aZ = 𝟙 _ ∧
        z ≫ (W.upperStarPull i hi frobZ sqZ).frobeniusIterate m = z} ↦ MonoidalCategory.trace
      ((W.upperStarPull i hi frobZ sqZ).stalkFrobenius m z.1 z.2.2))
  simp only [Sum.elim_inl, Sum.elim_inr] at key
  rw [← key]
  refine Fintype.sum_bijective _ hbij _ _ fun y ↦ ?_
  rcases y with y | z
  · simp only [Sum.elim_inl]
    exact W.trace_stalkFrobenius_upperStarPull j hj frobU sqU m y.1 y.2.2
  · simp only [Sum.elim_inr]
    exact W.trace_stalkFrobenius_upperStarPull i hi frobZ sqZ m z.1 z.2.2

end WeilComplex

end AlgebraicGeometry.ProEtale
