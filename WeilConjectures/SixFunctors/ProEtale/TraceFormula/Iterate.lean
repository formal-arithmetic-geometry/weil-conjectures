/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Additivity
public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.GlobalOperator

/-!
# Iterates of Weil complexes and the trace formula over a point

The `m`-th iterate of a Weil complex `(K, φ)` is the Weil complex `(K, φ_m)` with Frobenius
`Φ_m`; the trace formula in degree `m` for `(K, φ)` is the trace formula in degree one for its
`m`-th iterate. Over the base itself, `a_X = 𝟙 s`, the trace formula is a formal consequence of
the normalisations of the six-functor package at identities.

## Main definitions

- `AlgebraicGeometry.ProEtale.WeilComplex.iterate`: the `m`-th iterate `(K, φ_m)`.

## Main results

- `AlgebraicGeometry.ProEtale.WeilComplex.traceFormula_of_iterate`: the trace formula in degree
  `m` from the trace formula in degree one for the `m`-th iterate.
- `AlgebraicGeometry.ProEtale.WeilComplex.traceFormula_of_eq_id`: the trace formula over the
  base, `a_X = 𝟙 s`.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry.ProEtale.WeilComplex

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s X : Scheme.{u}} {aX : X ⟶ s}

/-- The `m`-th iterate of a Weil complex `(K, φ)`: the Weil complex `(K, φ_m)` with Frobenius
`Φ_m` (part of blueprint `def-trf-frobenius-coefficient-morphism`). -/
noncomputable def iterate (W : WeilComplex (A := A) aX) (m : ℕ) : WeilComplex (A := A) aX where
  frobenius := W.frobeniusIterate m
  frobenius_comp := W.frobeniusIterate_comp m
  obj := W.obj
  coeff := W.coeffIterate m

/-- The stalk composite `Lx^* K ≃ L(x ≫ g)^* K ≃ Lx^* Lg^* K ⟶ Lx^* K` of a coefficient map is
invariant under transporting the coefficient map along an equality `g = g'`. -/
lemma leftDerivedUpperStarComp_stalk_congr {g g' : X ⟶ X} (e : g = g') (x : s ⟶ X)
    (hx : x ≫ g = x) (hx' : x ≫ g' = x) (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (v' : ((upperStar A g').leftDerivedFunctor).obj K ⟶ K) :
    (leftDerivedUpperStarCongr A hx).inv.app K ≫ (leftDerivedUpperStarComp A x g).hom.app K ≫
        ((upperStar A x).leftDerivedFunctor).map
          ((leftDerivedUpperStarCongr A e).hom.app K ≫ v') =
      (leftDerivedUpperStarCongr A hx').inv.app K ≫ (leftDerivedUpperStarComp A x g').hom.app K ≫
        ((upperStar A x).leftDerivedFunctor).map v' := by
  subst e
  rw [leftDerivedUpperStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

/-- The Frobenius of the `m`-th iterate in degree one is the `m`-th iterate of the Frobenius. -/
lemma iterate_frobeniusIterate_one (W : WeilComplex (A := A) aX) (m : ℕ) :
    (W.iterate m).frobeniusIterate 1 = W.frobeniusIterate m :=
  (W.iterate m).frobeniusIterate_one

/-- The stalk Frobenius in degree one of the `m`-th iterate is the stalk Frobenius in degree
`m`. -/
lemma stalkFrobenius_iterate_one (W : WeilComplex (A := A) aX) (m : ℕ) (x : s ⟶ X)
    (hx : x ≫ (W.iterate m).frobeniusIterate 1 = x) :
    (W.iterate m).stalkFrobenius 1 x hx =
      W.stalkFrobenius m x (by rwa [iterate_frobeniusIterate_one] at hx) := by
  rw [stalkFrobenius, stalkFrobenius, coeffIterate_one]
  exact leftDerivedUpperStarComp_stalk_congr (W.iterate m).frobeniusIterate_one x hx _ W.obj
    (W.coeffIterate m)

variable [Etale.HasBoundedBelowUpperShrieks A] [DerivedBraiding A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

/-- The global operators of the graph correspondences of two equal proper endomorphisms
`g = g'` agree when the coefficient maps correspond under the transport
`L(g)^* K ≃ L(g')^* K`. -/
lemma _root_.AlgebraicGeometry.ProEtale.Correspondence.globalOperator_ofGraph_congr
    (G : GeometricOperations A s) [IsGeometric aX] [HasCompactification aX]
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} (hK : G.ctf X K) {g g' : X ⟶ X}
    (e : g = g') (hg : g ≫ aX = aX) (hg' : g' ≫ aX = aX)
    (v : ((upperStar A g).leftDerivedFunctor).obj K ⟶ K)
    (v' : ((upperStar A g').leftDerivedFunctor).obj K ⟶ K)
    [hp : IsProper (Correspondence.ofGraph G aX K hK g hg v).snd]
    [hp' : IsProper (Correspondence.ofGraph G aX K hK g' hg' v').snd]
    (hv : v = (leftDerivedUpperStarCongr A e).hom.app K ≫ v') :
    Correspondence.globalOperator G (Correspondence.ofGraph G aX K hK g hg v) hK =
      Correspondence.globalOperator G (Correspondence.ofGraph G aX K hK g' hg' v') hK := by
  subst e hv
  rw [leftDerivedUpperStarCongr_rfl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

/-- The trace formula in degree `m` for `(K, φ)` follows from the trace formula in degree one
for its `m`-th iterate `(K, φ_m)`: both are statements about the graph of `Φ_m` with coefficient
`φ_m`. -/
theorem traceFormula_of_iterate (G : GeometricOperations A s) [IsGeometric aX]
    [HasCompactification aX] (W : WeilComplex (A := A) aX) (hW : G.ctf X W.obj) (m : ℕ)
    [IsProper (W.graph G hW m).snd] [IsProper ((W.iterate m).graph G hW 1).snd]
    (h : (W.iterate m).TraceFormula G hW 1) : W.TraceFormula G hW m := by
  intro hX hx _
  let e : {x : s ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ (W.iterate m).frobeniusIterate 1 = x} ≃
      {x : s ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ W.frobeniusIterate m = x} :=
    Equiv.subtypeEquivRight fun x ↦ by rw [iterate_frobeniusIterate_one]
  let := Fintype.ofEquiv _ e.symm
  let hx' (x : {x : s ⟶ X // x ≫ aX = 𝟙 _ ∧ x ≫ (W.iterate m).frobeniusIterate 1 = x}) :
      HasRightDual (((upperStar A x.1).leftDerivedFunctor).obj W.obj) :=
    hx (e x)
  have hop : Correspondence.globalOperator G ((W.iterate m).graph G hW 1) hW =
      Correspondence.globalOperator G (W.graph G hW m) hW :=
    Correspondence.globalOperator_ofGraph_congr G hW (W.iterate_frobeniusIterate_one m) _ _ _ _
      (hp := ‹IsProper ((W.iterate m).graph G hW 1).snd›) (W.iterate m).coeffIterate_one
  unfold TraceFormula at h
  rw [← hop, @h hX hx' _]
  refine Fintype.sum_equiv e _ _ fun x ↦ ?_
  rw [stalkFrobenius_iterate_one]
  rfl

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.HasBoundedBelowUpperShrieks A]
  [DerivedBraiding A] in
/-- The transport of the derived exceptional direct image along `f = g` followed by its
transport along `g = h` is its transport along `f = h`. -/
lemma _root_.AlgebraicGeometry.ProEtale.rightDerivedLowerShriekCongr_hom_app_trans
    {Y Z : Scheme.{u}} {f g h : Y ⟶ Z} [HasCompactification f] [HasCompactification g]
    [HasCompactification h] (e₁ : f = g) (e₂ : g = h)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    (rightDerivedLowerShriekCongr A e₁).hom.app K ≫ (rightDerivedLowerShriekCongr A e₂).hom.app K =
      (rightDerivedLowerShriekCongr A (e₁.trans e₂)).hom.app K := by
  subst e₁ e₂
  simp

/-- The proper pullback along the identity is `Ra_{X!}` applied to the identification
`K ≃ L(𝟙 X)^* K`. -/
lemma _root_.AlgebraicGeometry.ProEtale.GeometricOperations.properPullback_id
    (G : GeometricOperations A s) [IsGeometric aX] [HasCompactification aX]
    (hh : 𝟙 X ≫ aX = aX) {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : G.ctf X K) :
    G.properPullback (𝟙 X) hh hK =
      (rightDerivedLowerShriek A aX).map ((leftDerivedUpperStarId A X).inv.app K) := by
  rw [GeometricOperations.properPullback, G.properComparison_id_inv_app_hom,
    G.lowerShriekComp_id_left]
  simp only [Iso.trans_hom, NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    ctfLowerShriekCongr_hom_app_hom, Functor.map_comp, Category.assoc]
  simp only [ObjectProperty.lift_map, ObjectProperty.homMk_hom, Functor.comp_map,
    ObjectProperty.ι_map, ObjectProperty.ι_obj, ObjectProperty.FullSubcategory.id_hom]
  have : HasCompactification (𝟙 X ≫ aX) := .of_eq hh.symm
  rw [rightDerivedLowerShriekCongr_hom_app_trans, rightDerivedLowerShriekCongr_rfl,
    Iso.refl_hom, NatTrans.id_app]
  erw [Category.comp_id, Category.comp_id]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← ObjectProperty.FullSubcategory.comp_hom, Iso.inv_hom_id_app,
    ObjectProperty.FullSubcategory.id_hom]
  erw [Category.comp_id]
  rw [conjugateIsoEquiv_apply_inv, unit_conjugateEquiv]
  simp

/-- The identification `R(𝟙 X)_! ≃ 𝟭` of the package is natural, as a family of morphisms of
`D(X, A)` indexed by `Dᵇctf(X)`. -/
@[reassoc]
lemma _root_.AlgebraicGeometry.ProEtale.GeometricOperations.lowerShriekId_hom_app_naturality
    (G : GeometricOperations A s) (hX : IsGeometricHom s (𝟙 X)) {M M' : Ctf A X}
    (φ : M.obj ⟶ M'.obj) :
    (rightDerivedLowerShriek A (𝟙 X)).map φ ≫ ((G.lowerShriekId X hX).hom.app M').hom =
      ((G.lowerShriekId X hX).hom.app M).hom ≫ φ :=
  congrArg (·.hom) ((G.lowerShriekId X hX).hom.naturality (ObjectProperty.homMk φ))

/-- Over the base, the trace of the global operator of the graph correspondence of an
endomorphism `g = 𝟙 s` with coefficient map `v` is the trace of the stalk composite
`L(𝟙 s)^* K ≃ L(𝟙 s ≫ g)^* K ≃ L(𝟙 s)^* Lg^* K ⟶ L(𝟙 s)^* K` of `v`. -/
lemma trace_globalOperator_ofGraph_of_eq_id (G : GeometricOperations A s)
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology s) A)} (hK : G.ctf s K) {g : s ⟶ s}
    (e : g = 𝟙 s) (hg : g ≫ 𝟙 s = 𝟙 s) (hx : 𝟙 s ≫ g = 𝟙 s)
    (v : ((upperStar A g).leftDerivedFunctor).obj K ⟶ K)
    [IsProper (Correspondence.ofGraph G (𝟙 s) K hK g hg v).snd]
    [HasRightDual ((rightDerivedLowerShriek A (𝟙 s)).obj K)]
    [hK' : HasRightDual (((upperStar A (𝟙 s)).leftDerivedFunctor).obj K)] :
    trace (Correspondence.globalOperator G (Correspondence.ofGraph G (𝟙 s) K hK g hg v) hK) =
      trace ((leftDerivedUpperStarCongr A hx).inv.app K ≫
        (leftDerivedUpperStarComp A (𝟙 s) g).hom.app K ≫
        ((upperStar A (𝟙 s)).leftDerivedFunctor).map v) := by
  subst e
  have hc : (leftDerivedUpperStarCongr A hx).inv.app K ≫
      (leftDerivedUpperStarComp A (𝟙 s) (𝟙 s)).hom.app K =
        (leftDerivedUpperStarId A s).inv.app (((upperStar A (𝟙 s)).leftDerivedFunctor).obj K) := by
    rw [← cancel_mono ((leftDerivedUpperStarId A s).hom.app _), Category.assoc,
      leftDerivedUpperStarComp_id_left_app, Iso.inv_hom_id_app, Iso.inv_hom_id_app]
    rfl
  rw [Correspondence.globalOperator_ofGraph, G.properPullback_id, ← Functor.map_comp]
  refine trace_eq_of_iso (X := (rightDerivedLowerShriek A (𝟙 s)).obj K)
    (X' := ((upperStar A (𝟙 s)).leftDerivedFunctor).obj K)
    ((DerivedCategory.constructibleFiniteTor A s).ι.mapIso
    ((G.lowerShriekId s (.id (𝟙 s))).app ⟨K, hK⟩) ≪≫ ((leftDerivedUpperStarId A s).app K).symm)
    _ _ ?_
  rw [Iso.trans_hom, Functor.mapIso_hom, ObjectProperty.ι_map, Iso.app_hom, Iso.symm_hom,
    Iso.app_inv, G.lowerShriekId_hom_app_naturality_assoc (M := ⟨K, hK⟩) (M' := ⟨K, hK⟩),
    Category.assoc, Category.assoc,
    reassoc_of% hc, ← (leftDerivedUpperStarId A s).inv.naturality v, Functor.id_map]

/-- The trace formula over the base: for a Weil complex on `a_X = 𝟙 s` the Frobenius is the
identity, the only fixed section is `𝟙 s`, and the global operator `F_{c,m}(φ)` on
`RΓ_c(s, K) ≃ K` is the stalk Frobenius `φ_m` at `𝟙 s`. -/
theorem traceFormula_of_eq_id (G : GeometricOperations A s) (W : WeilComplex (A := A) (𝟙 s))
    (hW : G.ctf s W.obj) (m : ℕ) [IsProper (W.graph G hW m).snd] : W.TraceFormula G hW m := by
  intro _ hx _
  have hΦ : W.frobeniusIterate m = 𝟙 s :=
    (Category.comp_id _).symm.trans (W.frobeniusIterate_comp m)
  have hx₀ : 𝟙 s ≫ 𝟙 s = 𝟙 s ∧ 𝟙 s ≫ W.frobeniusIterate m = 𝟙 s :=
    ⟨Category.id_comp _, by rw [hΦ, Category.id_comp]⟩
  have : Subsingleton {x : s ⟶ s // x ≫ 𝟙 s = 𝟙 s ∧ x ≫ W.frobeniusIterate m = x} :=
    ⟨fun a b ↦ Subtype.ext ((Category.comp_id _).symm.trans
      (a.2.1.trans (b.2.1.symm.trans (Category.comp_id _))))⟩
  rw [Fintype.sum_subsingleton _ ⟨𝟙 s, hx₀⟩]
  exact trace_globalOperator_ofGraph_of_eq_id G hW hΦ _ hx₀.2 _ (hK' := hx ⟨𝟙 s, hx₀⟩)

end AlgebraicGeometry.ProEtale.WeilComplex
