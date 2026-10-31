/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenInterchangeReduction.ProperOpenLambdaOrdinarySquare
import WeilConjectures.SixFunctors.GeneratorReduction.ShortWordCompletionIsomorphism
import Mathlib.CategoryTheory.Adjunction.Mates

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u s i
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction
namespace WeilConjectures.OpenInterchangeReduction

private theorem mate_reconstruction
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {RA : A ⥤ C} {LA : C ⥤ A} {RB : B ⥤ D} {LB : D ⥤ B}
    {P : B ⥤ A} {Q : A ⥤ B} {F : D ⥤ C} {G : C ⥤ D}
    (aa : RA ⊣ LA) (ab : RB ⊣ LB) (ap : P ⊣ Q) (af : F ⊣ G)
    (χ : RB ⋙ F ≅ P ⋙ RA) (K : A) :
    RB.map (Q.map (aa.unit.app K) ≫
        (conjugateIsoEquiv (ap.comp aa) (ab.comp af) χ).hom.app (RA.obj K)) ≫
        ab.counit.app (G.obj (RA.obj K)) =
      (mateEquiv ap af χ.hom).natTrans.app K := by
  have hv := conjugateEquiv_counit (ap.comp aa) (ab.comp af) χ.hom (RA.obj K)
  have hn := χ.hom.naturality (Q.map (aa.unit.app K))
  have hε := ap.counit.naturality (aa.unit.app K)
  apply (af.homEquiv _ _).symm.injective
  change F.map _ ≫ af.counit.app _ = _
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc]
  change _ = F.map ((mateEquiv ap af χ.hom).natTrans.app K) ≫ af.counit.app _
  rw [mateEquiv_counit ap af χ.hom K]
  simp only [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj] at hv
  rw [CategoryTheory.Functor.map_comp, Category.assoc, conjugateIsoEquiv_apply_hom]
  change F.map (RB.map (Q.map (aa.unit.app K))) ≫
      F.map (RB.map ((conjugateEquiv (ap.comp aa) (ab.comp af) χ.hom).app
        (RA.obj K))) ≫ _ = _
  rw [hv]
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn hε
  rw [← Category.assoc, hn, Category.assoc, ← RA.map_comp_assoc, hε,
    RA.map_comp, Category.assoc, aa.left_triangle_components,
    Category.comp_id]

private theorem inverseOrZero_eq_inv {A : Type*} [Category A] [HasZeroMorphisms A]
    {X Y : A} (f : X ⟶ Y) [IsIso f] : inverseOrZero f = inv f := by
  classical
  simp only [inverseOrZero, dif_pos (inferInstance : IsIso f)]

private theorem inverse_square {A : Type*} [Category A] [HasZeroMorphisms A]
    {X Y X' Y' : A} (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    [IsIso a] [IsIso b] (h : f ≫ b = a ≫ g) :
    g ≫ inverseOrZero b = inverseOrZero a ≫ f := by
  rw [inverseOrZero_eq_inv, inverseOrZero_eq_inv]
  apply (cancel_epi a).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem inverse_naturality {A N : Type*} [Category A] [Category N]
    [HasZeroMorphisms N] {F G : A ⥤ N} (α : F ⟶ G) {X Y : A} (f : X ⟶ Y)
    [IsIso (α.app X)] [IsIso (α.app Y)] :
    G.map f ≫ inverseOrZero (α.app Y) = inverseOrZero (α.app X) ≫ F.map f := by
  apply inverse_square
  exact α.naturality f

private theorem natTrans_isIso_at_iso {A N : Type*} [Category A] [Category N]
    {F G : A ⥤ N} (α : F ⟶ G) {X Y : A} (f : X ⟶ Y) [IsIso f]
    [IsIso (α.app X)] : IsIso (α.app Y) := by
  have hh : IsIso (F.map f ≫ α.app Y) := by
    rw [α.naturality f]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map f) _

private theorem inverseOrZero_naturality_iso {A N : Type*} [Category A] [Category N]
    [HasZeroMorphisms N] {F G : A ⥤ N} (α : F ⟶ G) {X Y : A}
    (f : X ⟶ Y) [IsIso f] :
    G.map f ≫ inverseOrZero (α.app Y) = inverseOrZero (α.app X) ≫ F.map f := by
  classical
  by_cases hx : IsIso (α.app X)
  · have := natTrans_isIso_at_iso α f
    exact inverse_naturality α f
  · have hy : ¬ IsIso (α.app Y) := by
      intro hY
      exact hx (natTrans_isIso_at_iso α (inv f))
    simp only [inverseOrZero, dif_neg hx, dif_neg hy, comp_zero, zero_comp]

private theorem pushOrdinaryR_formula (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (o : Operations l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    (IntegralSystemRealization.calculus l E Y).reduction.map
        ((IntegralSystemRealization.ringedPush l E f).map
            ((IntegralSystemRealization.calculus l E X).adjunction.unit.app K) ≫
          (o.realization.push l E f).inv.app
            ((IntegralSystemRealization.calculus l E X).reduction.obj K)) ≫
        pushR l E o f K =
      (ordinaryPushReductionY9 l E o.system o.realization f).app K := by
  exact mate_reconstruction
    (IntegralSystemRealization.calculus l E X).adjunction
    (IntegralSystemRealization.calculus l E Y).adjunction
    (IntegralSystemRealization.ringedAdj l E f) (o.system.direct f).adj
    (o.realization.reductionPull f).symm K

private theorem word_completion_reduction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E)
    {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    {a : S} (B : Word W location a) (hlen : B.length ≤ 3)
    (ha : B.admissible l E W location o K lo hi torLo torHi) :
    (IntegralSystemRealization.calculus l E (W a)).reduction.map
        (B.completionMap l E W location o K) ≫ B.r l E W location o K =
      properOpenOrdinaryR l E location o K B := by
  have hc {a : S} (B : Word W location a) (hl : B.length ≤ 3)
      (h : B.admissible l E W location o K lo hi torLo torHi) :
      IsIso (B.completionMap l E W location o K) :=
    completionMap_isIso l E W location o B hl K lo hi torLo torHi hAdm h
  induction B with
  | input k =>
    dsimp only [Word.completionMap, Word.r, properOpenOrdinaryR]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  | unit a =>
    dsimp only [Word.completionMap, Word.r, properOpenOrdinaryR]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  | @tensor a B C ihB ihC =>
    have hB : B.length ≤ 3 := by dsimp only [Word.length] at hlen; omega
    have hC : C.length ≤ 3 := by dsimp only [Word.length] at hlen; omega
    have := hc B hB ha.2.1
    have := hc C hC ha.2.2
    have ht := hc (.tensor B C) hlen ha
    have : IsIso (Prod.mkHom (B.completionMap l E W location o K)
        (C.completionMap l E W location o K)) :=
      (Iso.prod (asIso _) (asIso _)).isIso_hom
    dsimp only [Word.completionMap] at ht
    have : IsIso ((o.ringed.tensor (W a)).ordinary.tensor.map
        (Prod.mkHom (B.completionMap l E W location o K)
          (C.completionMap l E W location o K))) := by infer_instance
    have : IsIso ((tensorCompletion l E o (W a)).app
        (B.integralValue l E W location o K, C.integralValue l E W location o K)) := by
      exact IsIso.of_isIso_comp_left
        ((o.ringed.tensor (W a)).ordinary.tensor.map
          (Prod.mkHom (B.completionMap l E W location o K)
            (C.completionMap l E W location o K))) _
    dsimp only [Word.completionMap, Word.r, properOpenOrdinaryR, tensorR]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc,
      inverseOrZero_eq_inv, IsIso.hom_inv_id_assoc]
    have hn := (ordinaryTensorReductionY9 l E o.ringed (W a)).naturality
      (Prod.mkHom (B.completionMap l E W location o K)
        (C.completionMap l E W location o K))
    dsimp only [ordinaryTensorReductionY9, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.comp_map, Functor.prod_map] at hn
    simp only [Category.assoc] at hn
    dsimp only [ordinaryTensorReductionY9, NatTrans.comp_app, Functor.whiskerRight_app]
    simp only [eqToIso.hom, eqToHom_app] at hn ⊢
    erw [reassoc_of% hn, ← CategoryTheory.Functor.map_comp]
    simp only [prod_comp]
    erw [ihB hB ha.2.1, ihC hC ha.2.2]
    exact (Category.assoc _ _ _).symm
  | @pull a b v hs ht hq B ih =>
    have hB : B.length ≤ 3 := by dsimp only [Word.length] at hlen; omega
    have := hc B hB ha.2
    have hh := hc (.pull v hs ht hq B) hlen ha
    dsimp only [Word.completionMap] at hh
    have : IsIso (((o.ringed.pull v).unit l E).app
        (B.integralValue l E W location o K)) :=
      IsIso.of_isIso_comp_left
        ((IntegralSystemRealization.ringedPull l E v).map
          (B.completionMap l E W location o K)) _
    dsimp only [Word.completionMap, Word.r, properOpenOrdinaryR, pullR]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc,
      inverseOrZero_eq_inv, IsIso.hom_inv_id_assoc]
    erw [← Category.assoc, (o.realization.reductionPull v).hom.naturality,
      Category.assoc]
    simp only [Functor.comp_map]
    erw [← CategoryTheory.Functor.map_comp, ih hB ha.2]
  | @push a b v hs ht hq hp B ih =>
    have hB : B.length ≤ 3 := by dsimp only [Word.length] at hlen; omega
    dsimp only [Word.completionMap, Word.r, properOpenOrdinaryR]
    erw [CategoryTheory.Functor.map_comp, Category.assoc,
      reassoc_of% (pushOrdinaryR_formula l E o v
        (B.integralValue l E W location o K)),
      ]
    have hn := (ordinaryPushReductionY9 l E o.system o.realization v).naturality
      (B.completionMap l E W location o K)
    dsimp only [Functor.comp_map] at hn
    erw [reassoc_of% hn]
    erw [← CategoryTheory.Functor.map_comp, ih hB ha.2]
  | @«open» a b j hj hq B ih =>
    let := hj
    have hB : B.length ≤ 3 := by dsimp only [Word.length] at hlen; omega
    have := hc B hB ha.2
    dsimp only [Word.completionMap, Word.r, properOpenOrdinaryR, openR]
    erw [← Category.assoc,
      inverseOrZero_naturality_iso (o.realization.openReduction l E j)
        (B.completionMap l E W location o K),
      Category.assoc]
    simp only [Functor.comp_map]
    erw [← CategoryTheory.Functor.map_comp, ih hB ha.2]

/-- Push constructor equation for proper/open completion transport.
Source: the recursive completion comparison in
`fix-prop-coherence.proof.md`, constructor case `push`.
The proof expands this single constructor using the normalized operation comparison,
naturality, and the admissibility hypotheses for its immediate children.
(blueprint: lem-sf-proper-open-lambda-completion-transport-push) -/
theorem properOpenLambdaCompletionTransport_push
    {D : FiniteFieldDatum.{u}} (Cf : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic Cf.l) E]
    [FiniteDimensional (Padic Cf.l) E] (o : Operations Cf.l E)
    {S : Type s} (W : S → Scheme.{u})
    {I : Type i} (location : I → S)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource Cf.l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hInputs : ∀ k : I, Admissible Cf.l E
      (IntegralSystemRealization.calculus Cf.l E (W (location k))) (K k)
      lo hi torLo torHi)
    {a b : S} (f : W a ⟶ W b) (hs : IsSeparated f)
    (ht : LocallyOfFiniteType f) (hq : QuasiCompact f) (hp : IsProper f)
    (B : Word W location a)
    (hLength : (Word.push f hs ht hq hp B).length ≤ 3)
    (hAdmissible : Word.admissible Cf.l E W location o K lo hi torLo torHi
      (Word.push f hs ht hq hp B)) :
    (IntegralSystemRealization.calculus Cf.l E (W b)).reduction.map
        ((Word.push f hs ht hq hp B).completionMap Cf.l E W location o K) ≫
      (Word.push f hs ht hq hp B).r Cf.l E W location o K =
      properOpenOrdinaryR Cf.l E location o K (Word.push f hs ht hq hp B) := by
  exact word_completion_reduction Cf.l E o W location K lo hi torLo torHi hInputs
    (Word.push f hs ht hq hp B) hLength hAdmissible

end WeilConjectures.OpenInterchangeReduction
