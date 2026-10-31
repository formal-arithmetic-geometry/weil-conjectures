/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenInterchangeReduction.OpenInterchangeReductionData
import all WeilConjectures.SixFunctors.GeneratorReduction.GeneratorKind.TensorAdjunctionReductionSquares
import all WeilConjectures.SixFunctors.GeneratorReduction.ShortWordIntegralDomain
import WeilConjectures.SixFunctors.GeneratorReduction.PrimitiveCompletionEffectivity

/-! Constructor case for structural word substitution.
Source: current blueprint fix-prop-coherence, structural substitution step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.OpenInterchangeReduction


open GeneratorReduction

section

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S)

/-- The reconstruction proof has no word-length hypothesis. -/
private theorem substitutedIntegralDomain (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    {a : S} (B : Word W location a)
    (hB : Word.admissible l E W location o K lo hi torLo torHi B) :
    finiteTorConstructibleIntegral l E (W a) (B.integralValue l E W location o K) := by
  obtain ⟨e⟩ := word_realization l E W location o K lo hi torLo torHi hAdm B hB
  have hsys := word_system_admissible l E W location o K lo hi torLo torHi B hB
  exact domain_of_realization l E (W a) _ lo hi torLo torHi hsys _ e

/-- The completion induction uses the reconstructed domain at each child. -/
private theorem substitutedCompletion_isIso (o : Operations l E)
    {a : S} (B : Word W location a)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (_hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    (_hIntermediate : Word.admissible l E W location o K lo hi torLo torHi B) :
    IsIso (B.completionMap l E W location o K) := by
  revert _hIntermediate
  induction B with
  | input k =>
    intro _
    dsimp only [Word.completionMap]
    infer_instance
  | unit a =>
    intro _
    dsimp only [Word.completionMap]
    infer_instance
  | tensor B C ihB ihC =>
    intro _hIntermediate
    obtain ⟨hB, hC⟩ := _hIntermediate.2
    have := ihB hB
    have := ihC hC
    have := (primitiveCompletionEffectivity l E o).1 _ _ _
      (Or.inl (substitutedIntegralDomain l E W location o K lo hi torLo torHi _hAdm B hB))
      (Or.inl (substitutedIntegralDomain l E W location o K lo hi torLo torHi _hAdm C hC))
    have : IsIso (Prod.mkHom (B.completionMap l E W location o K)
        (C.completionMap l E W location o K)) := by
      exact (Iso.prod (asIso (B.completionMap l E W location o K))
        (asIso (C.completionMap l E W location o K))).isIso_hom
    dsimp only [Word.completionMap]
    infer_instance
  | pull f hs ht hq B ih =>
    intro _hIntermediate
    have hB := _hIntermediate.2
    have := ih hB
    have := (primitiveCompletionEffectivity l E o).2.1 f hs ht hq _
      (Or.inl (substitutedIntegralDomain l E W location o K lo hi torLo torHi _hAdm B hB))
    dsimp only [Word.completionMap]
    infer_instance
  | push f hs ht hq hp B ih =>
    intro _hIntermediate
    have hB := _hIntermediate.2
    have := ih hB
    have := (primitiveCompletionEffectivity l E o).2.2 _ _
      (Or.inl (substitutedIntegralDomain l E W location o K lo hi torLo torHi _hAdm B hB))
    dsimp only [Word.completionMap]
    infer_instance
  | «open» j hj hq B ih =>
    intro _hIntermediate
    let := hj
    have hB := _hIntermediate.2
    have := ih hB
    dsimp only [Word.completionMap]
    infer_instance


private theorem substitutedCompletion_reduction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {S : Type s} {W : S → Scheme.{u}} {I : Type i} {location : I → S}
    (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    {a : S} (B : Word W location a)
    (ha : B.admissible l E W location o K lo hi torLo torHi) :
    (IntegralSystemRealization.calculus l E (W a)).reduction.map
        (B.completionMap l E W location o K) ≫ B.r l E W location o K =
      B.ordinaryR l E o K := by
  have hc {a : S} (B : Word W location a)
      (h : B.admissible l E W location o K lo hi torLo torHi) :
      IsIso (B.completionMap l E W location o K) :=
    substitutedCompletion_isIso l E W location o B K lo hi torLo torHi hAdm h
  induction B with
  | input k =>
    dsimp only [Word.completionMap, Word.r, Word.ordinaryR]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  | unit a =>
    dsimp only [Word.completionMap, Word.r, Word.ordinaryR]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  | @tensor a B C ihB ihC =>
    have := hc B ha.2.1
    have := hc C ha.2.2
    have ht := hc (.tensor B C) ha
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
    dsimp only [Word.completionMap, Word.r, Word.ordinaryR, tensorR]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc,
      inverseOrZero_eq_inv, IsIso.hom_inv_id_assoc]
    have hn := (tensorOrdinaryR l E o (W a)).naturality
      (Prod.mkHom (B.completionMap l E W location o K)
        (C.completionMap l E W location o K))
    dsimp only [tensorOrdinaryR, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.comp_map, Functor.prod_map] at hn
    simp only [Category.assoc] at hn
    dsimp only [tensorOrdinaryR, NatTrans.comp_app, Functor.whiskerRight_app]
    simp only [eqToIso.hom, eqToHom_app] at hn ⊢
    erw [reassoc_of% hn, ← CategoryTheory.Functor.map_comp]
    simp only [prod_comp]
    erw [ihB ha.2.1, ihC ha.2.2]
    exact (Category.assoc _ _ _).symm
  | @pull a b v hs ht hq B ih =>
    have := hc B ha.2
    have hh := hc (.pull v hs ht hq B) ha
    dsimp only [Word.completionMap] at hh
    have : IsIso (((o.ringed.pull v).unit l E).app
        (B.integralValue l E W location o K)) :=
      IsIso.of_isIso_comp_left
        ((IntegralSystemRealization.ringedPull l E v).map
          (B.completionMap l E W location o K)) _
    dsimp only [Word.completionMap, Word.r, Word.ordinaryR, pullR]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc,
      inverseOrZero_eq_inv, IsIso.hom_inv_id_assoc]
    erw [← Category.assoc, (o.realization.reductionPull v).hom.naturality,
      Category.assoc]
    simp only [Functor.comp_map]
    erw [← CategoryTheory.Functor.map_comp, ih ha.2]
  | @push a b v hs ht hq hp B ih =>
    dsimp only [Word.completionMap, Word.r, Word.ordinaryR]
    erw [CategoryTheory.Functor.map_comp, Category.assoc,
      reassoc_of% (pushOrdinaryR_formula l E o v
        (B.integralValue l E W location o K)),
      ]
    have hn := (pushOrdinaryR l E o v).naturality
      (B.completionMap l E W location o K)
    dsimp only [Functor.comp_map] at hn
    erw [reassoc_of% hn]
    erw [← CategoryTheory.Functor.map_comp, ih ha.2]
  | @«open» a b j hj hq B ih =>
    let := hj
    have := hc B ha.2
    dsimp only [Word.completionMap, Word.r, Word.ordinaryR, openR]
    erw [← Category.assoc,
      inverseOrZero_naturality_iso (o.realization.openReduction l E j)
        (B.completionMap l E W location o K),
      Category.assoc]
    simp only [Functor.comp_map]
    erw [← CategoryTheory.Functor.map_comp, ih ha.2]

end

/-- The structuralReductionTensorAssociator component of structural word substitution.
The substitution argument reconstructs child systems, applies the bounded square to
a short skeleton, and pastes naturality; this statement isolates one constructor.
(blueprint: lem-sf-structural-reduction-word-substitution-TensorAssociator)
-/
theorem structuralReductionTensorAssociator
    {D : FiniteFieldDatum.{u}} (coeff : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic coeff.l) E]
    [FiniteDimensional (Padic coeff.l) E]
    (o : GeneratorReduction.Operations coeff.l E)
    (_hShort : ∀ {S : Type s} (W : S → Scheme.{u})
      (_hW : GeneratorReduction.FiniteTypeFamily W D.k)
      {I : Type i} (location : I → S)
      {a : S} {B C : GeneratorReduction.Word W location a}
      (g : GeneratorReduction.GeneratorKind W location B C),
      Structural g → B.length ≤ 3 → C.length ≤ 3 →
      ∀ (K : ∀ k : I, DerivedCategory (scalarReductionSource coeff.l E (W (location k))))
        (lo hi torLo torHi : ℤ),
        (∀ k : I, GeneratorReduction.Admissible coeff.l E
          (IntegralSystemRealization.calculus coeff.l E (W (location k))) (K k)
          lo hi torLo torHi) →
        GeneratorReduction.Word.admissible coeff.l E W location o K lo hi torLo torHi B →
        GeneratorReduction.Word.admissible coeff.l E W location o K lo hi torLo torHi C →
        GeneratorReduction.Assertion coeff.l E W location o K g)
    {S : Type s} (W : S → Scheme.{u})
    (_hW : GeneratorReduction.FiniteTypeFamily W D.k)
    {I : Type i} (location : I → S)
    {a : S}
    {B C T : GeneratorReduction.Word W location a}
    (K : ∀ k : I, DerivedCategory (scalarReductionSource coeff.l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (_hAdm : ∀ k : I, GeneratorReduction.Admissible coeff.l E
      (IntegralSystemRealization.calculus coeff.l E (W (location k))) (K k)
      lo hi torLo torHi)
    (hB : GeneratorReduction.Word.admissible coeff.l E W location o K lo hi torLo torHi
    (GeneratorReduction.Word.tensor (GeneratorReduction.Word.tensor B C) T))
    (hC : GeneratorReduction.Word.admissible coeff.l E W location o K lo hi torLo torHi
    (GeneratorReduction.Word.tensor B (GeneratorReduction.Word.tensor C T))) :
    GeneratorReduction.Assertion coeff.l E W location o K
    (GeneratorReduction.GeneratorKind.tensorAssociator B C T) := by
  have hIso := substitutedCompletion_isIso coeff.l E W location o
    (Word.tensor (Word.tensor B C) T) K lo hi torLo torHi _hAdm hB
  have hSrc := substitutedCompletion_reduction coeff.l E o K lo hi torLo torHi _hAdm
    (Word.tensor (Word.tensor B C) T) hB
  have hTgt := substitutedCompletion_reduction coeff.l E o K lo hi torLo torHi _hAdm
    (Word.tensor B (Word.tensor C T)) hC
  have hOrd := ordinary_tensor_associator coeff.l E o B C T K
  unfold GeneratorReduction.Assertion
  apply (cancel_epi ((IntegralSystemRealization.calculus coeff.l E (W a)).reduction.map
    ((Word.tensor (Word.tensor B C) T).completionMap coeff.l E W location o K))).1
  dsimp only [GeneratorKind.integralMap]
  rw [inverseOrZero_eq_inv, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_inv]
  simp only [← Category.assoc]
  rw [hSrc, hOrd, Category.assoc, hTgt]
  simp only [IsIso.hom_inv_id, Category.id_comp]

end WeilConjectures.OpenInterchangeReduction
