/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.SixFunctors.OpenInterchangeReductionData
import Sheaf.SixFunctors.CanonicalOpenReductionIsIso
import Sheaf.SixFunctors.PrimitiveCompletionEffectivity
import Sheaf.SixFunctors.ShortWordIntegralDomain
import Sheaf.SixFunctors.ProperOpenInterchangeReductionSquare
import Sheaf.SixFunctors.ProperOpenLambdaReductionSquare
import Sheaf.SixFunctors.OpenTensorReductionSquare
import Sheaf.SixFunctors.OpenBaseChangeReductionSquare


/-! # Open and proper/open coefficient squares

Source: blueprint main-20261015, fix-prop-coherence.proof.md, the maps-used sentence
and the open-adjunction/clopen expansion
(blueprint: lem-sf-open-interchange-reduction-squares).

The existing finite-word interface supplies the actual recursive coefficient maps,
independently completed ringed-site maps, and four-factor lambda. The predicates here
select generators in that interface; they introduce no new operations or comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u s i
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction

namespace WeilConjectures.OpenInterchangeReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

-- The published completion induction, kept below the parent coherence module.
private theorem completionMap_isIso {S : Type s} (W : S → Scheme.{u})
    {I : Type i} (location : I → S) (o : Operations l E)
    {a : S} (B : Word W location a)
    (_hLength : B.length ≤ 3)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (_hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    (_hIntermediate : Word.admissible l E W location o K lo hi torLo torHi B) :
    IsIso (B.completionMap l E W location o K) := by
  revert _hLength _hIntermediate
  induction B with
  | input k =>
    intro _ _
    dsimp only [Word.completionMap]
    infer_instance
  | unit a =>
    intro _ _
    dsimp only [Word.completionMap]
    infer_instance
  | tensor B C ihB ihC =>
    intro _hLength _hIntermediate
    obtain ⟨hB, hC⟩ := _hIntermediate.2
    have hlenB : B.length ≤ 2 := by simp only [Word.length] at _hLength; omega
    have hlenC : C.length ≤ 2 := by simp only [Word.length] at _hLength; omega
    have := ihB (by omega) hB
    have := ihC (by omega) hC
    have := (primitiveCompletionEffectivity l E o).1 _ _ _
      (shortWordIntegralDomain l E W location o B hlenB K lo hi torLo torHi _hAdm hB)
      (shortWordIntegralDomain l E W location o C hlenC K lo hi torLo torHi _hAdm hC)
    have : IsIso (Prod.mkHom (B.completionMap l E W location o K)
        (C.completionMap l E W location o K)) := by
      exact (Iso.prod (asIso (B.completionMap l E W location o K))
        (asIso (C.completionMap l E W location o K))).isIso_hom
    dsimp only [Word.completionMap]
    infer_instance
  | pull f hs ht hq B ih =>
    intro _hLength _hIntermediate
    have hB := _hIntermediate.2
    have hlen : B.length ≤ 2 := by simp only [Word.length] at _hLength; omega
    have := ih (by omega) hB
    have := (primitiveCompletionEffectivity l E o).2.1 f hs ht hq _
      (shortWordIntegralDomain l E W location o B hlen K lo hi torLo torHi _hAdm hB)
    dsimp only [Word.completionMap]
    infer_instance
  | push f hs ht hq hp B ih =>
    intro _hLength _hIntermediate
    have hB := _hIntermediate.2
    have hlen : B.length ≤ 2 := by simp only [Word.length] at _hLength; omega
    have := ih (by omega) hB
    have := (primitiveCompletionEffectivity l E o).2.2 _ _
      (shortWordIntegralDomain l E W location o B hlen K lo hi torLo torHi _hAdm hB)
    dsimp only [Word.completionMap]
    infer_instance
  | «open» j hj hq B ih =>
    intro _hLength _hIntermediate
    let := hj
    have hB := _hIntermediate.2
    have hlen : B.length ≤ 3 := by simp only [Word.length] at _hLength; omega
    have := ih hlen hB
    dsimp only [Word.completionMap]
    infer_instance

private theorem inverseOrZero_eq_inv {A : Type*} [Category A] [HasZeroMorphisms A]
    {X Y : A} (f : X ⟶ Y) [IsIso f] : inverseOrZero f = inv f := by
  classical
  unfold inverseOrZero
  rw [dif_pos (inferInstance : IsIso f)]

private theorem inverse_square {A B : Type*} [Category A] [Category B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] (F : A ⥤ B)
    {X Y : A} {X' Y' : B} (a : X ⟶ Y) (b : X' ⟶ Y')
    [IsIso a] [IsIso b] (rX : F.obj X ⟶ X') (rY : F.obj Y ⟶ Y')
    (h : rX ≫ b = F.map a ≫ rY) :
    rY ≫ inverseOrZero b = F.map (inverseOrZero a) ≫ rX := by
  simp only [inverseOrZero_eq_inv]
  apply (cancel_epi (F.map a)).1
  simp only [← F.map_comp_assoc, IsIso.hom_inv_id, F.map_id, Category.id_comp]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem inverse_naturality {A B : Type*} [Category A] [Category B]
    [HasZeroMorphisms B] {F G : A ⥤ B} (t : F ⟶ G) {X Y : A}
    (f : X ⟶ Y) [IsIso (t.app X)] [IsIso (t.app Y)] :
    G.map f ≫ inverseOrZero (t.app Y) = inverseOrZero (t.app X) ≫ F.map f := by
  simp only [inverseOrZero_eq_inv]
  apply (cancel_epi (t.app X)).1
  rw [← Category.assoc, ← t.naturality, Category.assoc]
  simp only [IsIso.hom_inv_id, Category.comp_id, IsIso.hom_inv_id_assoc]

private theorem systemMap_isIso {S : Type s} (W : S → Scheme.{u})
    {I : Type i} (location : I → S) (o : Operations l E)
    (M : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C)
    (hg : OpenIsomorphism g) : IsIso (g.systemMap l E W location o M) := by
  cases g <;> simp only [OpenIsomorphism] at hg
  all_goals dsimp only [GeneratorKind.systemMap]; infer_instance

private theorem ringedMap_isIso {S : Type s} (W : S → Scheme.{u})
    {I : Type i} (location : I → S) (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C)
    (hg : OpenIsomorphism g) : IsIso (g.ringedMap l E W location o K) := by
  cases g <;> simp only [OpenIsomorphism] at hg
  all_goals dsimp only [GeneratorKind.ringedMap]; infer_instance

private theorem systemMap_naturality {S : Type s} (W : S → Scheme.{u})
    {I : Type i} (location : I → S) (o : Operations l E)
    {M N : ∀ k : I, coefficientSequenceDerived l E (W (location k))}
    (f : ∀ k : I, M k ⟶ N k)
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C)
    (hg : OpenGenerator g) :
    systemInputMap l E W location o f B ≫ g.systemMap l E W location o N =
      g.systemMap l E W location o M ≫ systemInputMap l E W location o f C := by
  cases g <;> simp only [OpenGenerator] at hg
  case openBaseChange =>
    exact (o.opens.beta _ _ _ _ _ _).hom.naturality (systemInputMap l E W location o f _)
  case openTensor =>
    exact (o.opens.projection _).hom.naturality
      (Prod.mkHom (systemInputMap l E W location o f _) (systemInputMap l E W location o f _))
  case properOpenLambda =>
    exact (IntegralSystemRealization.properOpenLambda l E o.system o.composition o.opens
      _ _ _ _ _).hom.naturality (systemInputMap l E W location o f _)
  case properOpenInterchange =>
    dsimp only [systemInputMap, GeneratorKind.systemMap]
    rw [← Adjunction.homEquiv_naturality_left_symm,
      ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    exact (IntegralSystemRealization.properOpenLambda l E o.system o.composition o.opens
      _ _ _ _ _).inv.naturality (systemInputMap l E W location o f _)

private def ringedInputMap {S : Type s} (W : S → Scheme.{u})
    {I : Type i} (location : I → S) (o : Operations l E)
    {K L : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))}
    (f : ∀ k : I, K k ⟶ L k) : {a : S} → (B : Word W location a) →
      B.ringedValue l E W location o K ⟶ B.ringedValue l E W location o L
  | _, .input k => f k
  | _, .unit _ => 𝟙 _
  | a, .tensor B C => (o.ringed.tensor (W a)).ordinary.tensor.map
      (Prod.mkHom (ringedInputMap W location o f B) (ringedInputMap W location o f C))
  | _, .pull v _ _ _ B => (IntegralSystemRealization.ringedPull l E v).map
      (ringedInputMap W location o f B)
  | _, .push v _ _ _ _ B => (IntegralSystemRealization.ringedPush l E v).map
      (ringedInputMap W location o f B)
  | _, .open j hj _ B => let := hj
      (IntegralSystemRealization.ringedOpen l E j).map
        (ringedInputMap W location o f B)

private theorem ringedMap_naturality {S : Type s} (W : S → Scheme.{u})
    {I : Type i} (location : I → S) (o : Operations l E)
    {K L : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))}
    (f : ∀ k : I, K k ⟶ L k)
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C)
    (hg : OpenGenerator g) :
    ringedInputMap l E W location o f B ≫ g.ringedMap l E W location o L =
      g.ringedMap l E W location o K ≫ ringedInputMap l E W location o f C := by
  cases g <;> simp only [OpenGenerator] at hg
  case openBaseChange =>
    exact (o.ringedOpens.beta _ _ _ _ _ _).hom.naturality (ringedInputMap l E W location o f _)
  case openTensor =>
    exact (o.ringedOpens.projection _).hom.naturality
      (Prod.mkHom (ringedInputMap l E W location o f _) (ringedInputMap l E W location o f _))
  case properOpenLambda =>
    exact (IntegralSystemRealization.ringedProperOpenLambda l E o.ringed o.ringedOpens
      _ _ _ _ _).hom.naturality (ringedInputMap l E W location o f _)
  case properOpenInterchange =>
    dsimp only [ringedInputMap, GeneratorKind.ringedMap]
    rw [← Adjunction.homEquiv_naturality_left_symm,
      ← Adjunction.homEquiv_naturality_right_symm]
    apply congrArg (fun z ↦ (IntegralSystemRealization.ringedOpenAdj l E _).homEquiv _ _ |>.symm z)
    exact (IntegralSystemRealization.ringedProperOpenLambda l E o.ringed o.ringedOpens
      _ _ _ _ _).inv.naturality (ringedInputMap l E W location o f _)

private theorem completionMap_naturality {S : Type s} (W : S → Scheme.{u})
    {I : Type i} (location : I → S) (o : Operations l E)
    {K L : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))}
    (f : ∀ k : I, K k ⟶ L k) {a : S} (B : Word W location a) :
    ringedInputMap l E W location o f B ≫ B.completionMap l E W location o L =
      B.completionMap l E W location o K ≫ integralInputMap l E W location o f B := by
  induction B with
  | input k => simp only [ringedInputMap, Word.completionMap, integralInputMap,
      Category.comp_id, Category.id_comp]
  | unit a => simp only [ringedInputMap, Word.completionMap, integralInputMap,
      Category.comp_id]
  | tensor B C ihB ihC =>
    dsimp only [ringedInputMap, Word.completionMap, integralInputMap]
    rw [← Category.assoc, ← Functor.map_comp]
    have h : Prod.mkHom (ringedInputMap l E W location o f B)
        (ringedInputMap l E W location o f C) ≫
        Prod.mkHom (B.completionMap l E W location o L)
          (C.completionMap l E W location o L) =
        Prod.mkHom (B.completionMap l E W location o K)
          (C.completionMap l E W location o K) ≫
        Prod.mkHom (integralInputMap l E W location o f B)
          (integralInputMap l E W location o f C) := by
      ext <;> assumption
    rw [h, Functor.map_comp, Category.assoc]
    simp only [Category.assoc]
    apply congrArg (fun z ↦ _ ≫ z)
    exact (tensorCompletion l E o _).naturality
      (Prod.mkHom (integralInputMap l E W location o f B)
        (integralInputMap l E W location o f C))
  | pull v hs ht hq B ih =>
    dsimp only [ringedInputMap, Word.completionMap, integralInputMap]
    rw [← Category.assoc, ← Functor.map_comp, ih, Functor.map_comp, Category.assoc]
    simp only [Category.assoc]
    apply congrArg (fun z ↦ _ ≫ z)
    exact ((o.ringed.pull v).unit l E).naturality
      (integralInputMap l E W location o f B)
  | push v hs ht hq hp B ih =>
    dsimp only [ringedInputMap, Word.completionMap, integralInputMap]
    rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ih, Functor.map_comp]
    simp only [Category.assoc]
    congr 1
    rw [← Functor.map_comp_assoc]
    have hn := (IntegralSystemRealization.calculus l E _).adjunction.unit.naturality
      (integralInputMap l E W location o f B)
    dsimp only [Functor.id_map, Functor.comp_map] at hn
    rw [hn]
    rw [Functor.map_comp, Category.assoc]
    congr 1
    exact (o.realization.push l E v).inv.naturality
      ((IntegralSystemRealization.calculus l E _).reduction.map
        (integralInputMap l E W location o f B))
  | «open» j hj hq B ih =>
    let := hj
    dsimp only [ringedInputMap, Word.completionMap, integralInputMap]
    rw [← Functor.map_comp, ← Functor.map_comp, ih]

private theorem integralMap_naturality {S : Type s} (W : S → Scheme.{u})
    {I : Type i} (location : I → S) (o : Operations l E)
    {K L : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))}
    (f : ∀ k : I, K k ⟶ L k)
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C)
    (hg : OpenGenerator g)
    [IsIso (B.completionMap l E W location o K)]
    [IsIso (B.completionMap l E W location o L)] :
    integralInputMap l E W location o f B ≫ g.integralMap l E W location o L =
      g.integralMap l E W location o K ≫ integralInputMap l E W location o f C := by
  apply (cancel_epi (B.completionMap l E W location o K)).1
  dsimp only [GeneratorKind.integralMap]
  simp only [inverseOrZero_eq_inv, ← Category.assoc]
  rw [← completionMap_naturality l E W location o f B]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, ringedMap_naturality l E W location o f g hg, Category.assoc,
    completionMap_naturality l E W location o f C]

private theorem tensorR_naturality (o : Operations l E) (X : Scheme.{u})
    {K K' L L' : DerivedCategory (scalarReductionSource l E X)}
    (f : K ⟶ L) (f' : K' ⟶ L')
    [IsIso ((IntegralSystemRealization.calculus l E X).reduction.map
      ((tensorCompletion l E o X).app (K, K')))]
    [IsIso ((IntegralSystemRealization.calculus l E X).reduction.map
      ((tensorCompletion l E o X).app (L, L')))] :
    (IntegralSystemRealization.calculus l E X).reduction.map
        ((integralCompletedTensor l E X).map (Prod.mkHom f f')) ≫
      tensorR l E o X L L' =
    tensorR l E o X K K' ≫
      (IntegralSystemRealization.calculus l E X).systemClosed.tensor.map
        (Prod.mkHom ((IntegralSystemRealization.calculus l E X).reduction.map f)
          ((IntegralSystemRealization.calculus l E X).reduction.map f')) := by
  let R := (IntegralSystemRealization.calculus l E X).reduction
  have : IsIso ((whiskerRight (tensorCompletion l E o X) R).app (K, K')) :=
    (inferInstance : IsIso (R.map ((tensorCompletion l E o X).app (K, K'))))
  have : IsIso ((whiskerRight (tensorCompletion l E o X) R).app (L, L')) :=
    (inferInstance : IsIso (R.map ((tensorCompletion l E o X).app (L, L'))))
  have hn := inverse_naturality
    (whiskerRight (tensorCompletion l E o X) R) (Prod.mkHom f f')
  dsimp only [whiskerRight_app, Functor.comp_map] at hn
  have ht := (Functor.isoWhiskerRight (eqToIso (o.ringed.tensorClosed X)) R ≪≫
    (IntegralSystemRealization.calculus l E X).reductionTensor).hom.naturality
      (Prod.mkHom f f')
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    whiskerRight_app, eqToIso.hom, eqToHom_app, Functor.comp_map] at ht
  dsimp only [tensorR]
  rw [← Category.assoc, hn]
  simp only [Category.assoc]
  simpa only [Category.assoc, eqToIso.hom, Functor.prod_map] using
    congrArg (fun z ↦ inverseOrZero (R.map
      ((tensorCompletion l E o X).app (K, K'))) ≫ z) ht

private theorem pullR_naturality (o : Operations l E) {X Y : Scheme.{u}} (v : X ⟶ Y)
    {K L : DerivedCategory (scalarReductionSource l E Y)} (f : K ⟶ L)
    [IsIso ((IntegralSystemRealization.calculus l E X).reduction.map
      (((o.ringed.pull v).unit l E).app K))]
    [IsIso ((IntegralSystemRealization.calculus l E X).reduction.map
      (((o.ringed.pull v).unit l E).app L))] :
    (IntegralSystemRealization.calculus l E X).reduction.map
        ((integralDerivedPullback l E v).map f) ≫ pullR l E o v L =
    pullR l E o v K ≫ (IntegralSystemRealization.pull l E v).map
      ((IntegralSystemRealization.calculus l E Y).reduction.map f) := by
  have : IsIso ((whiskerRight ((o.ringed.pull v).unit l E)
      (IntegralSystemRealization.calculus l E X).reduction).app K) :=
    (inferInstance : IsIso ((IntegralSystemRealization.calculus l E X).reduction.map
      (((o.ringed.pull v).unit l E).app K)))
  have : IsIso ((whiskerRight ((o.ringed.pull v).unit l E)
      (IntegralSystemRealization.calculus l E X).reduction).app L) :=
    (inferInstance : IsIso ((IntegralSystemRealization.calculus l E X).reduction.map
      (((o.ringed.pull v).unit l E).app L)))
  have hn := inverse_naturality (whiskerRight ((o.ringed.pull v).unit l E)
    (IntegralSystemRealization.calculus l E X).reduction) f
  dsimp only [whiskerRight_app, Functor.comp_map] at hn
  dsimp only [pullR]
  rw [← Category.assoc, hn, Category.assoc]
  have ht := (o.realization.reductionPull v).hom.naturality f
  dsimp only [Functor.comp_map] at ht
  simpa only [Category.assoc] using congrArg
    (fun z ↦ inverseOrZero ((IntegralSystemRealization.calculus l E X).reduction.map
      (((o.ringed.pull v).unit l E).app K)) ≫ z) ht

private theorem reduction_naturality {S : Type s} (W : S → Scheme.{u})
    {I : Type i} (location : I → S) (o : Operations l E)
    {K L : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))}
    (f : ∀ k : I, K k ⟶ L k) (lo hi torLo torHi : ℤ)
    (hK : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    (hL : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (L k) lo hi torLo torHi)
    {a : S} (B : Word W location a) (hB : B.length ≤ 3)
    (hBK : B.admissible l E W location o K lo hi torLo torHi)
    (hBL : B.admissible l E W location o L lo hi torLo torHi) :
    (IntegralSystemRealization.calculus l E (W a)).reduction.map
        (integralInputMap l E W location o f B) ≫ B.r l E W location o L =
      B.r l E W location o K ≫ systemInputMap l E W location o
        (fun k ↦ (IntegralSystemRealization.calculus l E (W (location k))).reduction.map
          (f k)) B := by
  induction B with
  | input k => simp only [integralInputMap, systemInputMap, Word.r,
      Category.comp_id, Category.id_comp]
  | unit a =>
    dsimp only [integralInputMap, systemInputMap, Word.r, Word.systemValue]
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  | tensor B C ihB ihC =>
    have hBc : B.length ≤ 3 := by dsimp [Word.length] at hB; omega
    have hCc : C.length ≤ 3 := by dsimp [Word.length] at hB; omega
    have hBK' := hBK.2.1
    have hCK' := hBK.2.2
    have hBL' := hBL.2.1
    have hCL' := hBL.2.2
    have cBK := completionMap_isIso l E W location o B hBc K lo hi torLo torHi hK hBK'
    have cCK := completionMap_isIso l E W location o C hCc K lo hi torLo torHi hK hCK'
    have cBL := completionMap_isIso l E W location o B hBc L lo hi torLo torHi hL hBL'
    have cCL := completionMap_isIso l E W location o C hCc L lo hi torLo torHi hL hCL'
    have cTK := completionMap_isIso l E W location o (.tensor B C) hB K
      lo hi torLo torHi hK hBK
    have cTL := completionMap_isIso l E W location o (.tensor B C) hB L
      lo hi torLo torHi hL hBL
    have := cBK
    have := cCK
    have := cBL
    have := cCL
    have : IsIso (Prod.mkHom (B.completionMap l E W location o K)
        (C.completionMap l E W location o K)) := (isIso_prod_iff _ _).2 ⟨cBK, cCK⟩
    have : IsIso (Prod.mkHom (B.completionMap l E W location o L)
        (C.completionMap l E W location o L)) := (isIso_prod_iff _ _).2 ⟨cBL, cCL⟩
    dsimp only [Word.completionMap] at cTK cTL
    have := cTK
    have := cTL
    have tK := IsIso.of_isIso_comp_left
      ((o.ringed.tensor _).ordinary.tensor.map
        (Prod.mkHom (B.completionMap l E W location o K)
          (C.completionMap l E W location o K)))
      ((tensorCompletion l E o _).app
        (B.integralValue l E W location o K, C.integralValue l E W location o K))
    have tL := IsIso.of_isIso_comp_left
      ((o.ringed.tensor _).ordinary.tensor.map
        (Prod.mkHom (B.completionMap l E W location o L)
          (C.completionMap l E W location o L)))
      ((tensorCompletion l E o _).app
        (B.integralValue l E W location o L, C.integralValue l E W location o L))
    have := tK
    have := tL
    dsimp only [integralInputMap, systemInputMap, Word.r]
    rw [← Category.assoc, tensorR_naturality]
    simp only [Category.assoc, ← Functor.map_comp]
    congr 1
    congr 1
    ext
    · exact ihB hBc hBK' hBL'
    · exact ihC hCc hCK' hCL'
  | pull v hs ht hq B ih =>
    have hBc : B.length ≤ 3 := by dsimp [Word.length] at hB; omega
    have cBK := completionMap_isIso l E W location o B hBc K lo hi torLo torHi hK hBK.2
    have cBL := completionMap_isIso l E W location o B hBc L lo hi torLo torHi hL hBL.2
    have cPK := completionMap_isIso l E W location o (.pull v hs ht hq B) hB K
      lo hi torLo torHi hK hBK
    have cPL := completionMap_isIso l E W location o (.pull v hs ht hq B) hB L
      lo hi torLo torHi hL hBL
    have := cBK
    have := cBL
    dsimp only [Word.completionMap] at cPK cPL
    have := cPK
    have := cPL
    have pK := IsIso.of_isIso_comp_left
      ((IntegralSystemRealization.ringedPull l E v).map
        (B.completionMap l E W location o K))
      (((o.ringed.pull v).unit l E).app (B.integralValue l E W location o K))
    have pL := IsIso.of_isIso_comp_left
      ((IntegralSystemRealization.ringedPull l E v).map
        (B.completionMap l E W location o L))
      (((o.ringed.pull v).unit l E).app (B.integralValue l E W location o L))
    have := pK
    have := pL
    dsimp only [integralInputMap, systemInputMap, Word.r]
    rw [← Category.assoc, pullR_naturality, Category.assoc,
      ← Functor.map_comp, ih hBc hBK.2 hBL.2, Functor.map_comp, Category.assoc]
  | push v hs ht hq hp B ih =>
    have hBc : B.length ≤ 3 := by dsimp [Word.length] at hB; omega
    dsimp only [integralInputMap, systemInputMap, Word.r]
    rw [← Category.assoc]
    have hn := (IntegralSystemRealization.calculus l E _).adjunction.counit.naturality
      ((IntegralSystemRealization.Operations.push l E o.system v).map
        ((IntegralSystemRealization.calculus l E _).reduction.map
          (integralInputMap l E W location o f B)))
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [show (IntegralSystemRealization.calculus l E _).reduction.map
        ((integralPush l E o v).map (integralInputMap l E W location o f B)) ≫
        pushR l E o v (B.integralValue l E W location o L) = _ from hn,
      Category.assoc, ← Functor.map_comp, ih hBc hBK.2 hBL.2,
      Functor.map_comp, Category.assoc]
    rfl
  | «open» j hj hq B ih =>
    let := hj
    have hBc : B.length ≤ 3 := by dsimp [Word.length] at hB; omega
    have hOK := canonicalOpenReduction_isIso l E o j (B.integralValue l E W location o K)
    have hOL := canonicalOpenReduction_isIso l E o j (B.integralValue l E W location o L)
    have := hOK
    have := hOL
    have hn := inverse_naturality (o.realization.openReduction l E j)
      (integralInputMap l E W location o f B)
    dsimp only [Functor.comp_map] at hn
    dsimp only [integralInputMap, systemInputMap, Word.r, openR]
    rw [← Category.assoc, hn, Category.assoc,
      ← Functor.map_comp, ih hBc hBK.2 hBL.2, Functor.map_comp, Category.assoc]

/-- From structural coefficient squares to the canonical open squares, their inverses,
and the four-factor proper/open restriction and its open transpose. All maps are in
ordinary derived categories of strict semilinear systems, before finite evaluation.
Source: blueprint main-20261015, fix-prop-coherence.proof.md, maps-used sentence
(blueprint: lem-sf-open-interchange-reduction-squares).

Proof, step 1: squares paste by functoriality and associativity. Multiply the square
of an isomorphism by its two inverses to get the inverse square. Naturality of each
primitive r_A and the defining recursion for Word.r give unary whiskering; tensor
bifunctoriality gives whiskering in both independent slots. Induct over finite contexts.

Step 2: by lem-sf-open-tensor-normalization, beta inverse is the open adjunct of
inverse theta after inverse image of the open unit. Theta is the pair of pullback
compositors for the cartesian square. Paste their structural squares, the open-unit
square and the open-counit square. Inversion gives the beta square.

Step 3: restriction/tensor compatibility uses flat-term K-flat representatives.
Both quotient maps send x tensor y to (1 tensor j*x) tensor (1 tensor j*y).
The recorded completion map has that first Roos coordinate and zero shifted coordinate.
Restriction preserves quotient projections, the scalar unit and the signed tensor
differential. Thus the maps agree as strict quotient-complex maps. Use
lem-sf-immersion-completed-pullback-comparison, def-sf-tensor-completion-comparison
and lem-weil-pbc-site-derived-tensor-descent to obtain the whole-system square.

Step 4: gamma inverse is the open adjunct of the open unit tensor identity followed
by inverse restriction/tensor. Paste step 3 with the open-unit and counit squares,
then invert. The open coefficient comparison is the fixed simultaneous quotient map
of lem-sf-integral-open-reduction-comparison.

Step 5: for the proper/open square, the lift s into V times_Z W is clopen by
lem-sf-semilinear-proper-open-mate-pasting. The inverse open compositor is the
left-adjoint conjugate of the restriction compositor, hence a word in the structural
units, counits and pullback compositor. The restriction factor P_b J_k to J_s is
P_b of that inverse open compositor followed by the inverse open unit. It therefore
has its coefficient square.

Step 6: the first factor P_i S_p to S_q P_b is the right-adjoint conjugate of
beta inverse for the cartesian square. Expand conjugation by its two composite
adjunctions; their units and counits are composites of the primitive ones. Step 2
and the structural hypotheses give the square of this factor.

Step 7: the clopen factor J_s to S_s is the direct-image adjunction unit followed
by S_s of the inverse open unit. Thus its square follows from those two structural
squares. No arbitrary choice of a clopen isomorphism is made.

Step 8: paste steps 5--7 and the direct-image compositor S_q S_s to S_r.
This is exactly properOpenLambda and its independent ringed counterpart transported
by the canonical completion maps. All six additional systems are checked by
GeneratorKind.admissible, without a bound on their expression lengths.

Step 9: Gamma_Q is J_i of lambda inverse followed by the open counit. Invert the
lambda square and paste that counit square. All constructions are functorial in the
input complexes, so these are natural whole-system squares. No equality detection
by derived evaluations or scalar restriction is used. -/
theorem openInterchangeReductionSquares
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (o : Operations C.l E)
    (_hStructural : StructuralSquares.{u, s, i} C.l E D o)
    {S : Type s} (W : S → Scheme.{u}) (_hW : FiniteTypeFamily W D.k)
    {I : Type i} (location : I → S)
    {a : S} {B Cw : Word W location a} (g : GeneratorKind W location B Cw)
    (_hOpen : OpenGenerator g) (_hB : B.length ≤ 3) (_hC : Cw.length ≤ 3)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource C.l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (_hAdm : ∀ k : I, Admissible C.l E
      (IntegralSystemRealization.calculus C.l E (W (location k))) (K k)
      lo hi torLo torHi)
    (_hIntermediate : Word.admissible C.l E W location o K lo hi torLo torHi B ∧
      Word.admissible C.l E W location o K lo hi torLo torHi Cw)
    (_hGenerator : g.admissible C.l E W location o K lo hi torLo torHi) :
    Assertion C.l E W location o K g ∧
      (OpenIsomorphism g →
        IsIso (g.systemMap C.l E W location o (inputReduction C.l E W location K)) ∧
        IsIso (g.integralMap C.l E W location o K) ∧
        InverseAssertion C.l E W location o K g) ∧
      (∀ (L : ∀ k : I, DerivedCategory (scalarReductionSource C.l E (W (location k)))),
        (∀ k : I, Admissible C.l E
          (IntegralSystemRealization.calculus C.l E (W (location k))) (L k)
          lo hi torLo torHi) →
        Word.admissible C.l E W location o L lo hi torLo torHi B →
        Word.admissible C.l E W location o L lo hi torLo torHi Cw →
        g.admissible C.l E W location o L lo hi torLo torHi →
        ∀ f : ∀ k : I, K k ⟶ L k, SquareNaturality C.l E W location o f g) := by
  have hSquare : Assertion C.l E W location o K g := by
    cases g <;> simp only [OpenGenerator] at _hOpen
    case openBaseChange =>
      apply openBaseChangeReductionSquare C E o _hStructural W _hW location
      all_goals first | assumption | exact _hIntermediate.1 | exact _hIntermediate.2
    case openTensor =>
      apply openTensorReductionSquare C E o _hStructural W _hW location
      all_goals first | assumption | exact _hIntermediate.1 | exact _hIntermediate.2
    case properOpenLambda =>
      apply properOpenLambdaReductionSquare C E o _hStructural W _hW location
      all_goals first | assumption | exact _hIntermediate.1 | exact _hIntermediate.2
    case properOpenInterchange =>
      apply properOpenInterchangeReductionSquare C E o _hStructural W _hW location
      all_goals first | assumption | exact _hIntermediate.1 | exact _hIntermediate.2
  have cBK := completionMap_isIso C.l E W location o B _hB K
    lo hi torLo torHi _hAdm _hIntermediate.1
  have cCK := completionMap_isIso C.l E W location o Cw _hC K
    lo hi torLo torHi _hAdm _hIntermediate.2
  have := cBK
  have := cCK
  refine ⟨hSquare, ?_, ?_⟩
  · intro hg
    have hs := systemMap_isIso C.l E W location o
      (inputReduction C.l E W location K) g hg
    have hr := ringedMap_isIso C.l E W location o K g hg
    have := hs
    have := hr
    have hi : IsIso (g.integralMap C.l E W location o K) := by
      dsimp only [GeneratorKind.integralMap]
      rw [inverseOrZero_eq_inv]
      infer_instance
    have := hi
    refine ⟨hs, hi, ?_⟩
    exact inverse_square (IntegralSystemRealization.calculus C.l E (W a)).reduction
      (g.integralMap C.l E W location o K)
      (g.systemMap C.l E W location o (inputReduction C.l E W location K))
      (B.r C.l E W location o K) (Cw.r C.l E W location o K) hSquare
  · intro L hL hBL hCL _hGL f
    have cBL := completionMap_isIso C.l E W location o B _hB L
      lo hi torLo torHi hL hBL
    have := cBL
    refine ⟨?_, integralMap_naturality C.l E W location o f g _hOpen,
      systemMap_naturality C.l E W location o
        (fun k ↦ (IntegralSystemRealization.calculus C.l E (W (location k))).reduction.map
          (f k)) g _hOpen⟩
    intro V hV
    rcases hV with rfl | rfl
    · exact reduction_naturality C.l E W location o f lo hi torLo torHi _hAdm hL
        _ _hB _hIntermediate.1 hBL
    · exact reduction_naturality C.l E W location o f lo hi torLo torHi _hAdm hL
        _ _hC _hIntermediate.2 hCL

end WeilConjectures.OpenInterchangeReduction
