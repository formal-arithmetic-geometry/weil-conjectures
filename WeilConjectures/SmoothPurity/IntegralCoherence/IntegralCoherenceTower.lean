/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralCoherence.IntegralCoherenceData
import WeilConjectures.SmoothPurity.IntegralCoherence.IntegralStrictPullbackComparisons
import WeilConjectures.SmoothPurity.IntegralCoherence.IntegralGoodQuotientPresentation
import WeilConjectures.SmoothPurity.IntegralCoherence.IntegralStrictExpressionRealization

/-! # Strict expression models before derived inverse limit

Source: Stacks 07A4 and 0941; integral coherence, strict-model step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
attribute [local irreducible] SheafOfModules.monoidalCategory

universe t u s i j
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor MonoidalCategory
open Opposite AlgebraicGeometry
namespace WeilConjectures.IntegralCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {S : Type s} {W : S → Scheme.{t}}

private theorem normalized_of_iso {V : Scheme.{t}}
    {A B : coefficientSequenceDerived l E V} (e : A ≅ B)
    (hA : IsNormalizedCoefficientSequence l E V A) :
    IsNormalizedCoefficientSequence l E V B := by
  intro m n h P
  let F := coefficientSequenceDerivedEvaluation l E V m
  let G := coefficientSequenceDerivedEvaluation l E V n
  let U := normalizedDVRRes l E V h
  let τ := coefficientSequenceDerivedTransition l E V h
  constructor
  · intro f g hfg
    apply (cancel_epi (G.map e.hom)).1
    apply (hA h P).1
    simp only [Functor.map_comp]
    change τ.app A ≫ (G ⋙ U).map e.hom ≫ U.map f =
      τ.app A ≫ (G ⋙ U).map e.hom ≫ U.map g
    change τ.app B ≫ U.map f = τ.app B ≫ U.map g at hfg
    rw [← τ.naturality_assoc e.hom, ← τ.naturality_assoc e.hom, hfg]
  · intro f
    obtain ⟨g, hg⟩ := (hA h P).2 (F.map e.hom ≫ f)
    refine ⟨G.map e.inv ≫ g, ?_⟩
    apply (cancel_epi (F.map e.hom)).1
    rw [← Category.assoc, τ.naturality e.hom]
    simp only [Functor.comp_map, Category.assoc, Functor.map_comp]
    rw [← U.map_comp_assoc, ← G.map_comp, Iso.hom_inv_id, G.map_id, U.map_id,
      Category.id_comp]
    exact hg

private theorem realization_of_system (M : CompletedOperations.Models l E W)
    (hM : CompletedOperations.ComparisonLaws.{t, u, s, i} l E M)
    {I : Type i} {location : I → S} (N : ∀ k : I, Complex l E (W (location k)))
    (hg : ∀ {a : S} (P : CompletedOperations.Expression W location a),
      Good l E (W := W) a (value l E N P))
    (hn : ∀ {a : S} (P : CompletedOperations.Expression W location a),
      IsNormalizedCoefficientSequence l E (W a) (DerivedCategory.Q.obj (value l E N P)))
    (e : ∀ {a : S} (P : CompletedOperations.Expression W location a),
      DerivedCategory.Q.obj (value l E N P) ≅
        (CompletedOperations.systemValue l E M P).obj (fun k ↦ DerivedCategory.Q.obj (N k)))
    (hi : ∀ k : I, e (.input k) = Iso.refl _)
    (hu : ∀ a : S, e (.unit a) = (by
      with_unfolding_all exact Iso.refl (CompletedOperations.unit l E (W := W) a)))
    (ht : ∀ {a : S} (P Q : CompletedOperations.Expression W location a),
      e (.tensor P Q) =
        CoefficientTensorModels.iso
          (coefficientSequenceTopology (Scheme.ProEt.topology (W a)))
          (coefficientSequenceCommRingSheaf l E (W a)) (M.system a).closed (M.system a).models
          (value l E N P) (value l E N Q) (hg P).1 (hg Q).1 ≪≫
        (CompletedOperations.tensor l E M a).mapIso (Iso.prod (e P) (e Q)))
    (hf : ∀ {a b : S} (f : W a ⟶ W b)
      (P : CompletedOperations.Expression W location b),
      e (.pullback f P) =
        ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.app
          (value l E N P)).symm ≪≫
          (integralComparisonDerivedSequencePullback l E f).mapIso (e P))
    (hs : ∀ {a : S} {P Q : CompletedOperations.Expression W location a}
      (α : CompletedOperations.StructuralMap P Q),
      DerivedCategory.Q.map (structuralValue l E N α).hom ≫ (e Q).hom =
        (e P).hom ≫ (CompletedOperations.structuralValue l E M α
          (fun k ↦ DerivedCategory.Q.obj (N k))).hom) :
    Nonempty (Realization l E M N) := by
  let b {a : S} (P : CompletedOperations.Expression W location a) :=
    CompletedOperations.comparison l E M P (fun k ↦ DerivedCategory.Q.obj (N k))
  have hb {a : S} (P : CompletedOperations.Expression W location a) : IsIso (b P) :=
    (hM.invertible P (fun k ↦ DerivedCategory.Q.obj (N k))
      (fun k ↦ hn (.input k))).1
  let c {a : S} (P : CompletedOperations.Expression W location a) :=
    letI := hb P
    asIso (b P) ≪≫ (coefficientSequenceLimit l E (W a)).mapIso (e P).symm
  have hc {a : S} (P : CompletedOperations.Expression W location a) :
      IsIso ((M.calculus a).adjunction.counit.app
        (DerivedCategory.Q.obj (value l E N P))) := hM.counit a _ (hn P)
  let d {a : S} (P : CompletedOperations.Expression W location a) :=
    letI := hc P
    (M.calculus a).reduction.mapIso (c P) ≪≫
      asIso ((M.calculus a).adjunction.counit.app
        (DerivedCategory.Q.obj (value l E N P)))
  refine ⟨{
    good := hg
    normalized := hn
    system := e
    system_input := hi
    system_unit := hu
    system_tensor := ht
    system_pullback := hf
    structural := hs
    completed := c
    completed_normalization := ?_
    reduction := d
    reduction_normalization := ?_ }⟩
  · intro a P
    dsimp only [c, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom]
    rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  · intro a P
    rfl

private theorem reductionLaw_of_realization (M : CompletedOperations.Models l E W)
    {I : Type i} {location : I → S} {N : ∀ k : I, Complex l E (W (location k))}
    (R : Realization l E M N) : ReductionLaw l E M R := by
  intro a P Q v
  constructor
  · rw [R.reduction_normalization, R.reduction_normalization]
    dsimp only [completedArrow]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc _ (R.completed Q).inv (R.completed Q).hom,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    simpa only [Functor.comp_map, Functor.id_map, Category.assoc] using
      congrArg ((M.calculus a).reduction.map (R.completed P).hom ≫ ·)
        ((M.calculus a).adjunction.counit.naturality (DerivedCategory.Q.map v))
  · intro m n h
    exact ((coefficientSequenceDerivedTransition l E (W a) h).naturality
      (R.reduction P).hom).symm


/-- Strict integral quotient-tower coherence, with its completed-operation and finite
reduction realizations. Families only name the schemes and the three inputs: take S=Fin 3,
W=(Y,X,Z), and three inputs at Y to read the node's displayed diagrams. Finite expression
syntax permits both parenthesizations, both units, symmetries and iterated pullbacks.
The comparison data are characterized by generators and actual adjunctions, not assumed.

Source: Stacks sites-cohomology.tex, Tags 07A4 and 0941; blueprint coefficient twists
(blueprint: lem-pur-integral-coherence-tower).

Proof:
1. Form P_n,Q_n,H_n with their actual quotient maps. K-flat change of rings and
   derived change of rings identify transition adjoints with tensor association.
   The quotient unit and cocycle identities give normalized systems. The K-flat
   total tensor model and exact pro-etale constant inverse image give K-flat,
   flat-term representatives for every expression, including coefficient units.
2. Apply lem-pur-cochain-pullback-tensor-coherence to each quotient and to the
   ringed sequence site. Its insertion/contraction maps give tensor and its inverse.
   Naturality and reassociation give the two equal associativity routes, as chain maps.
3. Its signed symmetry and action-unit equations give the next three equations.
   Its composition clause uses precisely the adjunction-normalized compositor.
4. Its coefficient-change equation makes all these maps commute with every quotient.
   They are thus maps of whole strict systems, and the equations hold there before
   localization. Evaluation recovers the displayed equations at every positive level.
5. Apply the functorial strict-tower derived limit. It preserves equality and inverses.
   lem-pur-completed-operation-tower-substitution identifies every finite expression
   and structural arrow with its completed expression, by the recursive tensor and
   pullback realizations recorded here. The equations therefore become the integral
   associativity, symmetry, unit and composition equations.
6. Apply lem-coef-normalized-dvr-effectivity to the normalized expressions. Its
   natural coherent counit is invertible, and its transition squares identify reduction
   of each transported arrow with the original finite chain map, for every m>=n.
   This is ReductionLaw; no boundedness or constructibility is used.
-/
theorem integralCoherenceTower (W : S → Scheme.{t})
    (_hl : ∀ (a : S) (x : W a), IsUnit (l : (W a).residueField x)) :
    ∃ M : CompletedOperations.Models l E W,
      CompletedOperations.ComparisonLaws.{t, u, s, i} l E M ∧
      CompletedOperations.SubstitutionLaw.{t, u, s, i, j} l E M ∧
      CompletedOperations.StructuralLaw.{t, u, s, i} l E M ∧
      (∃ c : ∀ {a b : S} (f : W a ⟶ W b), PullbackComparison l E f,
        (∀ {a b : S} (f : W a ⟶ W b), Coherent l E f (c f)) ∧
        (∀ {a b d : S} (h : W d ⟶ W a) (f : W a ⟶ W b),
          CompositionLaw l E h f (c f) (c h) (c (h ≫ f)))) ∧
      (∀ (a : S) (P : CochainComplex (scalarReductionSource l E (W a)) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients
          (R := completedIntegralCommRingSheafUnrestricted l E (W a)) P)
        (_hflat : ∀ k : ℤ, SheafOfModules.IsFlatOnSite
          (J := Scheme.ProEt.topology (W a))
          (R := completedIntegralCommRingSheafUnrestricted l E (W a)) (P.X k)),
        Nonempty (QuotientPresentation l E M a P hP)) ∧
      (∀ {I : Type i} {location : I → S}
        (P : ∀ k : I, CochainComplex (scalarReductionSource l E (W (location k))) ℤ)
        (hP : ∀ k : I, CochainComplex.IsKFlatIndependentCoefficients
          (R := completedIntegralCommRingSheafUnrestricted l E (W (location k))) (P k))
        (T : ∀ k : I, QuotientPresentation l E M (location k) (P k) (hP k)),
        ∃ R : Realization l E M (fun k ↦ (T k).complex), ReductionLaw l E M R) := by
  obtain ⟨M, hc, hs, ht⟩ :=
    CompletedOperations.completedOperationTowerSubstitution.{t, u, s, i, j} l E W _hl
  refine ⟨M, hc, hs, ht, strictPullbackComparisons l E W, ?_, ?_⟩
  · intro a P hP hflat
    exact goodQuotientPresentation l E M a P hP hflat
  · intro I location P hP T
    have hn (k : I) : IsNormalizedCoefficientSequence l E (W (location k))
        (DerivedCategory.Q.obj (T k).complex) :=
      normalized_of_iso l E (T k).iso
        ((M.calculus (location k)).reduction_normalized _)
    obtain ⟨A⟩ := strictExpressionRealization l E M hc
      (fun k ↦ (T k).complex) (fun k ↦ (T k).good) hn
    obtain ⟨R⟩ := realization_of_system l E M hc _ A.good A.normalized A.system
      A.system_input A.system_unit A.system_tensor A.system_pullback A.structural
    exact ⟨R, reductionLaw_of_realization l E M R⟩

end WeilConjectures.IntegralCoherence
