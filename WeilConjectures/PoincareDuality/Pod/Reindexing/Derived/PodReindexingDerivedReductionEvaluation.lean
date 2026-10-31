/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedCoreData
public import Mathlib.CategoryTheory.Adjunction.Opposites
public import WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower

/-! Reduction evaluation law for raw derived comparison data.

The proof constructs the corresponding normalized comparison law from the strict
quotient, evaluation, and Roos-limit calculations.  This is a strictly smaller
obligation than the assembled five-law package.
(blueprint: lem-pod-reindexing-derived-core-reduction-evaluation) -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
  (SY : PodSignedRoosShift (scalarReductionSource l E Y))
  (SX : PodSignedRoosShift (scalarReductionSource l E X))

private theorem restrictionSquare
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    (F : A ⥤ C) (G : B ⥤ D) [F.IsEquivalence] [G.IsEquivalence]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (φ : L ⋙ G ≅ F ⋙ L') :
    ∃ ψ : R ⋙ F ≅ G ⋙ R', ∀ K,
      F.map (adj.unit.app K) ≫ ψ.hom.app (L.obj K) =
        adj'.unit.app (F.obj K) ≫ R'.map (φ.inv.app K) := by
  obtain ⟨e, he⟩ := adjointSquare G.op F.op adj.op adj'.op (NatIso.op φ).symm
  let ψ : R ⋙ F ≅ G ⋙ R' := NatIso.removeOp e
  have hc (N : B) : L'.map (ψ.hom.app N) ≫ adj'.counit.app (G.obj N) =
      φ.inv.app (R.obj N) ≫ G.map (adj.counit.app N) := by
    exact congrArg Quiver.Hom.unop (he (op N))
  refine ⟨ψ, ?_⟩
  intro K
  apply (adj'.homEquiv _ _).symm.injective
  rw [adj'.homEquiv_naturality_left_symm, Adjunction.homEquiv_counit]
  have hn := φ.inv.naturality (adj.unit.app K)
  change L'.map (F.map (adj.unit.app K)) ≫ φ.inv.app (R.obj (L.obj K)) =
    φ.inv.app K ≫ G.map (L.map (adj.unit.app K)) at hn
  rw [hc, ← Category.assoc, hn, Category.assoc, ← G.map_comp,
    adj.left_triangle_components, G.map_id]
  erw [Category.comp_id]
  exact ((adj'.homEquiv _ _).symm_apply_apply (φ.inv.app K)).symm

private theorem evaluationOfUnits
    {A A' B B' C C' : Type*}
    [Category* A] [Category* A'] [Category* B] [Category* B']
    [Category* C] [Category* C']
    (L : A ⥤ B) (R : B ⥤ A) (L' : A' ⥤ B') (R' : B' ⥤ A')
    (E : A ⥤ C) (U : C ⥤ A) (E' : A' ⥤ C') (U' : C' ⥤ A')
    (V : B ⥤ C) (V' : B' ⥤ C') (F : A ⥤ A') (G : B ⥤ B') (H : C ⥤ C')
    (adj : L ⊣ R) (adj' : L' ⊣ R') (a : E ⊣ U) (a' : E' ⊣ U')
    (ρ : L ⋙ V ≅ E) (ρ' : L' ⋙ V' ≅ E')
    (π : R ⟶ V ⋙ U) (π' : R' ⟶ V' ⋙ U')
    (α : L ⋙ G ≅ F ⋙ L') (γ : R ⋙ F ≅ G ⋙ R')
    (δ : G ⋙ V' ≅ V ⋙ H) (φ : E ⋙ H ≅ F ⋙ E') (ψ : U ⋙ F ≅ H ⋙ U')
    (hρ : ∀ K, adj.unit.app K ≫ π.app (L.obj K) =
      a.unit.app K ≫ U.map (ρ.inv.app K))
    (hρ' : ∀ K, adj'.unit.app K ≫ π'.app (L'.obj K) =
      a'.unit.app K ≫ U'.map (ρ'.inv.app K))
    (hφ : ∀ K, F.map (a.unit.app K) ≫ ψ.hom.app (E.obj K) =
      a'.unit.app (F.obj K) ≫ U'.map (φ.inv.app K))
    (hu : ∀ K, F.map (adj.unit.app K) ≫ γ.hom.app (L.obj K) ≫
      R'.map (α.hom.app K) = adj'.unit.app (F.obj K))
    (hp : ∀ N, F.map (π.app N) ≫ ψ.hom.app (V.obj N) =
      γ.hom.app N ≫ π'.app (G.obj N) ≫ U'.map (δ.hom.app N)) (K : A) :
    V'.map (α.hom.app K) ≫ ρ'.hom.app (F.obj K) =
      δ.hom.app (L.obj K) ≫ H.map (ρ.hom.app K) ≫ φ.hom.app K := by
  have hα : adj'.unit.app (F.obj K) ≫ R'.map (α.inv.app K) =
      F.map (adj.unit.app K) ≫ γ.hom.app (L.obj K) := by
    rw [← hu K]
    simp only [Category.assoc, ← R'.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hp' : γ.hom.app (L.obj K) ≫ π'.app (G.obj (L.obj K)) =
      F.map (π.app (L.obj K)) ≫ ψ.hom.app (V.obj (L.obj K)) ≫
        U'.map (δ.inv.app (L.obj K)) := by
    rw [← Category.assoc, hp]
    simp only [Category.assoc, ← U'.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have hi : ρ'.inv.app (F.obj K) ≫ V'.map (α.inv.app K) =
      φ.inv.app K ≫ H.map (ρ.inv.app K) ≫ δ.inv.app (L.obj K) := by
    apply (a'.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit, U'.map_comp]
    calc
      _ = (adj'.unit.app (F.obj K) ≫ π'.app (L'.obj (F.obj K))) ≫
          U'.map (V'.map (α.inv.app K)) := by
        rw [hρ']; exact (Category.assoc _ _ _).symm
      _ = (adj'.unit.app (F.obj K) ≫ R'.map (α.inv.app K)) ≫
          π'.app (G.obj (L.obj K)) := by
        have hn := π'.naturality (α.inv.app K)
        change R'.map (α.inv.app K) ≫ π'.app (G.obj (L.obj K)) =
          π'.app (L'.obj (F.obj K)) ≫ U'.map (V'.map (α.inv.app K)) at hn
        rw [Category.assoc, Category.assoc, hn]
      _ = (F.map (adj.unit.app K) ≫ γ.hom.app (L.obj K)) ≫
          π'.app (G.obj (L.obj K)) := by rw [hα]
      _ = F.map (adj.unit.app K) ≫ F.map (π.app (L.obj K)) ≫
          ψ.hom.app (V.obj (L.obj K)) ≫ U'.map (δ.inv.app (L.obj K)) := by
        rw [Category.assoc, hp']
      _ = F.map (a.unit.app K) ≫ F.map (U.map (ρ.inv.app K)) ≫
          ψ.hom.app (V.obj (L.obj K)) ≫ U'.map (δ.inv.app (L.obj K)) := by
        rw [← Category.assoc, ← Category.assoc, ← F.map_comp, hρ K, F.map_comp]
        simp only [Category.assoc]
      _ = (F.map (a.unit.app K) ≫ ψ.hom.app (E.obj K)) ≫
          U'.map (H.map (ρ.inv.app K)) ≫ U'.map (δ.inv.app (L.obj K)) := by
        simpa only [Functor.comp_obj, Functor.comp_map, Category.assoc] using
          congrArg (fun f ↦ F.map (a.unit.app K) ≫ f ≫
            U'.map (δ.inv.app (L.obj K))) (ψ.hom.naturality (ρ.inv.app K))
      _ = _ := by rw [hφ K]; simp only [Category.assoc]
  apply eq_of_inv_eq_inv
  simpa only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app,
    Category.assoc] using hi

/-- Reduction evaluation from the finite adjoint mate.

Source: the strict quotient, evaluation, and Roos-limit descent calculation
from the proof of lem-pod-reindexing-derived-comparisons-core.  The statement
constructs the finite restriction mate and derives one conjunct of the assembled
core package from its unit and projection conjuncts. The finite comparison itself
is preserved, so the generator-normalized finite-model law remains applicable.
(blueprint: lem-pod-reindexing-derived-core-reduction-evaluation) -/
theorem podReindexingDerivedCoreData_reductionEvaluation
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (S : PodReindexingStrictData l E g) (hS : S.Laws l E g SY SX)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n
          ((isoReductionIntegralComplex l E g).obj P))
    (hβ : podReindexingCoreQuotientGenerators l E g β)
    (htransition : podReindexingCoreQuotientTransition l E g β)
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X)
    (Q : PodReindexingDerivedCoreData l E g) :
    ∃ ψ : ∀ n : ℕ, coefficientFiniteDerivedRestriction l E Y n ⋙
        podOrdinaryReindex l E g ≅
      isoReductionFiniteDerived l E g n ⋙ coefficientFiniteDerivedRestriction l E X n,
      let Q' : PodReindexingDerivedCoreData l E g := { Q with restriction := ψ }
      PodCompletionReindex.Unit l E g (Q'.assemble l E g SY SX S β CY CX) →
      PodCompletionReindex.LimitProjection l E g (Q'.assemble l E g SY SX S β CY CX) →
      PodCompletionReindex.ReductionEvaluation l E g
        (Q'.assemble l E g SY SX S β CY CX) := by
  classical
  have _ := hS
  have _ := hβ
  have _ := htransition
  have : (isoReductionIntegralInverse l E g).IsEquivalence :=
    isoReduction_equivalence g (isoReductionCompletedMap l E g).hom
  have : (podOrdinaryReindex l E g).IsEquivalence :=
    Functor.isEquivalence_mapDerivedCategory (isoReductionIntegralInverse l E g)
  have hG (n : ℕ) : (isoReductionFiniteDerived l E g n).IsEquivalence := by
    have : (isoReductionFiniteInverse l E g n).IsEquivalence :=
      isoReduction_equivalence g (isoSectionwiseConstantMap g (CommRingCat.of
        (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
    exact Functor.isEquivalence_mapDerivedCategory (isoReductionFiniteInverse l E g n)
  have h (n : ℕ) := restrictionSquare (podOrdinaryReindex l E g)
    (isoReductionFiniteDerived l E g n) (coefficientFiniteAdjunction l E Y n)
      (coefficientFiniteAdjunction l E X n) (Q.finite n)
  choose ψ hψ using h
  refine ⟨ψ, ?_⟩
  dsimp only
  intro hu hp K n
  exact evaluationOfUnits _ _ _ _ _ _ _ _ _ _ _ _ _
    (podReindexCalculus l E Y).adjunction (podReindexCalculus l E X).adjunction
    (coefficientFiniteAdjunction l E Y n) (coefficientFiniteAdjunction l E X n)
    ((podReindexCalculus l E Y).reductionEvaluation n)
    ((podReindexCalculus l E X).reductionEvaluation n)
    (coefficientSequenceProjection l E Y n) (coefficientSequenceProjection l E X n)
    Q.reduction Q.limit (Q.evaluation n) (Q.finite n) (ψ n)
    (fun K ↦ (podReindexCalculus l E Y).unit_projection K n)
    (fun K ↦ (podReindexCalculus l E X).unit_projection K n)
    (hψ n) hu (fun N ↦ hp N n) K

end WeilConjectures
