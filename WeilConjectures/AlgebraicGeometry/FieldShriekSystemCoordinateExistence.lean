/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldShriekSystemEvaluation
import WeilConjectures.AlgebraicGeometry.ScalarDataExistence
import WeilConjectures.AlgebraicGeometry.ScalarEvaluationTransposeExistence
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Normalized scalar evaluation at a finite level -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u c v r
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.FieldShriekSystem

private theorem mate_of_transpose
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (a : L ⊣ R) (b : L' ⊣ R')
    (i : L ⋙ H ≅ G ⋙ L') (j : R ⋙ G ≅ H ⋙ R')
    (h : ∀ M N (f : L.obj M ⟶ N),
      G.map ((a.homEquiv _ _) f) ≫ j.hom.app N =
        (b.homEquiv _ _) (i.inv.app M ≫ H.map f)) :
    (mateEquiv a b i.inv).natTrans = j.hom := by
  ext N
  have hh := h (R.obj N) N (a.counit.app N)
  simp only [Adjunction.homEquiv_unit, Adjunction.right_triangle_components,
    G.map_id, Category.id_comp, R'.map_comp] at hh
  simpa [mateEquiv] using hh.symm

private theorem uniqueness_transpose
    {A B : Type*} [Category A] [Category B]
    {L L' : A ⥤ B} {R : B ⥤ A} (a : L ⊣ R) (b : L' ⊣ R)
    {M : A} {N : B} (f : L.obj M ⟶ N) :
    (b.homEquiv _ _) ((a.leftAdjointUniq b).inv.app M ≫ f) =
      (a.homEquiv _ _) f := by
  rw [Adjunction.homEquiv_unit, R.map_comp, ← Category.assoc]
  rw [Adjunction.leftAdjointUniq_inv_app, Adjunction.unit_leftAdjointUniq_hom_app]
  rfl

set_option maxHeartbeats 800000 in
-- Elaborating the normalized derived adjunction square compares large functor types.
private theorem scalar_evaluation_transport
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    (J : GrothendieckTopology C)
    (B F : ℕ → Sheaf J CommRingCat.{max c v r})
    (τ : ∀ n, B (n + 1) ⟶ B n) (σ : ∀ n, F (n + 1) ⟶ F n)
    (α : ∀ n, B n ⟶ F n) (hα : ∀ n, α (n + 1) ≫ σ n = τ n ≫ α n)
    (S : SemilinearSections.ScalarData.{c, v, max c v r}
      (SemilinearSections.systemMap J B τ F σ α hα))
    (levels : ∀ n, SemilinearSections.ScalarData.{c, v, max c v r} (α n))
    (q : SemilinearSections.ScalarEvaluationData.{c, v, r} J B τ F σ α hα S levels)
    (n : ℕ) (ψ : B n ⟶ F n) (hψ : α n = ψ)
    (L : SemilinearSections.D.{c, v, max c v r} J (B n) ⥤
      SemilinearSections.D.{c, v, max c v r} J (F n))
    (adj : L ⊣ SemilinearSections.resD.{c, v, max c v r} ψ) :
    ∃ (δ : SemilinearSections.res (SemilinearSections.systemMap J B τ F σ α hα) ⋙
        SemilinearSections.evaluation J B τ n ≅
      SemilinearSections.evaluation J F σ n ⋙ SemilinearSections.res ψ)
      (i : S.T ⋙ SemilinearSections.e J F σ n ≅
        SemilinearSections.e J B τ n ⋙ L),
      (∀ (M : SemilinearSections.Systems J F σ) (U : Cᵒᵖ),
        HEq (fun x ↦ ((δ.hom.app M).val.app U) x)
          (fun x : M.val.obj (Opposite.op (n, U.unop)) ↦ x)) ∧
      (mateEquiv S.adjunction adj i.inv).natTrans =
        (Functor.mapDerivedCategorySquareIso δ).hom := by
  subst ψ
  let δ := (SemilinearSections.restrictionEvaluation_existsUnique
    J B τ F σ α hα n).exists.choose
  let e := (levels n).adjunction.leftAdjointUniq adj
  let i := q.evaluation n ≪≫ Functor.isoWhiskerLeft (SemilinearSections.e J B τ n) e
  refine ⟨δ, i, (SemilinearSections.restrictionEvaluation_existsUnique
    J B τ F σ α hα n).exists.choose_spec, ?_⟩
  apply mate_of_transpose
  intro M N f
  rw [show i.inv.app M = e.inv.app _ ≫ (q.evaluation n).inv.app M from rfl]
  rw [Category.assoc, uniqueness_transpose]
  exact q.transpose_evaluation n M N f

set_option maxHeartbeats 4000000 in
-- Normalize the finite scalar adjunction without expanding its construction.
/-- The actual scalar extension has a level comparison normalized by its restriction mate.

Source: latest blueprint, field-extension towers proof (2), finite scalar evaluation
(blueprint: lem-route-field-shriek-system-coordinates).

Proof: use the section-identity restriction evaluation isomorphism for the ringed
sequence site. The tower_app equation identifies its finite coefficient map with the
constant sheaf map of the quotient inclusion. Localize this exact square to obtain the
right-hand derived restriction comparison. Take the inverse mate under the whole-system
scalar adjunction and the finite derived extension adjunction. On flat-term K-flat
resolutions its ordinary tensor comparison evaluates to the identical pure tensor.
Hence the inverse mate is invertible on each such resolution, and therefore on every
object of the unbounded derived category. Its inverse defines the scalar evaluation
isomorphism. The two mate operations are inverse equivalences, giving the transpose
normalization. Ordinary section carriers are unchanged by both restriction routes,
which gives the sections field. -/
theorem field_shriek_scalar_evaluation_exists (P : PurityFiniteSetting.{u})
    (D : Models P) {E F : Index P} (h : E ≤ F) (T : Scheme.{u}) (n : ℕ) :
    Nonempty (ScalarEvaluation P D h T n) := by
  classical
  let J := Scheme.ProEt.topology T
  let B := SpTowerShriek.B P.coefficients.l E.val T
  let F' := SpTowerShriek.B P.coefficients.l F.val T
  let t := SpTowerShriek.tau P.coefficients.l E.val T
  let s := SpTowerShriek.tau P.coefficients.l F.val T
  let a := D.coefficients E F h
  let α := fun n ↦ (a.tower T).app (Opposite.op n)
  have hα : ∀ n, α (n + 1) ≫ s n = t n ≫ α n :=
    fun n ↦ ((a.tower T).naturality (homOfLE (Nat.le_succ n)).op).symm
  let levels := fun n ↦
    ((SemilinearSections.semilinearScalarData.{u + 1, u, u + 1} J B t F' s α hα).2 n).some
  let S := D.scalars E F h T
  obtain ⟨q⟩ := SemilinearSections.semilinearScalarEvaluationTranspose.{u + 1, u, u + 1}
    J B t F' s α hα S levels
  have ha : α n = proEtaleConstantRingMap (T := T) (a.quotient n) :=
    a.tower_app T n
  obtain ⟨δ, i, hδ, hi⟩ := scalar_evaluation_transport.{u + 1, u, u + 1}
    J B F' t s α hα S levels q n _ ha
    (scalarExtensionFunctor (a.quotient n) T) (finiteScalarAdjunction (a.quotient n) T)
  let r : RestrictionEvaluation P D h T n :=
    { ordinary := δ
      sections := fun M U x ↦ heq_of_eq (congrFun (eq_of_heq (hδ M U)) x) }
  refine ⟨{ restriction := r, iso := i, transpose := ?_ }⟩
  unfold AdjunctionEvaluationNormalized restrictionEvaluation
  exact hi

end AlgebraicGeometry.ProEtale.FieldShriekSystem
