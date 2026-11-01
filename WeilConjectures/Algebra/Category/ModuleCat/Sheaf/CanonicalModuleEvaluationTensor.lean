/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.CategoryTheory.Sites.FiniteDisjointCover
import WeilConjectures.ZetaWeil.PartitionTensorSections
import WeilConjectures.CategoryTheory.Sites.IsDisjointCover.DisjointSheafSections
import all WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # The canonical tensor comparison for module evaluation

Source: Stacks Project, Tag 03EK; monoidal sheafification and its right adjoint.
(blueprint: lem-zl-canonical-module-evaluation-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe c v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped TensorProduct
namespace SheafOfModules

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r}) (U : Cᵒᵖ)

attribute [local instance 2000] cochainModulesMonoidal cochainModulesSymmetric

/-- The sectionwise tensor maps to the sheaf tensor by the sheafification unit.
Source: Stacks Project, Tag 03EK
(blueprint: lem-zl-canonical-module-evaluation-tensor). -/
def evaluationTensorComparison
    (M N : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :
    ModuleCat.of (R.obj.obj U) (M.val.obj U ⊗[R.obj.obj U] N.val.obj U) ⟶
      (evaluation.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) U).obj (M ⊗
          N) :=
  (((PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙 _)).unit.app
      (M.val ⊗ N.val)) ≫ (tensorObjIsoSheafification M N).inv.val).app U

@[instance_reducible]
private def presheafEvaluationMonoidal :
    (PresheafOfModules.evaluation.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj U).Monoidal
        :=
  (show (PresheafOfModules.evaluation.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj
        U).CoreMonoidal from
    { εIso := Iso.refl _
      μIso := fun _ _ ↦ Iso.refl _
      μIso_hom_natural_left := by intros; simp; rfl
      μIso_hom_natural_right := by intros; simp; rfl
      associativity := by intros; simp; rfl
      left_unitality := by intros; simp; rfl
      right_unitality := by intros; simp; rfl }).toMonoidal

/-- The canonical tensor comparison is invertible at an object with finite
partition refinements.

Source: Stacks Project, Tags 03EK and 0F63
(blueprint: lem-zl-canonical-module-evaluation-tensor).

Proof: the sheafification unit followed by a sheaf isomorphism is locally
bijective. Refine the local equality sieve to a finite disjoint cover; injectivity
of raw tensor restriction proves global injectivity. Refine the local image
sieve similarly; bijectivity of raw tensor restriction glues its local lifts.
Naturality and separatedness of the target prove their image is the given
section. This includes the empty partition. -/
theorem evaluationTensorComparison_isIso_of_finiteDisjointRefinements
    (hU : J.HasFiniteDisjointRefinements U.unop)
    (M N : SheafOfModules.{max c v r}
      ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) :
    IsIso (evaluationTensorComparison.{c, v, r} J R U M N) := by
  classical
  let A := ((sheafCompose J
    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let q : M.val ⊗ N.val ⟶ (M ⊗ N).val :=
    (PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙 A.obj)).unit.app
      (M.val ⊗ N.val) ≫ (tensorObjIsoSheafification M N).inv.val
  let φ := (PresheafOfModules.toPresheaf A.obj).map q
  have : Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf A.obj).map
        ((PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙 A.obj)).unit.app
          (M.val ⊗ N.val))) := by
    change Presheaf.IsLocallyInjective J
      (CategoryTheory.toSheafify J (M.val ⊗ N.val).presheaf)
    infer_instance
  have : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf A.obj).map
        ((PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙 A.obj)).unit.app
          (M.val ⊗ N.val))) := by
    change Presheaf.IsLocallySurjective J
      (CategoryTheory.toSheafify J (M.val ⊗ N.val).presheaf)
    infer_instance
  have : IsIso ((PresheafOfModules.toPresheaf A.obj).map
      (tensorObjIsoSheafification M N).inv.val) :=
    inferInstanceAs (IsIso ((forget A ⋙ PresheafOfModules.toPresheaf A.obj).map
      (tensorObjIsoSheafification M N).inv))
  have : Presheaf.IsLocallyInjective J φ := by
    dsimp only [φ, q]
    rw [Functor.map_comp]
    infer_instance
  have : Presheaf.IsLocallySurjective J φ := by
    dsimp only [φ, q]
    rw [Functor.map_comp]
    infer_instance
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y h
    obtain ⟨n, Y, f, hf, hmem⟩ := hU _
      (Presheaf.equalizerSieve_mem J φ x y h)
    apply (tensorSections_bijective_of_disjointCover.{c, v, r} R hf M N).injective
    funext i
    exact hmem i
  · intro y
    obtain ⟨n, Y, f, hf, hmem⟩ := hU _ (Presheaf.imageSieve_mem J φ y)
    choose t ht using hmem
    obtain ⟨x, hx⟩ :=
      (tensorSections_bijective_of_disjointCover.{c, v, r} R hf M N).surjective t
    refine ⟨x, ?_⟩
    let F := (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max c v r})).obj
      ((toSheaf A).obj (M ⊗ N))
    apply GrothendieckTopology.IsDisjointCover.type_ext hf F
    intro i
    change (M ⊗ N).val.map (f i).op (q.app U x) = (M ⊗ N).val.map (f i).op y
    rw [← PresheafOfModules.naturality_apply q]
    exact (congrArg (q.app (op (Y i))) (congrFun hx i)).trans (ht i)

/-- Invertible canonical tensor comparisons make module evaluation strong braided,
with the actual sheafification tensorator and identity coefficient-unit map.

Source: Stacks Project, Tag 03EK
(blueprint: lem-zl-canonical-module-evaluation-tensor).

Proof: pointwise evaluation of module presheaves is strictly braided monoidal.
The forgetful functor from module sheaves is lax braided, as the right adjoint
of braided monoidal sheafification. Compose them. Its tensorator is the unit
of sheafification followed by the inverse tensor comparison; its unit is the
identity by the adjunction triangle identity at the coefficient module.
The assumed invertibility of the tensorators therefore makes this lax braided
functor strong. -/
theorem evaluation_braided_of_isIso_tensorComparison
    (h : ∀ M N, IsIso (evaluationTensorComparison.{c, v, r} J R U M N)) :
    ∃ m : (evaluation.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) U).Braided,
      let := m
      (∀ M N, Functor.LaxMonoidal.μ (evaluation.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) U) M N =
        evaluationTensorComparison.{c, v, r} J R U M N) ∧
      Functor.LaxMonoidal.ε (evaluation.{max c v r}
        ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R) U) =
          𝟙 _ := by
  let A := ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)
  let : CommRing (A.obj.obj U) := inferInstanceAs (CommRing (R.obj.obj U))
  let E := PresheafOfModules.evaluation.{max c v r} A.obj U
  let F := forget A
  let := presheafEvaluationMonoidal.{c, v, r} J R U
  let : E.Braided :=
    { braided := by
        intro M N
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro x y
        rfl }
  let := LineEvaluation.forgetLax.{c, v, r} R
  let : F.LaxBraided :=
    { braided := (LineEvaluation.adj.{c, v, r} R).rightAdjointLaxMonoidal_μ_comp_map_braiding }
  let G := F ⋙ E
  let : G.LaxBraided := inferInstanceAs (F ⋙ E).LaxBraided
  have hμ (M N) : Functor.LaxMonoidal.μ G M N =
      evaluationTensorComparison.{c, v, r} J R U M N := by
    change 𝟙 _ ≫ _ = _
    rw [Category.id_comp]
    exact congrArg (fun f ↦ f.app U) (LineEvaluation.forget_mu.{c, v, r} R M N)
  have hε : Functor.LaxMonoidal.ε G = 𝟙 _ := by
    change 𝟙 _ ≫ _ = _
    rw [Category.id_comp]
    exact congrArg (fun f ↦ f.app U) (LineEvaluation.forget_epsilon.{c, v, r} R)
  have : IsIso (Functor.LaxMonoidal.ε G) := by rw [hε]; infer_instance
  have hμiso (M N) : IsIso (Functor.LaxMonoidal.μ G M N) := by rw [hμ]; exact h M N
  let : ∀ M N, IsIso (Functor.LaxMonoidal.μ G M N) := hμiso
  let : G.Monoidal := .ofLaxMonoidal G
  let b : G.Braided :=
    { toMonoidal := inferInstance
      braided := Functor.LaxBraided.braided (F := G) }
  exact ⟨b, hμ, hε⟩

end SheafOfModules
