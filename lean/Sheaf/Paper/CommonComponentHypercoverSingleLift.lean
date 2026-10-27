/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.ComponentRelativeProfiniteSite
public import Sheaf.RingTheory.StoneanCoverSecondStage
public import Sheaf.CategoryTheory.ProperFaceMatchingObject
public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-! # Lifting a Stonean hypercover over one affine base

Source: Bhatt--Scholze, Lemmas 2.2.8 and 2.4.8; Stacks, Tag 097D.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open scoped Simplicial

namespace AlgebraicGeometry.ProEtale

/-- Lift a prescribed Stonean hypercover over a single w-strictly local affine scheme.

Source: Bhatt--Scholze, Lemmas 2.2.8 and 2.4.8; Stacks, Tag 097D.
(blueprint: lem-sfb-common-component-hypercover-single-lift).

Proof: Transport the augmentation along a and apply the relative component functor
of component_relative_profinite_site to the given simplicial object. Its finite-limit
preservation transports each matching cone and its limit property. Replace the zero
matching object by the canonically isomorphic terminal scheme over T. Its preservation
of finite jointly surjective families makes every matching arrow a singleton pro-etale
cover. The relative pullback-space comparison supplies affine terms, the displayed
homeomorphisms, stalk isomorphisms, natural second coordinates, and component spaces.
In degree n apply stonean_cover_second_stage to the coordinate ring of T and S_n;
the base map is surjective because a, the affine-spectrum component identification,
and the augmentation are surjective. The canonical graph-restriction ring is
w-contractible and has closed-point space S_n. To identify the topology of the partition model,
apply clopen-restriction localization
and the finite-product spectrum isomorphism to each partition stage. Refinement sends
(x,A') to (x,A), where A contains A'. The partition-restriction theorem gives these
transition maps in a small directed diagram. The filtered-spectrum limit theorem and
the profinite partition-incidence theorem identify the limit homeomorphically with
|T| times_P S_n, over both coordinates. Equivalently, the canonical graph-restriction
model has this homeomorphism by PullbackProfinite.fiberHomeo. Both structural maps are stalkwise
isomorphisms, so lift that
homeomorphism and its inverse by existsUnique_lift_of_stalkMap_isIso. Uniqueness
makes them inverse scheme maps over T. Compose this scheme isomorphism with the
normalized partition-colimit algebra equivalence from stonean_cover_second_stage.
This gives k and the required finite-stage formula and both projection identities.
Transport w-contractibility and the closed-point homeomorphism through the comparison;
affine w-contractible pro-etale objects are weakly contractible by projectivity.
All constructions include empty spaces: the empty partition is an index, its product
is the zero ring, and every empty matching and augmentation map is surjective. -/
theorem exists_common_component_hypercover_single_lift
    (T : Scheme.{u}) [IsAffine T] [IsWStrictlyLocalRing Γ(T, ⊤)]
    {P : Profinite.{u}} (a : P ≃ₜ ConnectedComponents T)
    (S : SimplicialObject (Over P))
    (hS :
      ∃ (M : ∀ n : ℕ, Cone (S.properFaceDiagram n))
        (μ : ∀ n : ℕ, S _⦋n⦌ ⟶ (M n).pt),
        (M 0).pt = Over.mk (𝟙 P) ∧
        (∀ n : ℕ, Nonempty (IsLimit (M n))) ∧
        (∀ (n : ℕ) (b : SimplicialObject.ProperFaceCategory n),
          μ n ≫ (M n).π.app (op b) = S.map b.obj.hom.op) ∧
        (∀ n : ℕ, Function.Surjective (μ n).left) ∧
        (∀ n : ℕ, ExtremallyDisconnected (S _⦋n⦌).left) ∧
        (∀ n : ℕ, Function.Surjective (S _⦋n⦌).hom)) :
    ∃ (U : SimplicialObject T.ProEt)
      (p : ∀ n : ℕ, C((U _⦋n⦌).left, (S _⦋n⦌).left)),
      (∃ (M : ∀ n : ℕ, Cone (U.properFaceDiagram n))
          (μ : ∀ n : ℕ, U _⦋n⦌ ⟶ (M n).pt),
        (M 0).pt = Scheme.ProEt.mk (𝟙 T) ∧
        (∀ n : ℕ, Nonempty (IsLimit (M n))) ∧
        (∀ (n : ℕ) (b : SimplicialObject.ProperFaceCategory n),
          μ n ≫ (M n).π.app (op b) = U.map b.obj.hom.op) ∧
        (∀ n : ℕ, Presieve.singleton (μ n) ∈ Scheme.ProEt.precoverage T (M n).pt)) ∧
      (∀ n : ℕ, IsAffine (U _⦋n⦌).left ∧
        IsWContractibleRing Γ((U _⦋n⦌).left, ⊤) ∧
        (Scheme.ProEt.topology T).IsWeaklyContractible.{u + 1} (U _⦋n⦌)) ∧
      (∀ (m n : SimplexCategoryᵒᵖ) (f : m ⟶ n) (x : (U.obj m).left),
        p n.unop.len ((U.map f).left x) = (S.map f).left (p m.unop.len x)) ∧
      (∀ n : ℕ, (∀ x : (U _⦋n⦌).left, IsIso ((U _⦋n⦌).hom.stalkMap x)) ∧
        (∃ H : (U _⦋n⦌).left ≃ₜ
            {z : T × (S _⦋n⦌).left | ConnectedComponents.mk z.1 = a ((S _⦋n⦌).hom z.2)},
          (∀ x, (H x).val.1 = (U _⦋n⦌).hom x) ∧ (∀ x, (H x).val.2 = p n x)) ∧
        (∃ c : ConnectedComponents (U _⦋n⦌).left ≃ₜ (S _⦋n⦌).left,
          ∀ x : (U _⦋n⦌).left, c (ConnectedComponents.mk x) = p n x) ∧
        (∃ c : closedPoints (U _⦋n⦌).left ≃ₜ (S _⦋n⦌).left,
          ∀ x : closedPoints (U _⦋n⦌).left, c x = p n x.val)) ∧
      (∀ n : ℕ,
        ∃ (e : (colimit (Algebra.stoneanPartitionDiagram Γ(T, ⊤) (S _⦋n⦌).left
              (⟨fun s ↦ T.isoSpec.hom.continuous.connectedComponentsMap
                (a ((S _⦋n⦌).hom s)),
              T.isoSpec.hom.continuous.connectedComponentsMap_continuous.comp
                (a.continuous.comp (S _⦋n⦌).hom.hom.hom.continuous)⟩)) :
            CommAlgCat Γ(T, ⊤)) ≃ₐ[Γ(T, ⊤)]
            WContractification.PullbackProfinite Γ(T, ⊤) (S _⦋n⦌).left
              (⟨fun s ↦ T.isoSpec.hom.continuous.connectedComponentsMap
                (a ((S _⦋n⦌).hom s)),
              T.isoSpec.hom.continuous.connectedComponentsMap_continuous.comp
                (a.continuous.comp (S _⦋n⦌).hom.hom.hom.continuous)⟩))
          (k : (U _⦋n⦌).left ≅ Spec (.of
            (colimit (Algebra.stoneanPartitionDiagram Γ(T, ⊤) (S _⦋n⦌).left
              (⟨fun s ↦ T.isoSpec.hom.continuous.connectedComponentsMap
                (a ((S _⦋n⦌).hom s)),
              T.isoSpec.hom.continuous.connectedComponentsMap_continuous.comp
                (a.continuous.comp (S _⦋n⦌).hom.hom.hom.continuous)⟩)) : CommAlgCat Γ(T, ⊤)))),
          (∀ (Q : DiscreteQuotient (S _⦋n⦌).left) (r : Q → Γ(T, ⊤)),
            e ((colimit.ι (Algebra.stoneanPartitionDiagram Γ(T, ⊤) (S _⦋n⦌).left
                (⟨fun s ↦ T.isoSpec.hom.continuous.connectedComponentsMap
                (a ((S _⦋n⦌).hom s)),
              T.isoSpec.hom.continuous.connectedComponentsMap_continuous.comp
                (a.continuous.comp (S _⦋n⦌).hom.hom.hom.continuous)⟩)) (op Q)).hom
                  (fun b ↦ algebraMap Γ(T, ⊤) _ (r b))) =
              algebraMap (LocallyConstant (S _⦋n⦌).left Γ(T, ⊤))
                (WContractification.PullbackProfinite Γ(T, ⊤) (S _⦋n⦌).left
                  (⟨fun s ↦ T.isoSpec.hom.continuous.connectedComponentsMap
                (a ((S _⦋n⦌).hom s)),
              T.isoSpec.hom.continuous.connectedComponentsMap_continuous.comp
                (a.continuous.comp (S _⦋n⦌).hom.hom.hom.continuous)⟩))
                (LocallyConstant.comapₐ Γ(T, ⊤) ⟨Q.proj, Q.proj_continuous⟩
                  ⟨r, IsLocallyConstant.of_discrete r⟩)) ∧
          k.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤)
              (colimit (Algebra.stoneanPartitionDiagram Γ(T, ⊤) (S _⦋n⦌).left
                (⟨fun s ↦ T.isoSpec.hom.continuous.connectedComponentsMap
                (a ((S _⦋n⦌).hom s)),
              T.isoSpec.hom.continuous.connectedComponentsMap_continuous.comp
                (a.continuous.comp (S _⦋n⦌).hom.hom.hom.continuous)⟩)) : CommAlgCat Γ(T, ⊤)))) ≫
              T.isoSpec.inv = (U _⦋n⦌).hom ∧
          (∀ x : (U _⦋n⦌).left,
            WContractification.PullbackProfinite.projT Γ(T, ⊤) (S _⦋n⦌).left
              (⟨fun s ↦ T.isoSpec.hom.continuous.connectedComponentsMap
                (a ((S _⦋n⦌).hom s)),
              T.isoSpec.hom.continuous.connectedComponentsMap_continuous.comp
                (a.continuous.comp (S _⦋n⦌).hom.hom.hom.continuous)⟩)
              (Spec.map (CommRingCat.ofHom e.symm.toRingHom) (k.hom x)) = p n x)) := by sorry

end AlgebraicGeometry.ProEtale
