/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# Automorphisms of a set-valued functor

Source: Stacks Project, Lemma 58.3.1 (Tag 0BMR)
(blueprint: lem-galois-aut-profinite).
-/

@[expose] public section

universe u v w

namespace CategoryTheory
namespace SetFunctorAut

open Topology

/-- The pointwise convergence topology on permutations of a discrete set.
Source: Stacks Project, Tag 0BMR (blueprint: lem-galois-aut-profinite). -/
@[instance_reducible]
def fiberTopology (A : Type w) : TopologicalSpace (Aut A) :=
  letI : TopologicalSpace A := ⊥
  TopologicalSpace.induced (fun σ : Aut A => (σ.hom : A → A)) inferInstance

/-- The pointwise topology on permutations of a discrete set.
Source: Stacks Project, Section 58.3 (Tag 0BMQ) (blueprint: lem-galois-aut-profinite). -/
instance fiberTopologyInstance (A : Type w) : TopologicalSpace (Aut A) := fiberTopology A

/-- Evaluation of a natural automorphism on every object.
Source: Stacks Project, equation (58.3.0.1) (blueprint: lem-galois-aut-profinite). -/
def evaluation {C : Type u} [Category.{v} C] (F : C ⥤ Type w) :
    Aut F →* ∀ X : C, Aut (F.obj X) :=
  MonoidHom.mk' (fun σ X => σ.app X) (fun _ _ => rfl)

/-- The topology induced by evaluation into the product of pointwise permutation groups.
Source: Stacks Project, Tag 0BMR (blueprint: lem-galois-aut-profinite). -/
@[instance_reducible]
def functorTopology {C : Type u} [Category.{v} C] (F : C ⥤ Type w) :
    TopologicalSpace (Aut F) :=
  letI (X : C) : TopologicalSpace (Aut (F.obj X)) := fiberTopology (F.obj X)
  TopologicalSpace.induced (evaluation F) inferInstance

/-- The subspace topology from componentwise evaluation.
Source: Stacks Project, Section 58.3 (Tag 0BMQ) (blueprint: lem-galois-aut-profinite). -/
instance functorTopologyInstance {C : Type u} [Category.{v} C] (F : C ⥤ Type w) :
    TopologicalSpace (Aut F) := functorTopology F

private theorem evaluation_injective {C : Type u} [Category.{v} C]
    (F : C ⥤ Type w) : Function.Injective (evaluation F) := by
  intro σ τ h
  ext X x
  have hx : σ.app X = τ.app X := congr_fun h X
  rw [← Iso.app_hom, ← Iso.app_hom, hx]

private theorem evaluation_range {C : Type u} [Category.{v} C] (F : C ⥤ Type w) :
    Set.range (evaluation F) =
      ⋂ (f : Arrow C), ⋂ (x : F.obj f.left),
        {a | F.map f.hom ((a f.left).hom x) = (a f.right).hom (F.map f.hom x)} := by
  ext a
  simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨σ, rfl⟩ f x
    exact (ConcreteCategory.congr_hom (σ.hom.naturality f.hom) x).symm
  · intro h
    refine ⟨NatIso.ofComponents a (fun {X Y} f ↦ ?_), rfl⟩
    ext x
    exact (h ⟨X, Y, f⟩ x).symm

private theorem fiber_hom_continuous (A : Type w) :
    letI : TopologicalSpace A := ⊥
    Continuous (fun σ : Aut A ↦ (σ.hom : A → A)) := by
  let : TopologicalSpace A := ⊥
  exact continuous_induced_dom

private theorem evaluation_range_closed {C : Type u} [Category.{v} C]
    (F : C ⥤ Type w) : IsClosed (Set.range (evaluation F)) := by
  rw [evaluation_range]
  apply isClosed_iInter
  intro f
  apply isClosed_iInter
  intro x
  let : TopologicalSpace (F.obj f.left) := ⊥
  let : DiscreteTopology (F.obj f.left) := ⟨rfl⟩
  let : TopologicalSpace (F.obj f.right) := ⊥
  let : DiscreteTopology (F.obj f.right) := ⟨rfl⟩
  apply isClosed_eq
  · exact continuous_of_discreteTopology.comp
      ((continuous_apply x).comp
        ((fiber_hom_continuous _).comp (continuous_apply f.left)))
  · exact (continuous_apply (F.map f.hom x)).comp
      ((fiber_hom_continuous _).comp (continuous_apply f.right))

/-- Evaluation is an injective group homomorphism because natural transformations are
determined by their components. A family of bijections lies in its image exactly when
it commutes with every arrow; its componentwise inverse then gives the inverse natural
transformation. Outside the image, an arrow and point violating naturality give two
pointwise-open conditions whose intersection misses the image, even when the source
and target objects coincide. Thus the image is closed. With finite fibres the
permutation groups are finite and discrete; the closed subgroup theorem for their
product (blueprint: lem-galois-closed-subgroup-product-finite-groups) makes `Aut F`
profinite with its induced topology.
Source: Stacks Project, Lemma 58.3.1 (Tag 0BMR)
(blueprint: lem-galois-aut-profinite). -/
theorem evaluation_isClosedEmbedding_and_profinite
    {C : Type u} [Category.{v} C] (F : C ⥤ Type w) :
    IsClosedEmbedding (evaluation F) ∧
      ((∀ X : C, Finite (F.obj X)) →
        CompactSpace (Aut F) ∧ T2Space (Aut F) ∧
          TotallyDisconnectedSpace (Aut F) ∧ IsTopologicalGroup (Aut F)) := by
  have he : IsClosedEmbedding (evaluation F) :=
    { eq_induced := rfl
      injective := evaluation_injective F
      isClosed_range := evaluation_range_closed F }
  refine ⟨he, ?_⟩
  intro hfinite
  have (X : C) : Finite (F.obj X) := hfinite X
  have (X : C) : Finite (Aut (F.obj X)) :=
    Finite.of_injective (fun σ ↦ (σ.hom : F.obj X → F.obj X)) (by
      intro σ τ h
      exact Iso.ext (ConcreteCategory.hom_ext _ _ (congr_fun h)))
  have (X : C) : DiscreteTopology (Aut (F.obj X)) := by
    let : TopologicalSpace (F.obj X) := ⊥
    let : DiscreteTopology (F.obj X) := ⟨rfl⟩
    exact (show IsEmbedding (fun σ : Aut (F.obj X) ↦
        (σ.hom : F.obj X → F.obj X)) from
      { eq_induced := rfl
        injective := fun σ τ h ↦
          Iso.ext (ConcreteCategory.hom_ext _ _ (congr_fun h)) }).discreteTopology
  have : CompactSpace (Aut F) := he.compactSpace
  have : T2Space (Aut F) :=
    T2Space.of_injective_continuous he.injective he.continuous
  have : TotallyDisconnectedSpace (Aut F) :=
    he.isEmbedding.isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  have : ContinuousMul (Aut F) := he.isInducing.continuousMul (evaluation F)
  have : ContinuousInv (Aut F) := he.isInducing.continuousInv fun _ ↦ rfl
  exact ⟨inferInstance, inferInstance, inferInstance, ⟨⟩⟩

end SetFunctorAut
end CategoryTheory
