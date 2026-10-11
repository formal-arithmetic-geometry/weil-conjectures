/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# Automorphisms of a set-valued functor

Source: Stacks Project, Lemma 58.3.1 (Tag 0BMR)
(blueprint: lem-galois-aut-profinite).
-/

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
          TotallyDisconnectedSpace (Aut F) ∧ IsTopologicalGroup (Aut F)) := by sorry

end SetFunctorAut
end CategoryTheory
