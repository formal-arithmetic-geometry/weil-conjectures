/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.AlgebraicGeometry.EtaleFieldPointFunctor
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Geometric points of a coproduct of field spectra

Source: Stacks Project, Tags 03QR and 01JB.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] etaleFieldDiscreteForget₂ etaleFieldActionForget₂

/-- Geometric points of a prescribed coproduct of field spectra are the sum of embeddings.
Source: Stacks Project, Tag 03QR, coproduct construction; Tag 01JB, scheme coproducts.
(blueprint: lem-exc-etale-coproduct-embedding-points).

Proof: A map from Spec Ksep into the coproduct has its unique topological point in a
unique component. The coproduct inclusion of that component is an open immersion,
so the map factors uniquely through it. The Spec anti-equivalence identifies maps
from Spec Ksep to Spec (E i) over Spec K with K-algebra maps E i to Ksep. These two
constructions are inverse, giving the displayed equivalence. Precomposition by the
spectrum map of g corresponds under the anti-equivalence to postcomposition of the
embedding by g, and does not change the component. This proves the equivariance
formula. For empty I there is no map from the nonempty Spec Ksep to the empty scheme;
for a singleton I the assertion is precisely the affine anti-equivalence. -/
theorem etaleCoproduct_embedding_points
    (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
    [IsSepClosure K Ksep] (I : Type u) (E : I → IntermediateField K Ksep)
    [Etale (Sigma.desc (fun i : I ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))))] :
    let X := Scheme.Etale.mk (Sigma.desc (fun i : I ↦
      Spec.map (CommRingCat.ofHom (algebraMap K (E i)))))
    ∃ e : ((etaleFieldPointFunctor K Ksep).obj X).obj.obj.V ≃
        (Σ i, E i →ₐ[K] Ksep),
      ∀ (g : Gal(Ksep/K)) (x : ((etaleFieldPointFunctor K Ksep).obj X).obj.obj.V),
        e (((etaleFieldPointFunctor K Ksep).obj X).obj.obj.ρ g x) =
          ⟨(e x).1, g.toAlgHom.comp (e x).2⟩ := by sorry

end AlgebraicGeometry
