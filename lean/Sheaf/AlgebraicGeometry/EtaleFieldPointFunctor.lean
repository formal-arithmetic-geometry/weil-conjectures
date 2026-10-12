/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.AlgebraicGeometry.EtaleFieldGeometricAction
import Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Sheaf.FieldTheory.EtaleFieldGaloisClassification

/-!
# The geometric-point functor for étale schemes over a field

Source: Stacks Project, Tag 03QR.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] etaleFieldDiscreteForget₂ etaleFieldActionForget₂

variable (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep]
  [IsSepClosure K Ksep]

/-- The continuous discrete action on the geometric points of an étale scheme. -/
noncomputable def etaleFieldPointObject
    (X : Scheme.Etale (Spec (CommRingCat.of K))) :
    DiscreteContAction (Type u) (Gal(Ksep/K)) :=
  ⟨⟨etaleFieldGeometricAction K Ksep X,
    etaleFieldGeometricAction_continuous K Ksep X⟩, by
      change DiscreteTopology (TopCat.discrete.obj (etaleFieldGeometricAction K Ksep X).V)
      infer_instance⟩

/-- Geometric points, with their Galois action; maps act by postcomposition. -/
noncomputable def etaleFieldPointFunctor :
    Scheme.Etale (Spec (CommRingCat.of K)) ⥤
      DiscreteContAction (Type u) (Gal(Ksep/K)) where
  obj := etaleFieldPointObject K Ksep
  map f := ⟨⟨
    { hom := ↾(fun x ↦ x ≫ (Scheme.Etale.forget _).map f)
      comm := by
        intro g
        apply ConcreteCategory.hom_ext
        intro x
        change (etaleFieldPointAutomorphism K Ksep g ≫ x) ≫
          (Scheme.Etale.forget _).map f =
            etaleFieldPointAutomorphism K Ksep g ≫ (x ≫ (Scheme.Etale.forget _).map f)
        exact Category.assoc _ _ _ }⟩⟩
  map_id X := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ConcreteCategory.hom_ext
    intro x
    change x ≫ (Scheme.Etale.forget _).map (𝟙 X) = x
    simp
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply ConcreteCategory.hom_ext
    intro x
    change x ≫ (Scheme.Etale.forget _).map (f ≫ g) =
      (x ≫ (Scheme.Etale.forget _).map f) ≫ (Scheme.Etale.forget _).map g
    simp

/-- The geometric-point functor is full and faithful.
Source: Stacks Project, Tag 03QR, the equivalence assertion
(blueprint: lem-exc-etale-field-point-functor-fully-faithful).

Proof: By Morphisms, Tag 02GL, an étale K-scheme is the disjoint union of spectra of
finite separable extensions. On a component Spec L its geometric points are the
K-embeddings L → Ksep, a nonempty finite transitive Galois set. An equivariant map
from such a transitive set lands in one target orbit. The finite Galois classification
identifies maps between these orbits with unique K-morphisms of the corresponding
spectra. The coproduct universal property assembles these maps, proving fullness.
Uniqueness on every component proves faithfulness. The empty source has a unique map;
a nonempty source cannot map to the empty target on either side of the correspondence. -/
theorem etaleFieldPointFunctor_fullyFaithful :
    (etaleFieldPointFunctor K Ksep).Full ∧ (etaleFieldPointFunctor K Ksep).Faithful := by
  sorry

end AlgebraicGeometry
