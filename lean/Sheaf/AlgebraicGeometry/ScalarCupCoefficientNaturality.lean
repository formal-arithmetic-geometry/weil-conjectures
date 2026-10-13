/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # ScalarCupCoefficientNaturality

Source: Stacks Project, Cohomology, Tags 01F7, 07MB and 0FKV.
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Cup products are natural in two coefficient morphisms on a fixed scheme.
Source: Stacks Project, Cohomology, Tags 07MB and 0FKV; Tag 01F7 for coefficient maps.
(blueprint: lem-sc-scalar-cup-coefficient-naturality).

Proof: Choose injective resolutions of the four coefficient modules and comparison
chain maps lifting phi and psi. Evaluation at 1 intertwines a comparison chain map
with the global-sections map, since an O-linear map sends the image of 1 to the
image of that section. Thus the moduleExtEquiv comparison intertwines the recorded
right-derived-functor coefficient map with postcomposition in Ext. Restriction to
k and precomposition by scalarUnitMorphism preserve this equality by associativity
of Yoneda composition, giving the same assertion for scalarCohomologyExtEquiv.
For the tensor coefficient, both orders send s tensor t to phi(s) tensor psi(t).
The tensor universal property and sheafification adjunction make this an equality
of sheaf morphisms. Apply this square to the tensor pairing of resolution complexes:
comparison chain maps have degree zero, so the signs of Tag 07MB agree in both
orders. Tag 0FKV identifies its augmentation with the ordinary coefficient tensor
map and the derived cup product. Equivalently, associativity and naturality of
Yoneda composition identify postcomposition of scalarExtCup with the cup of the
two postcompositions. Compose with scalarTensorCoefficient, use its square, and
transport through the injective scalarCohomologyExtEquiv. The comparison with the
recorded coefficient maps proved above gives the displayed equality. No acyclic
cover or quasi-coherence assumption is used. In degree zero this is precisely the
pure-tensor identity; if a morphism or a coefficient is zero both sides are zero.
-/
theorem scalarCup_coefficient_naturality
    (k : Type w) [Field k] (X : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (F G F' G' : X.Modules)
    (φ : F ⟶ F') (ψ : G ⟶ G') (p q : ℕ)
    (a : scalarCohomology f F p) (b : scalarCohomology f G q) :
    scalarCohomologyMap f (@id ((F ⊗ G) ⟶ (F' ⊗ G')) (φ ⊗ₘ ψ)) 
        (p + q) (scalarCohomologyCup f F G p q a b) =
      scalarCohomologyCup f F' G' p q
        (scalarCohomologyMap f φ p a) (scalarCohomologyMap f ψ q b) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
