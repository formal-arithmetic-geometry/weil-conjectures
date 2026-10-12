/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations

/-! # Scalar cup products under pullback and coefficient maps

Source: Stacks Project, Cohomology, Tags 01FD, 07MB and 0FKV.
(blueprint: lem-sc-scalar-cup-pullback-coefficient-naturality).
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Cup products commute with a pullback followed by two coefficient maps.
Source: Stacks Project, Cohomology, Tags 01FD, 07MB and 0FKV;
the tensor-section computation in Step 8 of lem-sc-picard-kunneth-qcoh (Tag 0BED).
(blueprint: lem-sc-scalar-cup-pullback-coefficient-naturality).

Proof: Use the injective-resolution comparison defining scalarCohomologyExtEquiv.
Evaluation of a morphism from the structure sheaf at 1 identifies its Hom complex
with the sections complex. Restriction to k and precomposition by scalarUnitMorphism
identify this with Ext from the constant k-sheaf, so this comparison is natural in
coefficients. The scalarPullbackCoefficient is adjoint to the normalized module
pullback unit. The resolution diagram of Tag 01FD therefore computes the same
pullback as scalarCohomologyPullback. The Yoneda tensor pairing defining scalarExtCup
is represented by the signed resolution tensor pairing of Tag 07MB. Tag 0FKV
identifies that pairing with the cohomology cup product after augmentation to the
ordinary tensor. On sections, pullback of a tensor is the tensor of the pullbacks;
the tensor-pullback comparison has this normalization. Applying phi and psi gives
the tensor of their images. These equalities commute with the differentials and
augmentations, and the sign is unchanged because the degrees p and q are unchanged.
Transport the resulting equality of classes back through scalarCohomologyExtEquiv.
Naturality in coefficients identifies the final coefficient map with the recorded
derived-functor map scalarCohomologyMap, giving exactly the displayed composite.
This uses no affine-cover comparison inverse. At degree zero it is the section
tensor identity; a zero coefficient or an empty scheme gives zero on both sides.
-/
theorem scalarCup_pullback_coefficient_naturality
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (t : Y ⟶ X) (ht : t ≫ f = g) (F G : X.Modules) (F' G' : Y.Modules)
    (φ : (tensorPullback t).obj F ⟶ F') (ψ : (tensorPullback t).obj G ⟶ G')
    (p q : ℕ) (a : scalarCohomology f F p) (b : scalarCohomology f G q) :
    scalarCohomologyMap g
        (((Classical.choose (module_pullback_tensor t)) F G).hom ≫
          (@id (((tensorPullback t).obj F ⊗ (tensorPullback t).obj G) ⟶ (F' ⊗ G'))
            (φ ⊗ₘ ψ))) (p + q)
        (scalarCohomologyPullback f g t ht (@id X.Modules (F ⊗ G)) (p + q)
          (scalarCohomologyCup f F G p q a b)) =
      scalarCohomologyCup g F' G' p q
        (scalarCohomologyMap g φ p (scalarCohomologyPullback f g t ht F p a))
        (scalarCohomologyMap g ψ q (scalarCohomologyPullback f g t ht G q b)) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
