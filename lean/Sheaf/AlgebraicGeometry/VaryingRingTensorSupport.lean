/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingOperations

/-! # Tensor support for extension of varying-ring systems

Source: Stacks Project, Tag 0E8I, and Tags 06YS and 06YU.
(blueprint: lem-pur-varying-ring-tensor-support).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open WeilConjectures WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.VaryingRing

/-- The image of extension by zero is a tensor ideal for the actual K-flat
modeled tensor on the vertical sequence site. Only essential-image membership
is asserted; this does not choose or normalize a projection morphism.

Source: Stacks Project, sites-modules.tex Tag 0E8I; sites-cohomology.tex
Tags 06YS and 06YU; Zheng, Construction 4.1 and Lemma 4.10.
(blueprint: lem-pur-varying-ring-tensor-support).

Proof: identify the constant coefficient tower on U with restriction of the
tower on X along open composition. The constant-section universal property
identifies the ring maps, including the horizontal transitions. The induced
module-category equivalence identifies canonical extension with the normalized
restricted-ring extension by uniqueness of adjoints. Derive these exact
functors termwise. The tensor representative comparisons identify A.tensor
with the normalized ambient tensor: both are the localization of the same
total tensor on flat-term K-flat complexes, so two-variable localization
uniqueness supplies their natural comparison. Apply derivedTensor_openSupported
in that restricted-ring presentation, and transport its essential-image witness
through these equivalences. This proves support without choosing a projection
morphism, including for the empty open and for nonflat coefficient transitions. -/
theorem tensor_openSupported
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (A : SemilinearSections.Closed.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (systemRing (Scheme.ProEt.topology X) (coefficients R X) (coefficientTransition R φ X)))
    (T : SemilinearSections.Models.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (systemRing (Scheme.ProEt.topology X) (coefficients R X) (coefficientTransition R φ X)) A)
    (M : Derived R φ U) (N : Derived R φ X) :
    (J R φ j).essImage (A.tensor.obj ((J R φ j).obj M, N)) := by
  sorry

end AlgebraicGeometry.ProEtale.VaryingRing
