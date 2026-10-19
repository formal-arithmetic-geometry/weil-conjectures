/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q96
-/
module

public import Sheaf.RingTheory.CotangentResolutionCoherence
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.Algebra.Homology.FlatSurjectionDerivedSelfTensor

/-!
# Vanishing of the cotangent complex of an étale ring map

Source: Stacks Project, Cotangent Complex, Tag 08R2 (lemma-when-zero), case (5)
(blueprint: lem-trf-etale-cotangent-vanishing).

The cotangent complex uses the standard polynomial resolution supplied by
`Algebra.CotangentResolution.Coherence`. The lifting hypothesis is written
explicitly as bijectivity of reduction for every square-zero ideal.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra.CotangentResolution

/-- The standard cotangent complex of an étale ring map is zero, and all its
integer-indexed cohomology objects vanish.
Source: Stacks Project, Tag 08R2 (lemma-when-zero), case (5)
(blueprint: lem-trf-etale-cotangent-vanishing).

Proof:
1. Apply `lem-trf-etale-ring-map-weakly-etale` to finite presentation and the
   square-zero lifting bijections. Both `R → C` and multiplication
   `μ : C ⊗[R] C → C` are flat.
2. Multiplication is surjective since `c ⊗ 1` maps to `c`. Apply
   `lem-trf-flat-epimorphism-derived-self-tensor` to this flat surjection to
   identify its derived self-tensor with `C[0]`. Then
   `lem-trf-derived-diagonal-cotangent-vanishing` gives `L_{C/(C ⊗[R] C)} = 0`.
3. Flatness over `R` gives `Tor_i^R(C,C) = 0` for every `i > 0`. Apply
   `lem-trf-cotangent-bootstrap` with the preceding diagonal vanishing to obtain
   `L_{C/R} = 0` in `D(C)`. The cohomology functors of
   `def-weil-abstract-derived-category` send this zero object to zero objects;
   conversely vanishing in every degree detects zero in the derived category. -/
theorem isZero_cotangentComplex_of_etale
    [∀ B : CommRingCat.{u}, HasDerivedCategory.{u + 1} (ModuleCat.{u} B)]
    (κ : Coherence.{u}) (R C : CommRingCat.{u}) [Algebra R C]
    [FinitePresentation R C]
    (hlift : ∀ (D : Type u) [CommRing D] [Algebra R D] (J : Ideal D), J ^ 2 = ⊥ →
      Function.Bijective
        ((Ideal.Quotient.mkₐ R J).comp : (C →ₐ[R] D) → C →ₐ[R] D ⧸ J)) :
    IsZero (cotangentComplex κ (Arrow.mk (CommRingCat.ofHom (algebraMap R C)))) ∧
      ∀ i : ℤ, IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} C) i).obj
        (cotangentComplex κ (Arrow.mk (CommRingCat.ofHom (algebraMap R C))))) := by
  sorry

end Algebra.CotangentResolution
