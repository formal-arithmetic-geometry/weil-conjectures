/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Sheaf.RingTheory.IsStrictHenselization
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Cotangent dimension and strict henselization

Source: Stacks Project, `more-algebra.tex`, Tag 06LN and Tag 07QM
(blueprint: lem-sc-strict-henselization-cotangent-dimension).
-/

universe u

namespace Algebra

/-- A strict henselization `C` of a Noetherian local ring `R` is local, and the canonical
base-change map `(m_R/m_R²) ⊗ κ^sep → m_C/m_C²` is an isomorphism; it is written as the
canonical `C`-linear map `C ⊗[R] (m_R/m_R²) → m_C/m_C²` (the same map: `m_R` kills the source,
`m_R C = m_C`, and the residue field of `C` is `κ^sep`). In particular the cotangent-space
dimensions agree.
Source: Stacks Project, More on Algebra, Tag 06LN, using Tag 07QM.

Proof:
1. `lem-weil-pbc-strict-henselization-triples` identifies the maximal ideal of `C`
   with the extension of the maximal ideal of `R`, and its residue field with `K`.
   `lem-sc-strict-henselization-faithfully-flat` makes the structural map flat.
2. Apply `lem-weil-pbc-ideal-cotangent-flat-base-change-ring` to that flat map and
   the maximal ideal of `R`. This gives bijectivity of the canonical `C`-linear
   map from `C` tensored over `R` with the cotangent space of `R`.
3. The maximal ideals annihilate the respective cotangent spaces. Thus the map
   factors through residue-field scalar extension, giving exactly the canonical
   residue-field base-change isomorphism. The cotangent space of `R` is finite
   dimensional by Noetherianity; scalar extension and the isomorphism preserve
   this dimension, giving the final equality.
(blueprint: lem-sc-strict-henselization-cotangent-dimension). -/
theorem finrank_cotangentSpace_eq_of_isStrictHenselization
    (R K C : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K]
    [Algebra R K] [IsScalarTower R (IsLocalRing.ResidueField R) K]
    [CommRing C] [Algebra R C]
    (hC : IsStrictHenselization R K C) :
    ∃ _ : IsLocalRing C,
      (∃ h : IsLocalRing.maximalIdeal R ≤
          (IsLocalRing.maximalIdeal C).comap (algebraMap R C),
        Function.Bijective (LinearMap.liftBaseChange C
          (Ideal.mapCotangent (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal C)
            (Algebra.ofId R C) h))) ∧
        Module.finrank (IsLocalRing.ResidueField R)
            (IsLocalRing.CotangentSpace R) =
          Module.finrank (IsLocalRing.ResidueField C)
            (IsLocalRing.CotangentSpace C) := by
  sorry

end Algebra
