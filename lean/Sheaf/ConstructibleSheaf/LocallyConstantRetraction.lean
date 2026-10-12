/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber
public import WeilConjectures.ConstructibleSheaf.Defs
import Sheaf.AlgebraicGeometry.FiniteEtaleTrace
import Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Finite étale trace splitting

Source: Stacks Project, etale-cohomology.tex, Section 03SH (section-trace-method),
Definition 03SE (definition-trace-map).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Etale

/-- **The adjunction unit splits for a prime-to-ℓ finite étale cover.**
The coefficient field is `ULift.{u + 1} (ZMod ℓ)`, a universe lift of the prime field
`ℤ/ℓℤ`.

Source: Stacks Project, `etale-cohomology.tex`, Section 03SH (`section-trace-method`),
the characterization and restriction/trace composite immediately after Definition 03SE
(`definition-trace-map`).
(blueprint: split-locally-constant-retraction)

Proof: Finite étale covers split étale locally as finite disjoint unions of copies of the
base. At a geometric point the number of summands is the cardinality of the geometric
fibre, hence d by the hypothesis. On a split cover the unit sends a section to the diagonal
d-tuple, and the trace sums its entries. These maps are coefficient-linear. The trace is
unchanged by a permutation of the summands, so the local trace maps agree on overlaps
and glue to a morphism v_*v*G ⟶ G of coefficient-module sheaves. The composite of the unit
and trace is multiplication by d on every splitting neighbourhood, hence globally by
sheaf separatedness. Since ℓ is prime and does not divide d, the scalar d is nonzero and
invertible in ℤ/ℓℤ and in its universe lift. Multiply the trace by its inverse to obtain r.
Coefficient-linearity gives unit ≫ r = d⁻¹d times the identity, which is the identity.
This construction applies also to the zero sheaf and to the degree-one cover. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_retraction
    {U V : Scheme.{u}} [IrreducibleSpace U] (ℓ : ℕ) [Fact ℓ.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))))
    [IsFiniteLocallyConstantSheaf G] (v : V ⟶ U) [IsFinite v] [Etale v]
    [ConnectedSpace V] (d : ℕ) (hd : ¬ ℓ ∣ d)
    (hdeg : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U),
      Nat.card (v.GeometricFiber s) = d) :
    ∃ r : (v)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj
          ((v)^*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))].obj G) ⟶ G,
        (Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) v).unit.app G ≫ r = 𝟙 G := by
  sorry

end AlgebraicGeometry
