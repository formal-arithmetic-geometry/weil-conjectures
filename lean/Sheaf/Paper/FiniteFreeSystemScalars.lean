/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.Paper.FiniteFreeSystemRestrictionData

/-! # Finite free scalar normalization on strict systems

Source: finite-free restriction proof Steps 2--5; Stacks 03CY, 03EK, 06YY and 07A6
(blueprint: lem-coef-finite-free-system-scalars).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale.SemilinearProperOpen
open WeilConjectures.SemilinearSections
namespace WeilConjectures.FiniteFreeSystemRestriction

variable (l : ℕ) [Fact l.Prime]
  (E L : Type (u + 1)) [Field E] [Field L]
  [Algebra ℚ_[l] E] [Algebra ℚ_[l] L]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] L]
  (i : E →ₐ[ℚ_[l]] L)

/-- A compatible finite basis gives the normalized exact scalar calculus on one site.
Source: lem-coef-finite-free-system-restriction, proof Steps 2--5; Stacks 03CY,
03EK, 06YY and 07A6 (blueprint: lem-coef-finite-free-system-scalars).

Proof: use semilinearDerivedSections to obtain the lower and upper system calculi.
The displayed quotient bases commute with transitions, since the same integral
sections b are used at every level. They identify the restricted coefficient system
with d copies of the lower unit. For every m >= n, ordinary tensor reduction of
this presentation is the corresponding presentation at n; its generators are free,
so it also computes derived reduction. This proves Normalized for the specified
transition adjuncts. Each level is a constant finite free module over the finite
ring A_n: the one-stratum constructibility criterion applies, and tensor is a finite
sum of identity functors, giving Tor amplitude [0,0]. This includes the empty site.
Apply the ordinary sheaf-ring coefficient adjunction on the sequence site and
finiteFreeScalarExtension to this free presentation. Restriction is exact and its
composite with extension is d copies of the identity, so extension is exact.
The canonical cochain change-of-rings model and derived coefficient adjunction
supply ScalarData with the required unit and transpose formulas. Exact extension
computes on every complex, by the uniqueness of its derived functor. Finally the
exact left scalar adjoint makes restriction preserve K-injectives: maps from an
acyclic complex to the restriction transpose to maps from its acyclic extension.
No choice of unrelated finite-level bases or uniform cohomological bound occurs. -/
theorem scalarAssertions_of_reducedBasis
    (d : ℕ) (b : Fin d → Padic.coefficientExtensionIntegers l L)
    (hb : ∀ n : ℕ, Function.Bijective
      (fun a : Fin d → A l E n ↦ ∑ j,
        (levelMap l E L i n).hom (a j) *
          Ideal.Quotient.mk ((Ideal.span {integralScalarIntegerInclusion l E L i
            (Padic.coefficientExtensionUniformizer l E)}) ^ (n + 1)) (b j)))
    (X : Scheme.{u}) : Nonempty (ScalarAssertions l E L i X) := by sorry

end WeilConjectures.FiniteFreeSystemRestriction
