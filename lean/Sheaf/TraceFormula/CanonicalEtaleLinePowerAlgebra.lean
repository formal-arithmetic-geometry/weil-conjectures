/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q65, SHEAF group W4
-/
module

public import Sheaf.TraceFormula.EtalePowerProductNormalization

/-!
# Canonical graded algebra on powers of an étale line module

Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL;
spaces-descent.tex, Tag 0D3C, the algebra preceding psi_d
(blueprint: lem-trf-canonical-etale-line-power-algebra).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The actual tensor powers of a line module carry the canonical commutative
homogeneous products, with the structure-sheaf unit and chart normalizations.
Source: Stacks Project, sites-modules.tex, Tags 03EK and 03EL;
spaces-descent.tex, Tag 0D3C
(blueprint: lem-trf-canonical-etale-line-power-algebra).

Proof: on the small affine étale model, concatenate the actual tensor factors by
`evaluationPowerAddIso`. The sheaf tensor's universal bilinear pairing gives the
products on sections. Transport these pairings through the counit of the existing
small-site equivalence. In degree zero the canonical equivalence with the tensor
unit gives the unit morphism; it is invertible and its chart value is the identity
on regular functions. The sheaf tensor universal property gives bilinearity and
restriction compatibility. For associativity, induct on the first degree m: at m = 0 the equation is
unitor naturality, and at m + 1 the recursion for `evaluationPowerAddIso` reduces
it to the preceding case and the associator pentagon. The left unit is its zero
case; the right unit follows by induction using the triangle identity. Thus the
two composites concatenate exactly the same ordered factors.
For commutativity, restrict to a covering sieve trivializing the given line module.
In such a trivialization each tensor factor is a multiple of the same generator,
and both products multiply the same scalar coefficients in the commutative ring.
The equality descends because the target is a sheaf. This rank-one argument is
needed: powers of an arbitrary module need not be ordinarily commutative.
Finally the equivalence counit identifies these transported products and the unit
with the displayed chart formulas, including when either degree is zero. -/
theorem canonical_etale_line_power_algebra (X : AlgebraicSpace S)
    (L : X.Modules) (hL : X.IsLineModule L) :
    ∃ A : EtaleGradedModuleAlgebra (evaluationLinePower X L),
      HasCanonicalEtalePowerProducts X L A := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
