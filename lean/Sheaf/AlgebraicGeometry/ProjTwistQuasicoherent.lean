/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-! # Quasi-coherence of the concrete twisting sheaf

Source: Stacks Project, Constructions, Lemma 01MB and Definition 01MN.
(blueprint: lem-sfb-proj-twist-quasicoherent).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace AlgebraicGeometry.Proj

/-- Every integer twisting sheaf is quasi-coherent, without generation in degree one.

Source: Stacks Project, constructions.tex, lemma-proj-scheme (Tag 01MB),
definition-twist (Tag 01MN), and lemma-proj-sheaves (Tag 01M7).

Proof: Give the underlying ring the integer grading whose negative pieces are zero,
and shift it by j: its degree n piece is A_(j+n) when j+n is nonnegative and zero
otherwise. This is an internal graded module, since the original ring grading is
internal and shifting permutes the integer indices. Its associated module sheaf is
quasi-coherent by the graded-module sheaf construction, Tag 01MB. If one presents
the pieces as additive subgroups to apply that construction, use identity graded
ring maps between the two presentations. Their Proj maps send a prime to its inverse
image under the identity, so are mutually inverse. At corresponding primes their
maps on ordinary localizations are the identity, and the homogeneous numerator and
denominator membership conditions agree. The resulting maps on twist sections act
pointwise by these localization identities, commute with restrictions, and preserve
the structure-sheaf action because it is multiplication in the same localization.
Thus the associated sheaf and the concrete twist can be compared on the original
Proj; quasi-coherence is preserved by the displayed scheme isomorphism.

On each positive homogeneous standard open D_+(f), the single-twist fraction theorem
identifies sections of the concrete twist with the degree-zero fractions of this
shifted module: a numerator in degree j+n divided by a denominator in degree n.
These identifications are additive, bijective, and linear over the homogeneous
localization, and their restriction maps send y/f^m to a^m*y/g^(e*m) whenever
D_+(g) is contained in D_+(f) and g^e=a*f. They therefore agree with the associated
module sheaf's chart and restriction maps. The positive homogeneous standard opens
form a basis. Uniqueness of extension from that basis gives an isomorphism from
the associated sheaf to the concrete twist, and quasi-coherence transports along
it. This uses every positive degree, rather than degree one. If Proj is empty the
same basis argument is vacuous and gives the unique sheaf; negative shifts have
zero negative components and require no invertibility assumption.
(blueprint: lem-sfb-proj-twist-quasicoherent). -/
theorem isQuasicoherent_twist
    {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (j : ℤ) :
    (twist 𝒜 j).IsQuasicoherent := by sorry

end AlgebraicGeometry.Proj
