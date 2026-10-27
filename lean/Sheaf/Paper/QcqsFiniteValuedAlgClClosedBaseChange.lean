/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.Paper.CondensedConstantConstructibility
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Closed proper base change for finite-subextension-valued algebraic-closure coefficients

Source: blueprint, det-sf-comp-coherence-refinement.proof.md, (2), the closed-complement
calculation and coefficient devissage
(blueprint: lem-sfb-qcqs-finite-valued-algcl-closed-base-change).

This coefficient is distinct from the all-continuous norm-topological algebraic closure.
The statement is an exchange theorem on arbitrary bounded constructible finite-Tor inputs;
it has no open-support hypothesis and no localizing-closure input.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The actual closed proper exchange for the finite-subextension-valued algebraic closure.

Source: blueprint, det-sf-comp-coherence-refinement.proof.md, (2), closed-complement
proper base change, with coefficient devissage through finite rational extensions
(blueprint: lem-sfb-qcqs-finite-valued-algcl-closed-base-change).

Proof in words:
Transport first along the specified coefficient-ring isomorphism to the canonical
finite-subextension-valued ring. Restriction and extension along this isomorphism are
inverse exact equivalences; they preserve finite scalar presentations, their pulled-back
local models, cohomology bounds and Tor intervals. The geometric adjunctions transport
with their actual units and counits, so they also transport the specified exchange mate.
For the canonical ring, use qcqs integral generators: a bounded constructible finite-Tor
input is obtained by finitely many extensions and shifts of scalar extensions of integral
constructible finite-Tor objects over finite subextensions. Factor each scalar map through
its finite rational field. Integral-to-rational extension preserves constructibility and Tor
amplitude. Closed proper base change for the finite rational coefficient applies to this
object and to its closed pullback. The algebraic-closure direct-image comparison is
invertible on these bounded-below inputs, both for f and for its proper base change.
The scalar/pullback comparison is invertible. Its unit-square-counit rectangle identifies
the scalar extension of the finite-field exchange with the algebraic-closure exchange,
so the latter is invertible on every generator. Canonical derived shifts and triangulated
functors make its isomorphism locus closed under shifts and extensions. Finite integral
generation therefore proves invertibility on every input. This also covers zero objects,
empty schemes and the identity closed immersion; no descent of arbitrary morphisms to a
finite field, or equality of the two algebraic-closure coefficient topologies, is used. -/
theorem qcqs_finiteValuedAlgCl_closed_baseChange
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    {S X Y C : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (q : Y ⟶ S) [IsProper q] (f : X ⟶ Y) [IsProper f]
    (c : C ⟶ Y) [IsClosedImmersion c]
    [QuasiCompact (Scheme.Opens.ι (X := Y)
      ⟨(Set.range c)ᶜ, c.isClosedEmbedding.isClosed_range.isOpen_compl⟩)]
    (L : ConstantModelConstructibleFiniteTor Λ X) :
    IsIso ((condensedAmbientExchange Λ
      (g' := pullback.fst f c) (f' := pullback.snd f c) (f := f) (g := c)
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).app L.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
