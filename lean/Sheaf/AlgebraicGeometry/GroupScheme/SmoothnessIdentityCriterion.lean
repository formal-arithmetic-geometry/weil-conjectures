/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.AlgebraicGeometry.ResidueField
import Sheaf.AlgebraicGeometry.FlatSmoothPointBaseChange
import Sheaf.AlgebraicGeometry.FiniteOfIsClosedOfClosedPoints
import WeilConjectures.AlgebraicGeometry.GroupScheme.Basic

/-!
# Smoothness of a flat group scheme at the identity section

Source: BLR, Néron Models, §7.1, paragraph before Theorem 5, pp.174–175,
and §10.1, Proposition 4 proof, p.291. The recorded proof is assembled from
Stacks Project, Tags 01TX, 01V5, 01V6, 02V4 and 0BA8, and the translation argument
in Groupoids, `lemma-group-scheme-field-geometrically-irreducible`.
(blueprint: lem-sfb-group-smoothness-identity-criterion).

## Main statements

* `GrpObj.smooth_fiber_iff_smooth_identity`: the fibre criterion.
* `GrpObj.smooth_identity_locus_open_and_smooth`: openness and smooth restriction.
* `GrpObj.finite_nonsmooth_identity_of_dedekind`: finitely many closed bad points.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped MonObj

namespace AlgebraicGeometry

/-- A flat locally finite type group scheme over a locally Noetherian base is smooth
at all points of a fibre if and only if it is smooth at the identity of that fibre.
Membership in the existing `smoothLocus` expresses smoothness on an open neighbourhood;
local finite presentation follows from local finite type over the locally Noetherian base.

Source: BLR §7.1, pp.174–175; Stacks Project, Tags 01TX and 02V4, and Groupoids,
`lemma-group-scheme-field-geometrically-irreducible`.
(blueprint: lem-sfb-group-smoothness-identity-criterion).

Proof:
1. By pqf-lem-lft-fp-locnoeth, the structure morphism is locally finitely presented.
   Its smooth locus W is open, and its restriction to W is smooth by
   lem-weil-pbc-smooth-local-on-source (Tags 01V5 and 01V6).
2. Fix x over s. Use lem-weil-pbc-morphism-from-spec-field to take the canonical
   residue-field-valued point of x. Base change the group diagrams to κ(x),
   producing a rational point x' and the identity e' on this group scheme.
   By lem-sfb-scheme-flat-smooth-point-base-change, smoothness at e(s) implies
   smoothness at e', without any flatness assumption on the base change.
3. By def-sc-group-scheme-translate and lem-sc-translation-automorphism,
   translation by x' identifies an open smooth neighbourhood of e' with one of x'.
   Smoothness is invariant under this isomorphism by def-sbc-smooth-morphisms.
   Apply lem-sfb-scheme-flat-smooth-point-base-change again to descend to x.
   This proves smoothness at every point of the fibre. The reverse implication
   applies the assertion to the identity point of the fibre. -/
theorem GrpObj.smooth_fiber_iff_smooth_identity
    {S : Scheme.{u}} [IsLocallyNoetherian S] (G : Over S) [GrpObj G]
    [Flat G.hom] [LocallyOfFiniteType G.hom] (s : S) :
    (∀ x : G.hom.fiber s, G.hom.fiberι s x ∈ G.hom.smoothLocus) ↔
      η[G].left s ∈ G.hom.smoothLocus := by
  sorry

/-- The base points where a flat locally finite type group scheme is smooth at its
identity form an open subset, and the group scheme restricted to that open is smooth.
No quasi-compactness, commutativity or Néron mapping property is required.

Source: BLR §7.1, pp.174–175; Stacks Project, Tags 01V5, 01V6 and 02V4.
(blueprint: lem-sfb-group-smoothness-identity-criterion).

Proof:
1. By pqf-lem-lft-fp-locnoeth, the structure morphism is locally finitely presented.
   Write W for its open smooth locus as in Tags 01V5 and 01V6, and put U=e⁻¹(W).
   Continuity of the identity section makes U open, including when U is empty.
2. The residue-field base change and translation argument of the fibre criterion
   shows that every point of the inverse image of U belongs to W.
3. By lem-weil-pbc-smooth-local-on-source, the restriction to W is smooth, as is
   its source restriction to the inverse image of U. Restricting the target to U
   leaves the same local presentations and lifting problems in
   def-sbc-smooth-morphisms. Thus the indicated restriction is smooth. -/
theorem GrpObj.smooth_identity_locus_open_and_smooth
    {S : Scheme.{u}} [IsLocallyNoetherian S] (G : Over S) [GrpObj G]
    [Flat G.hom] [LocallyOfFiniteType G.hom] :
    IsOpen {s : S | η[G].left s ∈ G.hom.smoothLocus} ∧
      Smooth (G.hom ∣_ (η[G].left ⁻¹ᵁ G.hom.smoothLocus)) := by
  sorry

/-- Over the spectrum of a Dedekind domain of dimension one, a flat locally finite type
 group scheme with smooth generic fibre has only finitely many nonsmooth base points,
 and every such point is closed. The explicit dimension equality retains the node's
 dimension-one convention, since Mathlib's Dedekind domains also include fields.

Source: BLR §10.1, Proposition 4 proof, p.291; Stacks Project, Tags 02V4 and 0BA8.
(blueprint: lem-sfb-group-smoothness-identity-criterion).

Proof:
1. Let η be the prime (0). The fibre at η is the generic fibre, equivalently the
   base change to the fraction field. By lem-sfb-scheme-flat-smooth-point-base-change,
   its smoothness at the identity descends to smoothness at e(η). Here local finite
   presentation follows from pqf-lem-lft-fp-locnoeth and Noetherianness of the base.
2. By the preceding open-locus argument, U=e⁻¹(W) is open. Its complement E is closed
   and avoids η. Every prime in E is nonzero, hence maximal: a strictly larger prime
   would give a chain (0) < p < q contradicting dimension one. Thus its points are closed.
3. The affine scheme Spec A is Noetherian because A is Noetherian. Apply
   lem-sc-noetherian-closed-points-finite to E to obtain finiteness. This uses no
   quasi-compactness assumption on G, and permits an empty complement. -/
theorem GrpObj.finite_nonsmooth_identity_of_dedekind
    (A : Type u) [CommRing A] [IsDedekindDomain A] (hdim : ringKrullDim A = 1)
    (G : Over (Spec (.of A))) [GrpObj G] [Flat G.hom] [LocallyOfFiniteType G.hom]
    [Smooth (G.hom.fiberToSpecResidueField ⟨⊥, Ideal.isPrime_bot⟩)] :
    {s : Spec (.of A) | η[G].left s ∉ G.hom.smoothLocus}.Finite ∧
      ∀ s : Spec (.of A), η[G].left s ∉ G.hom.smoothLocus →
        IsClosed ({s} : Set (Spec (.of A))) := by
  sorry

end AlgebraicGeometry
