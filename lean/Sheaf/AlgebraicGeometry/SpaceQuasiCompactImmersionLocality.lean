/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFppfCoveringCalculus
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.QuasiCompactImmersionAffineDescent
import Sheaf.AlgebraicGeometry.SpaceQuasiAffineAffineDescent
import Sheaf.AlgebraicGeometry.SpaceQuasiCompactAffineTests
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoproduct
import Sheaf.AlgebraicGeometry.FppfSheafCoproductPartition
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Fppf locality of quasi-compact immersions of algebraic spaces

Source: Stacks Project, Spaces Descent, Tag 0424,
lemma-descending-property-quasi-compact-immersion, specialized to fppf coverings
(blueprint: lem-sfb-space-quasi-compact-immersion-locality).

The scheme-test predicate includes representability by schemes in its conclusion.
The covering members are arbitrary algebraic spaces, not necessarily schemes or
representable over the target. The pullback projection is the actual presheaf pullback;
sheaf inclusion preserves this fibre product.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A space morphism is a quasi-compact immersion precisely when it becomes one over
all members of an fppf covering of its target. In particular scheme representability
is descended, rather than assumed. The scheme immersion predicate means a closed
immersion followed by an open immersion (`IsImmersion.isImmersion_iff_exists`).
Source: Stacks Project, Spaces Descent, Tag 0424
(blueprint: lem-sfb-space-quasi-compact-immersion-locality).

Proof, following the five steps of the accepted split:
1. Set P to quasi-compact immersion. The immersion and quasi-compact affine tests
   [lem-sfb-space-immersion-affine-tests, lem-sfb-space-quasicompact-affine-tests]
   give base-change stability and hypothesis (2) of the fpqc affine criterion
   [lem-sfb-space-fpqc-property-affine-criterion]. For hypothesis (1), form finite
   coproducts [lem-trf-algebraic-space-coproduct]. A scheme mapping into the target
   coproduct partitions into clopen pieces [lem-trf-fppf-sheaf-coproduct-partition].
   On each piece the pullback is an immersion, hence so is the whole map by the
   immersion criterion. For an affine test, its clopen pieces are quasi-compact;
   the pullback pieces are quasi-compact and their finite union is quasi-compact.
   The empty coproduct is an empty isomorphism. All objects obey
   [def-weil-size-convention].
2. For hypothesis (3), let V → U be flat surjective between affine schemes, and let
   X → U become a quasi-compact immersion over V. Its pullback X_V is a scheme.
   Factor X_V → V as open then closed
   [lem-pqf-qc-immersion-open-closed-factor]. The intermediate scheme is affine
   [lem-weil-pbc-closed-immersion-affine-cover-criterion]. Also X_V is quasi-compact
   [lem-weil-pbc-quasi-compact-morphism-preimage-qc-open,
   lem-weil-pbc-affine-scheme-qcqs]. Thus X_V is a quasi-compact open in an affine
   scheme, hence quasi-affine.
3. Apply [lem-sfb-space-quasi-affine-affine-descent] to obtain scheme
   representability of X. Now [lem-sfb-scheme-qc-immersion-fpqc-descent] applies to
   the same square and descends quasi-compactness and immersion. This verifies
   hypothesis (3) without assuming representability downstairs. The source's
   sentence saying "closed immersion" at this step is a typo: the conclusion
   used and proved there is "quasi-compact immersion".
4. Apply [lem-sfb-space-fpqc-property-affine-criterion] to the isomorphism-invariant
   property P with the three hypotheses just verified. This gives fpqc locality.
5. The given fppf family is fpqc. After scheme pullback choose étale scheme charts
   and use [lem-trf-fppf-covering-is-fpqc]; on each affine test the finite flat
   affine refinements give the required fpqc refinements. Step 4 therefore gives
   descent along this family. The forward implication is also immediate from
   base-change stability in step 1. An empty covering forces the target empty;
   the source is then empty and the conclusion is the empty isomorphism. -/
theorem quasiCompactImmersion_iff_fppfCover
    {S : Scheme.{u}} {I : Type w} {Z T : AlgebraicSpace S}
    (h : Z ⟶ T) (Tᵢ : I → AlgebraicSpace S) (q : ∀ i : I, Tᵢ i ⟶ T)
    (hq : IsFppfCover q) :
    IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left ∧ IsImmersion p.left)
      h.hom.hom ↔
      ∀ i : I,
        IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left ∧ IsImmersion p.left)
          (Limits.pullback.snd h.hom.hom (q i).hom.hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
