## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.EtaleLimitCohomologyBinaryGluing`
with a complete Lean proof, preserving its signature and visibility. The proof opens
`EtaleCohomologyStageContinuity.holds`, uses existing
`AlgebraicGeometry.Etale.etale_limit_cohomology_class_descent` for representatives,
and uses the new kernel-only theorem
`AlgebraicGeometry.Etale.etale_limit_binary_eventual_zero` for eventual killing.
It proves injectivity of `colimit.desc H B` by representing a colimit element,
using the coprojection identity, killing its representative at a later stage,
and applying cocone naturality. Existing class descent proves surjectivity.
`ConcreteCategory.isIso_iff_bijective` then makes the comparison an isomorphism;
`Cocone.ext` and `IsColimit.ofIsoColimit` transport the actual colimit structure.

Added `Sheaf.AlgebraicGeometry.EtaleLimitBinaryEventualZero`, one public named
kernel theorem with a complete source-based proof in words, and its DAG node.
Updated the original node's proof, proof dependencies and proof origin to match
this assembly. All work is below the unit level; neither `sk-thm-p1` nor any of
its realized statement or step nodes was bypassed or changed. No definitions,
existing signatures, public imports, or other modules were changed.

Both delivered modules compile cleanly together through the required lcompile
wrapper. The new theorem has the same universe and supplied system data as the
original predicate, including all coherence equations and comparison legs.
The ambient scheme has no qcqs assumption. On an actual union stage, its qcqs
hypotheses make the overlap compact, so the restricted-system argument applies.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.etale_limit_cohomology_binary_gluing`
(node `lem-weil-pbc-etale-limit-cohomology-binary-gluing`). No sorry remains in
the item's module.

Added and left: `AlgebraicGeometry.Etale.etale_limit_binary_eventual_zero`
(node `lem-weil-pbc-etale-limit-binary-eventual-zero`). Its whole proof is
`:= by sorry`, in its own new module. This is a decomposition, not a completed
axiom-free proof: one upper hole closed and one kernel hole added (net zero).
Existing class descent and its dependencies are used unchanged.

The new statement only detects zero at a later stage; it asserts neither
representatives of arbitrary limit classes nor a colimit universal property.
These are supplied separately and combined in real Lean in the item's module.
In general group diagrams kernel detection does not imply surjectivity (for a
singleton diagram, an injective proper inclusion has kernel detection but is
not a colimit cocone). Thus this is a strict part of the argument, not the
original continuity property under another name. Edge cases checked in words:
zero classes use identity transitions; empty opens give the other-open or zero
case; repeated opens give diagonal restriction and the difference map; degree
zero uses the initial injective restriction; singleton systems use the supplied
scheme and coefficient identifications. No data is chosen from an unproved
mere-existence theorem.

## No longer needed

Removed these six direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`
- `Sheaf.AlgebraicGeometry.EtaleMayerVietoris`
- `Sheaf.AlgebraicGeometry.EtaleMayerVietorisPullback`
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

Added only the proof imports of class descent, the new kernel theorem, and
`Mathlib.Algebra.Category.Grp.FilteredColimits`.

The original direct DAG dependencies for pullback functoriality, cofinal tails,
restricted limits, inverse-image restriction/composition, left-adjoint colimit
preservation, Mayer-Vietoris and its pullback compatibility, filtered exactness,
and scheme conventions move to the kernel node. They are still needed there,
so no whole-library pruning of those modules is claimed. The full five-lemma
node `lem-weil-pbc-five-lemma` is no longer needed by this route: the new kernel
node gives the elementary injective half of the exact-sequence chase explicitly.
`def-weil-pbc-category-colimit` is retained by the assembly. No other existing
nodes or modules are declared unnecessary.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped without implementing a reduction. Its uncompiled
`EtaleLimitCohomologyBinaryGluingHolds` helper also gave the complete original
statement with the structure field expanded, which would merely relocate the
hole. Removed that helper from the deliverable and replaced it with kernel
detection only. The missing comparison ladder is real work, but it can be
stated as the strictly smaller kernel theorem and does not block delivery.

A shorter route was available for the other half: the existing general
class-descent declaration fits the supplied interface exactly and does not
import binary gluing. The general eventual-vanishing theorem would be circular:
it imports qcqs gluing, which imports this item, and was not used. The full
five-lemma assembly can consequently be replaced by an elementwise kernel and
surjectivity argument. No mathematical error in the original statement was found.

Read the local Stacks source at Tag 09YQ (`theorem-colimit`) and Tag 0A50
(`lemma-mayer-vietoris`). Tag 09YQ proves continuity by affine sites; the finite
open-cover reduction here is explicitly agent-written, as in the original node.
The original Mayer-Vietoris and pullback interfaces were read before writing
the kernel node. LeanFinder found structure-sheaf section vanishing lemmas,
not this arbitrary-coefficient cohomology statement; grep found no exact match;
LeanSearch returned HTTP 500 and is recorded as unavailable. Blueprint searches
for binary gluing and eventual zero found no matching imported blueprint node.

## New nodes

`lem-weil-pbc-etale-limit-binary-eventual-zero` in
`dag/nodes/sec-proper-base-change/` states finite-stage kernel detection for a
specified union stage with continuity on the two compact opens and their
intersection. Its module is
`lean/Sheaf/AlgebraicGeometry/EtaleLimitBinaryEventualZero.lean`. Its proof
separates restriction of systems, the natural exact-sequence ladder, the
injective diagram chase (with a separate degree-zero case), and finite-stage
zero detection in the filtered group colimit. It contains all the quantified
system data and cites the existing dependencies rather than copying their
statements. No change record is needed because no existing interface changes.

## Second reading by W3

1. Compared the delivered gluing module with the repository version. The target
   signature and all existing declaration signatures are unchanged; only proof
   imports and proof bodies differ, and the added module is recorded by its new
   node. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`. They compile with
   no errors. The sole remaining `sorry` is the named split theorem
   `etale_limit_binary_eventual_zero`; it has a complete source-based docstring
   and matching DAG node. No forbidden declarations or hollow definitions occur.
   Verdict: pass, with one documented split-off hole.
3. The split theorem is a strict kernel-detection statement: it does not restate
   binary gluing, and its edge cases reduce to the claimed zero-transition
   behavior. The statement and node agree exactly. Verdict: pass.
4. The proof uses class descent and kernel detection, then the filtered-colimit
   element argument; it does not bypass the realized unit route. Direct imports
   no longer used by the assembly were removed and listed above. Verdict: pass.
5. The DAG proof steps, dependencies, origin, and new node metadata match the
   Lean proof and its imports. Verdict: pass.

Changed during second reading: no Lean declarations or statements; added this
review record only.
