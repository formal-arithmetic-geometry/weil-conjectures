## What changed

Repaired the returned import cycle by removing the unused proof-only import
`WeilConjectures.AlgebraicGeometry.Cohomology.Projective` from the new module
`Sheaf.AlgebraicGeometry.UniformDirectImageBoundCore`. No shared Lean declaration
is needed by its current whole-proof `sorry`: the finite-support theorem is cited
only in its complete natural-language proof plan and matching DAG node. Removing
that edge breaks the cycle without changing or adapting any existing library API.
The existing finite-support result stays in its original module and the core node
continues to record it as a mathematical dependency. No statement or definition
is weakened, moved, duplicated, or replaced.

The original reduction is unchanged. Proved
`AlgebraicGeometry.exists_schemeDerivedDirectImage_uniform_truncation_bound`
by choosing N from `AlgebraicGeometry.uniform_bound_core`, taking the explicit
threshold `n₀ = N - q`, and applying
`AlgebraicGeometry.directImage_truncation_tail_bound` in degrees q and q+1.
The derived image of the standard truncation triangle is distinguished;
Mathlib's homology sequence makes its second arrow both mono and epi, hence an
isomorphism. Lean checks both integer inequalities and identifies the arrow with
the requested canonical truncation map. The original signature is unchanged.

The two new modules package strictly separate steps: the geometric upper bound
(steps 1–3) and the shift estimate for the truncation tail (part of step 4).
The tail lemma assumes a supplied bound, has no qcqs or compact-base hypotheses,
and asserts neither existence of a bound nor a truncation isomorphism.
Their sourced docstrings and nodes retain the complete natural-language arguments.

## Proved and sorry left

Proved the original module's sole sorry:
`AlgebraicGeometry.exists_schemeDerivedDirectImage_uniform_truncation_bound`.
The two split statements remain whole-proof sorries:

- `AlgebraicGeometry.uniform_bound_core`, node
  `lem-pc-uniform-direct-image-bound-core`.
- `AlgebraicGeometry.directImage_truncation_tail_bound`, node
  `lem-pc-direct-image-truncation-tail-bound`.

The tail estimate allows arbitrary integers N, n, j and requires only
`N ≤ j+n+1`; the chosen threshold need not be nonnegative. For the zero object
both statements are immediate. No axiom or hollow definition is introduced.

## No longer needed

The repair removes the unused import
`WeilConjectures.AlgebraicGeometry.Cohomology.Projective` from
`UniformDirectImageBoundCore`. It was imported to prepare for a later proof of the
finite-support step, but its declaration does not occur in the current Lean proof.
The old source result and node `lem-pc-finite-support-hi` remain necessary in the
geometric proof plan; no mathematical dependency is pruned merely to avoid a cycle.
A worker formalizing that step will need a lower-level module for the finite-support
result, since the current aggregator reaches the theorem being proved. This pending
source-library refactor is not needed by this compiling reduction.

Removed from the item's module the proof imports
`Sheaf.Algebra.Homology.KInjectiveRestrictOpen`,
`Sheaf.AlgebraicGeometry.DerivedSectionsPushforwardComparison`,
`Sheaf.AlgebraicGeometry.LerayDegenerateSections`,
`Sheaf.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound`,
`Sheaf.Paper.PQFCohomology`, and
`WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`.
They now belong to the geometric split's plan. The old direct proof dependencies
redirected to the core node are `lem-pc-finite-support-hi`,
`lem-pc-affine-vanishing`, `lem-pc-leray-degenerate-sections`,
`pqf-def-cohomology`, `lem-pc-unbounded-derived-functor-cohomological-bound`,
`lem-pc-derived-sections-pushforward-comparison`, and
`lem-sc-derived-k-injective-restrict-open`. All seven remain in its proof plan.
No source declaration or node is claimed globally unnecessary.
The item's existing public imports remain unchanged. Its private proof imports
are the two split modules and the existing triangulated right-derived-functor
module used for `map_distinguished`, plus the upstream derived-category t-structure
module used for `isIso_homologyMap_mor₂`.

The second reading also removes the six private imports listed above from
`UniformDirectImageBoundCore`, where no Lean proof currently uses them. Their
mathematical nodes remain in the core's complete sourced proof plan. This reduces
source import edges without declaring any of those nodes globally unnecessary.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery unnecessarily imported the finite-support theorem's entire
`Projective` aggregator into the core split. Its transitive imports go through
`DirectImage.Sections`, `DerivedDirectImagePreservesDirectSums`, and
`DerivedDirectImageCohomologyCoproduct` back to the original truncation module.
Single-file compilation against existing oleans did not expose this source cycle.
The repair removes the unused edge and verifies the combined source import graph
with all three sandbox modules substituted at once.

An attempted extraction of the shared finite-support declaration compiled but was
rejected by preflight because adapting `Projective` requires a separate claim.
The worker brief explicitly forbids invoking the claim tool directly, so that
attempt is not part of this delivery. Only sandbox files were changed; no claim
or project tool was bypassed. The cycle is repaired by pruning a Lean import that
has no use in the delivered proof, while preserving the mathematical dependency.

The finite-support theorem uses `Scheme.Modules`, while the derived statements
use the shared `SheafOfModules` category; transporting those presentations remains
part of the geometric glue. The affine-basis detection and restriction/truncation
glue are not themselves stated by the original prerequisites. No statement is
changed or disputed, and no unit route is bypassed. The old second-reading section
was removed because the repaired delivery must be read again independently.

## New nodes

`lem-pc-uniform-direct-image-bound-core` in
`lean/Sheaf/AlgebraicGeometry/UniformDirectImageBoundCore.lean` packages the first
three source proof steps: the uniform bound on higher direct images, affine Leray
degeneration, the unbounded sections bound, and affine-basis detection of zero
cohomology sheaves.

`lem-pc-direct-image-truncation-tail-bound` in
`lean/Sheaf/AlgebraicGeometry/DirectImageTruncationTailBound.lean` packages only
the shift-and-truncation vanishing estimate. The original target proves the
isomorphism from the resulting two vanishings by the homology sequence.
No further node or change record is added by the repair; all existing public
imports and signatures are unchanged.

## Second reading by S1

1. PASS: diffed the existing module against the repository and compared the full
   theorem signature byte for byte. All existing public imports, statements and
   definitions are unchanged. The other two delivered modules are new; neither
   changes a library API. No change record is required.
2. PASS: compiled all three modules with lcompile.py. There is one whole-proof
   sorry in each of the two reported split theorems and none in the original
   theorem. No forbidden declaration mechanism or hollow definition occurs.
   Fresh scratch copies with #print axioms for all three declarations reported
   only propext, Classical.choice, Quot.sound and sorryAx. The last is expected
   from the two open splits and the pre-existing open derived-image construction.
3. PASS: the geometric core is precisely the uniform-bound part of
   [Stacks 08D5](https://stacks.math.columbia.edu/tag/08D5), with the positive
   bound enlarged as needed; [01XJ](https://stacks.math.columbia.edu/tag/01XJ)
   supplies the base-change-uniform module bound. The tail is a strictly separate
   shift estimate conditional on any supplied bound. Checked zero objects,
   identity morphisms and a single cohomology sheaf in degree -n-1: after shifting
   by -n-1 the latter is in degree zero, and the boundary j+n+1=N is valid.
   Negative n,j,N cause no change in the argument. Neither split restates the
   original conjunction or claims the truncation isomorphism. Both have complete
   sourced proof docstrings and matching nodes. Independent LeanFinder, Loogle
   and grep searches used cohomological amplitude, shift compatibility and
   quasi-coherent truncation terminology. No existing theorem closes either
   geometric glue or quasi-coherence/shift transport immediately.
4. PASS after simplification: replaced the explicit mono/epi assembly with the
   proved upstream DerivedCategory.isIso_homologyMap_mor₂, imported privately.
   The two tail vanishings and canonical-map identification remain explicit.
   Also removed the six unused private imports from UniformDirectImageBoundCore:
   KInjectiveRestrictOpen, DerivedSectionsPushforwardComparison,
   LerayDegenerateSections, UnboundedDerivedFunctorCohomologicalBound,
   PQFCohomology and WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech.
   Its whole-proof sorry uses no declarations from those modules; their nodes
   remain in the sourced mathematical proof plan for subsequent formalization.
   The old seven proof dependencies are all accounted for under No longer needed
   as redirected to the core, not globally pruned. The unit record
   sk-thm-picard-duality has empty realized statement/step lists; no realized node
   or unit route is bypassed or altered by this reduction.
5. PASS: read all three node records; their proof_deps equal the unions of the
   step uses. The original node follows the two estimates and final triangle
   argument; its text now names the upstream packaged isomorphism lemma. New
   nodes have the required source, origin, searches, status, creation, blueprint,
   chapter/unit and Lean fields, and verbatim matching Lean signatures.

Changes by this reading: shortened the final assembly using the proved upstream
lemma; added its private import; removed six unused private imports from the
unproved core; updated the original node's proof text. Neither split was closed.
No mathematical dependency was globally pruned. The source-only import cycle
repair remains intact: no delivered module imports the Projective aggregator.
