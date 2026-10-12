## What changed

Proved the unchanged `AlgebraicGeometry.uniform_bound_core` signature in
`Sheaf.AlgebraicGeometry.UniformDirectImageBoundCore` from the existing proved
unbounded-functor bound and one new ordinary module-section bound. Applied the
unbounded theorem on X to Γ(f⁻¹U,-), rather than restricting E to an open derived
category. Countable-product preservation is inferred from the actual section
functor. The positive natural bound is cast to an integer, and `omega` checks
both its positivity and the strict inequality N-1<m.

Added `Sheaf.AlgebraicGeometry.DirectImageHomologyAffineDetection`, with a complete
proof for arbitrary derived objects, arbitrary morphisms, and every integer degree.
Its private proved helper transports homology through exact evaluations and stalks.
Every stalk of the section-homology presheaf has an affine representative; zero
section homology therefore gives zero stalks of the cohomology sheaf. Faithfulness
of forgetting module structure reflects zero identities. K-injective computation
connects this complex argument to derived direct image.

Added `Sheaf.AlgebraicGeometry.UniformInverseAffineSectionsBound`, containing the
remaining ordinary module-section theorem with its source and full proof in words.
Updated the core's DAG proof and dependencies and added the two corresponding nodes.
No existing signature, definition, public import, or visibility changed.

All three modules compile cleanly together through lcompile.py. The detection
statement was tested by its proof on arbitrary integer degrees and without qcqs,
quasi-coherence, or boundedness assumptions; no nonempty assumption occurs.
The remaining module bound has N>0: empty opens, empty schemes and zero modules
satisfy it trivially; the identity of an affine scheme allows N=1. No separatedness
assumption replaces quasi-separatedness, and S need not be quasi-separated.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.uniform_bound_core`
(node `lem-pc-uniform-direct-image-bound-core`): 1 of 1 original holes closed.
This is a decomposition, not a sorry-free proof: one new lower hole was added.

Also proved `AlgebraicGeometry.isZero_schemeHigherDirectImage_of_affine_sections`
(node `lem-pc-direct-image-homology-affine-detection`) and its private helper
`homology_zero_of_affine_sections`, with no direct sorry.

The only sorry left in the delivered modules is
`AlgebraicGeometry.exists_uniform_inverse_affine_sections_bound`
(node `lem-pc-uniform-inverse-affine-sections-bound`). This concerns only ordinary
quasi-coherent modules and natural-number right derived section functors. It has
no unbounded derived object, support hypothesis, or derived direct-image conclusion.
The original module contains no sorry. Existing imported theorems and instance
proofs can still depend transitively on sorry; this delivery does not claim that
the target's full axiom closure is finished. Holes closed minus holes added is zero.

## No longer needed

Removed these proof imports from the original core module:

- `Sheaf.Algebra.Homology.KInjectiveRestrictOpen`
- `Sheaf.AlgebraicGeometry.DerivedSectionsPushforwardComparison`
- `Sheaf.AlgebraicGeometry.LerayDegenerateSections`
- `Sheaf.Paper.PQFCohomology`
- `WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech`

The core's former proof dependencies `lem-sc-derived-k-injective-restrict-open`
and `lem-pc-derived-sections-pushforward-comparison` are unnecessary for the entire
new route: direct sections on X and the termwise K-injective computation replace
restriction and comparison through the open subschemes.

The core no longer directly uses `lem-pc-finite-support-hi`,
`lem-pc-affine-vanishing`, `lem-pc-leray-degenerate-sections`,
`pqf-def-cohomology`, or `def-pc-derived-direct-image` as proof steps.
Finite support, affine vanishing and Leray remain in the natural-language proof
of the ordinary bound, so they are not declared mathematically unnecessary.
Cohomology is expressed directly as right derived open sections, rather than
through the additional PQFCohomology comparison. SchemeDerivedDirectImage remains
publicly imported because the original statement needs it. The general unbounded
bound remains a proof import. No unit statement or realized unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The declared `lem-pc-finite-support-hi` lives in
`WeilConjectures.AlgebraicGeometry.Cohomology.Projective`. The import-direction
check reports that Projective already reaches UniformDirectImageBoundCore; importing
it here would close a cycle. In addition, the upstream affine section comparison
in DirectImage.Sections assumes `IsSeparated f`, which cannot be inferred from
this item's `QuasiSeparated f`. Its module also reaches the present item.
Thus the planned use of these declarations cannot directly supply the ordinary
bound here. The new ordinary section-bound item preserves exactly the actual
mathematical hypotheses and states the strictly smaller remaining step.

Stacks Tags 08D5, 01XJ and 08D4 were read directly online. Tag 08D5 applies the
unbounded theorem to Γ(f⁻¹U,-) on X, precisely the implementation used here.
Mathlib search found no direct uniform bound or derived-image detection theorem.
LeanSearch returned Internal Server Error and is recorded as unavailable, never
as a negative result. LeanFinder, Loogle and grep were run through msearch.py;
local source searches found the exact-functor, stalk and K-injective interfaces
used in the completed proof. No source statement was disputed or changed.

The blueprint ancestor command returned None for this generated core node because
its immediate from.node is another generated node. The new nodes trace through
DerivedDirectImageUniformTruncationBound and ProperUpperShriekComposition to the
existing blueprint ancestor `lem-sc-finite-duality`, preserving the original route.
The associated unit's realized arrays are empty and were not modified.

## New nodes

`lem-pc-uniform-inverse-affine-sections-bound` states the ordinary module bound on
inverse images of all affine opens, uniformly in the open and module. Its complete
proof in words follows Tags 01XJ and 01XK and restriction of injective resolutions.
It is the single remaining new hole.

`lem-pc-direct-image-homology-affine-detection` is completely proved. It detects
zero higher direct-image cohomology from inverse-affine derived sections, without
extra geometric or support hypotheses. It is the independent local-to-global
step, not a restatement of the uniform derived bound. Affine basis searches found
no identical blueprint node; the bounded-below pro-etale detection node concerns
a different site and an isomorphism in all degrees.

No change records or forced adaptations are needed.

## Second reading by R3

1. **Statements and interfaces.** Compared all delivered Lean modules with the repository versions. The existing
`uniform_bound_core` signature is byte-for-byte unchanged. The two added statements are lower-level reductions:
ordinary module section vanishing and affine-basis detection of direct-image homology. Neither adds assumptions to
the target; the detection statement is stronger only in the intended independent local-to-global direction and is
used exactly for that step.

2. **Proof and axioms.** Compiled all three modules together with `lcompile.py --all`; compilation is clean. The
axiom probes report only the allowed standard axioms plus `sorryAx` transitively from the explicitly split ordinary
section-bound theorem and existing imported open theorems. There are no new `sorry`s in a definition, and no
`axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or `sorryAx` text.

3. **Split-off statement.** Checked `exists_uniform_inverse_affine_sections_bound` against Stacks Tags 01XJ,
01XK, and 08D5. It is true, strictly simpler than the target, and concerns only ordinary quasi-coherent module
cohomology on inverse images of affine opens. Its proof source, complete natural-language proof, node, and
blueprint ancestry are recorded. The affine-detection theorem is fully proved and has its own node; local searches
found no duplicate declaration.

4. **Pruning and route.** Verified the core proof uses only the new ordinary-bound module, the proved affine-detection
module, and the existing unbounded derived-functor bound. The removed proof-only imports and obsolete proof
dependencies are listed under `## No longer needed`. The route preserves the direct-image/homology unit step;
`dag/units/sk-thm-picard-duality.json` has no realized entries to alter. Import-direction checks confirm the planned
Projective and DirectImage.Sections modules would create cycles and are therefore correctly excluded.

5. **DAG agreement.** Checked each node's Lean record, declaration, proof steps, proof dependencies, source, and
blueprint against the delivered code. Existing node changes are limited to stage-3-owned proof fields; added nodes
contain the required source, searches, proof metadata, and Lean records. No target or definition statement changed.

I changed only this report by adding the second-reading record; no Lean source, node, or interface repair was needed.
