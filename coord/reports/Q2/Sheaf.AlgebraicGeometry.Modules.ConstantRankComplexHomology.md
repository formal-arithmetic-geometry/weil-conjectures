## What changed

Replaced the sole proof hole of
`Sheaf.AlgebraicGeometry.Modules.ConstantRankComplexHomology` by a compiled reduction.
The existing declaration signature and docstring are unchanged. The proof applies
`kernel_image_pullback_of_constantRank` separately to the outgoing and incoming differentials,
extracts the kernel, image and local image retractions, applies
`isFiniteLocallyFreeOfRank_homology_of_locally_split_image` to the three-term short complex,
and transports the rank statement across `HomologicalComplex.homologyIsoSc'`.

Added two new statement modules, each with a single named theorem, a complete proof in words,
and a matching node. These are strictly smaller components of the argument: the first concerns
one map, with no complex or homology; the second concerns a short complex with already locally
free cycles and boundaries and local retractions, with no reducedness or fibre-rank condition.
Their conjunction is genuinely used twice and then combined by a real Lean proof.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_homology_pullback_of_constantRank`
(node `lem-pc-constant-rank-complex-homology`). There are no direct proof holes left in the
item module. This is a decomposition, not a sorry-free proof: one hole closed, two added,
net minus one hole, with no claim of transitive axiom closure.

The two remaining holes added by this delivery are:

- `AlgebraicGeometry.Scheme.Modules.kernel_image_pullback_of_constantRank`
  (`lem-pc-constant-rank-map-kernel-image`), in
  `Sheaf.AlgebraicGeometry.Modules.ConstantRankMapKernelImage`.
- `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_homology_of_locally_split_image`
  (`lem-pc-locally-split-short-complex-homology`), in
  `Sheaf.AlgebraicGeometry.Modules.LocallySplitShortComplexHomology`.

All three modules compile together using the prescribed local compiler. The new single-map
statement handles zero source/target ranks, rank zero via the empty minor, and empty open
subschemes. At nonempty points its hypotheses force a ≤ min(m,n). The second statement uses
local retractions, not a global splitting; refining to affine opens preserves the retractions.
The split image-to-kernel sequence forces b ≤ k at every nonempty fibre, so natural subtraction
is valid. On an empty scheme arbitrary formal ranks cause no contradiction. No definition or
existing theorem statement was changed and no data was chosen from a mere existence hole.

## No longer needed

Second reading also removed the redundant direct public LocallyFree import from both new
modules; it is already exposed by FreeComplex through Modules.Sheaf.

Removed the item's direct proof imports:

- `Sheaf.LinearAlgebra.MatrixRankFieldExtension`;
- `Sheaf.RingTheory.FiniteProjectiveStandardFreeCover`;
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`.

These are not globally pruned: field-extension rank is retained by the new single-map module;
the finite-projective standard free cover is retained by the new short-complex module; and
local freeness definitions are needed by both new statements. All original substantive proof
dependencies remain needed inside the new statements: reducedness, matrix rank, free modules,
field-extension rank, finite-projective standard covers and open pullback/restriction.
No existing DAG node or module is claimed to have left the targets' import closure. The main
node now lists the two new argument components as its direct proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The previous plan marked the reduced-ring normal-form step as elementary although no existing
Lean declaration supplies its substantial matrix, localization and sheaf glue. The existing
finite-projective standard-free-cover theorem by itself cannot bridge from a complex of sheaves
to that module theorem. The new nodes make those two independent missing components explicit.
The existing local-splitting theorem for short exact sequences of finite locally free sheaves
is unsuitable here: it already assumes local freeness of the quotient being proved.

The source blueprint markdown is absent from this read-only checkout. The source's full unit
paragraph and the inherited node proof were read in `dag/units/sk-thm-picard-semicon.json` and
`dag/nodes/sec-picard-framework/thm-pc-semicontinuity-base-change.json`. The new proof descriptions
expand their normal-form and direct-summand arguments and are marked as written by an agent.
The unit route is unchanged, and no unit-realized node is bypassed. Mathlib searches via the
prescribed wrapper found generic free-locus/projective/homology APIs but no matching sheaf
statements. LeanSearch returned Internal Server Error and is recorded as unavailable.

## New nodes

`lem-pc-constant-rank-map-kernel-image` records the single-map reduced-scheme normal-form
argument. It states local freeness of the kernel and image and local retractions of the image
inclusion after the given open pullback. Its ancestor is
`thm-pc-semicontinuity-base-change`, proof (3), normal-form claim. It uses the existing rank
field-extension node and affine sheaf/module comparison nodes. The second reader should
especially check the compatibility of restricting categorical images with the affine normal
form. There is no new definition.

`lem-pc-locally-split-short-complex-homology` records the kernel/image direct-summand argument
on any scheme. Its ancestor is `thm-pc-semicontinuity-base-change`, proof (3), the subsequent
kernel/image splitting paragraph. It uses the finite-projective standard free cover as a
generic tool; the original item's plan already used that node. It also cites the existing
affine tilde comparison and projective direct-summand tools. Local freeness is proved by
refining the local retraction neighbourhoods; no global retraction is assumed. No change
record is needed because existing signatures and definitions are unchanged.

## Second reading by Q2

1. I compared the delivered item module with the repository version. The theorem signature and
all existing declarations are byte-for-byte unchanged; only the proof and proof-only imports
changed. Verdict: pass.

2. I compiled all three delivered modules with `lcompile.py --all`; they compile without
errors or warnings. The two remaining `sorry`s are exactly the named split-off theorems in
the new modules, and there are no `sorry`s in definitions. The reduction theorem uses the two
split-off declarations and transports the result through the canonical homology isomorphism.
Verdict: pass.

3. The two split-off statements are genuine components of the blueprint proof. The
constant-rank map statement has the reduced-scheme normal-form hypotheses and separately
returns kernel freeness, image freeness, and local splitting. The short-complex statement
assumes precisely locally free kernel/image and local splitting, and returns the homology
rank. They are strictly smaller than the original complex theorem and are not restatements.
I checked zero-rank and empty-scheme cases against the natural-subtraction formulations.
Searches found no existing upstream or Mathlib theorem with either statement. Verdict: pass.

4. The proof follows the unit route: outgoing kernel, incoming image with local retractions,
then the locally split short-complex homology argument, followed by the canonical homology
isomorphism. The removed imports were proof-only dependencies from the original module; each
is still retained by the split-off modules where used. Verdict: pass.

5. The DAG proof steps, proof dependencies, proof origins, Lean declarations, and new-node
metadata agree with the Lean files. No unit statement or definition was changed. Verdict:
pass.

I removed the redundant public LocallyFree import from both new modules: FreeComplex
already exposes it through Modules.Sheaf. I corrected the short-complex node proof to
justify exactness of open restriction on stalks, rather than claim sectionwise exactness
of sheaf sequences. I normalized both new nodes’ Lean statement records to the verbatim
signatures. Scratch `#print axioms` checks for all three declarations showed exactly
propext, Classical.choice, Quot.sound, and sorryAx. No Lean statements or proofs changed.

Additional second-reading search evidence: LeanFinder was queried for a linear map of
vector bundles with constant fibre dimension on a reduced base and returned only topological
vector-bundle trivialization APIs. Loogle with `"IsSplitMono", "kernel"` returned generic
binary-bicone splitting constructions, which do not establish local freeness. The prescribed
grep search for finite-local-freeness with splitting and rank with nilradical had no hits.
Local `rg` searches included retractions, summands, constant rank, and the upstream affine
locally-free modules; the latter goes from local freeness to a summand, not conversely.

For clarity, the original direct proof dependencies removed from the main node are
`def-pc-cochain-complex-modules`, `def-weil-open-immersion`,
`lem-weil-matrix-rank-field-extension`, `def-pc-reduced-scheme`, `def-weil-matrix-rank`,
`def-weil-pbc-free-module`, `lem-weil-pbc-finite-projective-standard-free-cover`,
`lem-weil-pbc-open-immersion-module-pullback-restriction`, and
`def-amb-finite-locally-free-module`. Their definitions or substantive argument steps remain
in the two components or the existing public statement imports; none is globally pruned.
