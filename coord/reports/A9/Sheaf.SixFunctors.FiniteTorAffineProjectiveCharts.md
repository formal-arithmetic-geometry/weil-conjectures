## What changed

Proved `WeilConjectures.GeneratorReduction.finiteTorAffineProjectiveCharts` with its
statement unchanged. The proof constructs the required finite pro-etale family from
one weakly contractible affine cover of each leaf and the existing common finite
projective-chart theorem. It proves point-surjectivity, translates strict cochain
bounds to termwise vanishing, and transports the representative isomorphisms to the
specified ordinary derived pullback.

Added two proved public helper modules:

- `Sheaf.SixFunctors.AffineConstructibleRestrictionComplete` proves completeness
  after ordinary restriction through the affine open, a tree path, and a weakly
  etale object. Its private exactness argument reuses the existing restriction
  proof without the unnecessary ambient qcqs hypotheses. The normalized quotient,
  Roos, completion, and unit comparisons are the existing proved APIs.
- `Sheaf.SixFunctors.AffineResidueLisseTree` constructs the simultaneous residue
  stratification. It builds a recursive binary pullback tree from the existing
  constructible-cut helper, retaining the actual factoring maps; its private
  conversion to `QcqsOpenClosedTree` is proved by induction. Residue bounds and
  finite module models are transported using the existing reduction/homology
  and constant-module pullback comparisons.

All new theorem bodies are complete. Existing shared modules and their interfaces
are unchanged. All proof dependencies are private imports. New public imports are
only those needed for the new modules' statements.

The completeness helper explicitly passes its limit-preservation instances to
avoid hidden conversions in class search. Its two backward transparency options
are true. These local checking choices change no shared definition or exported
attribute. Profiling identified the abstract root-path conversion as an
unnecessary cost; case-splitting the root subtree makes its identity map reduce
immediately. The final chart goal is normalized using the generated
pro-etale constructor equations before the cochain witnesses are introduced.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.GeneratorReduction.finiteTorAffineProjectiveCharts`
(node `lem-sf-finite-tor-affine-projective-charts`).

Also proved the new helpers
`WeilConjectures.GeneratorReduction.affineConstructibleRestrictionComplete`
(node `lem-sf-affine-constructible-restriction-complete`) and
`WeilConjectures.GeneratorReduction.affineResidueLisseTree`
(node `lem-sf-affine-residue-lisse-tree`).

Original holes closed: 1 of 1. Holes added: 0. Sorries remaining in the delivered
files: none. No split-off unproved obligation is added. The proofs use the existing
stated library dependencies, some of which themselves remain unproved.

## No longer needed

No original public import was removed, and no module is withdrawn. The planned
constructible open/closed refinement and common affine projective charts remain
needed, the former through its proved constructible-cut helper and recursive tree
construction. The numerical tree encoding is unnecessary: we retain the recursive
tree and its leaf factorizations directly. Its encoding theorem is not applied,
although the existing constructible-cut module still imports the module that
contains it; this delivery therefore claims no pruning of that module.

The theorems `constructible_residue_tree` and
`constructible_projective_chart_refinement` are not applied: their invertibility
and ambient qcqs binders do not match this item's arbitrary ambient scheme.
`ConstructibleResidueTree` remains a proof import for its existing proved finite
model transport helpers and uniqueness comparison of ordinary derived pullbacks.
Consequently this delivery claims no pruned module and no withdrawal of those
existing declarations.

The finite Tor interval is not needed beyond membership in
`sfIntegralConstructible`: bounded residue cohomology and its finite module models
suffice for the existing affine common-chart theorem. Neither a residue
characteristic restriction nor an invertibility hypothesis is added.

## Where the brief, the DAG or earlier work was wrong

The planned dependencies do not directly supply the assertion in this item's
signature. The existing residue refinement and projective refinement theorems
require an invertibility hypothesis and a qcqs ambient scheme. The signature here
allows arbitrary X and has neither hypothesis. The existing underlying immersion
inverse-image theorem and the private exactness ingredients require no ambient
compactness, so a local proof adaptation supplies the missing restriction fact
without changing a shared interface. The source restriction and residue proofs
already do not use the invertibility hypothesis. The new residue proof pulls the
original constructible partitions back to the affine open and keeps a recursive
tree, avoiding both the extra hypothesis and an unnecessary numerical encoding.

A metadata scan found a preexisting cycle between
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent`. No dependency path returns to
any node changed or added by this packet. The existing metadata is left for the
maintainer.

The unit route is preserved: both new nodes are below the original chart node,
and no unit statement or realized step is replaced or withdrawn.

## New nodes

`lem-sf-affine-constructible-restriction-complete` records the proved completeness
restriction step, including the normalized quotient/completion unit comparison.
It makes no constructibility or projective-model conclusion.

`lem-sf-affine-residue-lisse-tree` records the proved finite geometric refinement
and residue-model transport. It asserts neither projective models nor a finite
chart family. Both new nodes lie in `sec-six-functors`, unit
`sk-thm-sf-compatibility`, below the assigned chart node. No change record is
required because no existing statement, definition, or public interface changes.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
