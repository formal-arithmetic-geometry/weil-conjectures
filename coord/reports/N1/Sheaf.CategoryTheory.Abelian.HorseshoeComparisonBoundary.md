## What changed

The original boundary statement is preserved. Its proof combines three parts: canonical
SES-boundary naturality for the augmentation maps, an inverse-unit boundary statement on
bounded below injective complexes, and canonical SES-boundary naturality for mapExtendIso.
The private comparison_eq_unit calculation identifies the fixed inverse-unit comparison
with the existing explicit chosen-resolution comparison. All constructions use real
maps and inverses of isomorphisms; no data are chosen from an unproved existence claim.

The new proof import is Sheaf.CategoryTheory.Abelian.RightDerivedInjectiveBoundary.
The node copy follows this route. No existing public definition, statement or visibility
is changed, and no other existing module is adapted. All helper binders are explicit,
and injectivity instances are local hypotheses of the proofs; the static interface
comparison for the original module is empty.

## Proved and sorry left

Closed: CategoryTheory.horseshoe_comparison_boundary
(node lem-sc-p1-horseshoe-comparison-boundary).

Added and left: CategoryTheory.rightDerived_injectiveComplex_boundary
(node lem-sc-p1-right-derived-injective-boundary), in the new module
Sheaf.CategoryTheory.Abelian.RightDerivedInjectiveBoundary.

This is a decomposition: one original hole is closed and one strictly lower hole is
added, so the net hole count is zero. The new theorem handles only the inverse derived
unit on an arbitrary bounded below injective-complex SES. It has no augmentation maps,
objects of the original short exact sequence, injective-resolution choices or explicit
chosen-resolution comparisons. The augmentation and endpoint-identification parts are
proved in the original module and are required to combine it with this lower theorem.
No other sorry is left in the delivered Lean files.

## No longer needed

No original import is removed: both public imports are needed by the unchanged statement.
The direct proof no longer needs lem-weil-pbc-triangle-morphism-extension or
lem-weil-pbc-kinjective-hom-derived. Canonical SES-boundary naturality replaces the
vanishing-Hom and third-map-uniqueness detour. The old direct dependencies
lem-weil-pbc-bounded-below-injectives-kinjective, def-weil-abstract-derived-category and
def-weil-triangulated-category are not separately applied by this proof; the existing
Mathlib derived-unit and category structures supply their relevant infrastructure.
The degreewise-split connecting-morphism node remains a dependency of the new theorem.
The degreewise-split-derived-triangle node is no longer needed: the proved
lem-sc-p1-split-ses-boundary-comparison supplies the boundary identification directly. No claim is made that these modules are globally unreachable from
other targets.

## Where the brief, the DAG or earlier work was wrong

The old Step 2's uniqueness argument is unnecessary: Mathlib already proves naturality
of the canonical SES boundary. The remaining resolution-level boundary comparison was
not separately stated in the DAG. The new node isolates original Steps 1 and 3 rather
than repeating the original theorem under another name. The unit route is unchanged;
sk-thm-picard-duality has no realized statement or proof-step node to bypass.

The local literature/stacks-project/derived.tex file is absent on this machine. The cited
Stacks tags [014Q](https://stacks.math.columbia.edu/tag/014Q),
[0159](https://stacks.math.columbia.edu/tag/0159) and
[015B](https://stacks.math.columbia.edu/tag/015B) were read from the Stacks website. The source and proof
follow the original item's references.

The compiler wrapper was updated during the session to queue shared compile slots.
One request waited over twelve minutes before starting Lean; it was restarted through
the same wrapper. No compile limit, tool or shared library was altered by this worker.

## New nodes

lem-sc-p1-right-derived-injective-boundary, at
 dag/nodes/sec-picard-framework/lem-sc-p1-right-derived-injective-boundary.json,
states the inverse-unit boundary square for general bounded below injective complexes.
Its two accompanying definitions lift the canonical boundary through a fully faithful
inclusion and form the inverse-unit comparison. The lift and inverse are uniquely
specified; they do not use sorry. The statement remains valid for zero complexes,
split SESs, and arbitrary lower bounds: the same cone and unit argument applies in
these cases. Three Mathlib search kinds were attempted; LeanSearch was unavailable.
No change record is needed: the existing module has no interface changes. The first
dry run conservatively flagged section-variable commands and private instance
registration; these were removed in favor of explicit binders and local instances.


## Second reading by N1

1. Compared every delivered existing module with the repository using diff and the
   declaration-table comparison: the original public signature and visibility are
   unchanged byte for byte. The only new original-module import is proof-only.
   No existing definition changes and no change record or forced adaptation is needed.
2. Both modules compile through lcompile.py. The only sorry is the named
   CategoryTheory.rightDerived_injectiveComplex_boundary listed above. Scanning finds
   no prohibited declarations or attributes and no holed definitions. Explicit
   #print axioms checks show only propext, Classical.choice and Quot.sound for both
   new definitions; the original theorem and the one lower hole additionally have
   sorryAx. The definitions use actual maps, inverses of established isomorphisms,
   and the unique preimage through a fully faithful inclusion.
3. Read the lower statement with its explicit definitions, its complete docstring
   proof and node. Zero complexes and split sequences give zero boundaries; arbitrary
   lower bounds remain valid under shift and admit a common minimum bound. The result
   needs only additivity, since termwise splittings are preserved; it does not require
   v to be left exact. It is a genuine reduction: the proved augmentation square and
   chosen-to-fixed comparison calculation are absent from the lower theorem.
   Independent leanfinder, loogle and grep searches used the queries recorded in the
   new node and searches.jsonl. No duplicate complete statement was found.
4. Checked the proof from the top downward and the full old proof_deps list. Canonical
   boundary naturality proves the augmentation square and mapExtendIso square directly.
   A shorter route for the remaining lower hole uses the already proved
   DerivedCategory.triangleOfSESδ_eq_degreewiseSplit twice and unit naturality at the
   connecting chain map. This avoids reproving the cone comparison or constructing a
   distinguished-triangle morphism. The new node and docstring now give this route.
   The unit sk-thm-picard-duality has empty realized statement and step arrays; no
   realized unit step is bypassed. No original module import can be removed, because
   both public imports serve the unchanged signature. No global module pruning is claimed.
5. Checked both JSON nodes against the Lean declarations and definitions. Existing
   node changes are confined to proof, proof_deps and proof_origin. The new node has
   source, complete proof steps, dependency union, search records, creation and blueprint
   provenance, unit/chapter and its verbatim declaration record. The source references
   were checked against Stacks [014Q](https://stacks.math.columbia.edu/tag/014Q),
   [0159](https://stacks.math.columbia.edu/tag/0159),
   [015B](https://stacks.math.columbia.edu/tag/015B) and
   [0152](https://stacks.math.columbia.edu/tag/0152).

Second reading changed the new module's public PlusSingle import to the smaller
WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus import,
which supplies the actual derived functor and its shift structure. It also replaced
an unnecessary cone/triangle argument in the lower hole's proof plan and docstring
with the existing proved split-boundary comparison, updated its dependency union,
and completed the pruning report. No further hole was closed or added. This remains
one original hole closed and one strictly lower hole added: a decomposition, net zero.
