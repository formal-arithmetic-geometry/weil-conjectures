## What changed

Proved `AlgebraicGeometry.Scheme.exists_dense_open_finite_noetherian_scheme_splitting`
from the existing integral affine splitting theorem and one new fixed-open descent lemma.
The signature and public imports are unchanged.

The proved private helper `reduced_generic_finite_splitting` constructs the dense open
as the union of splitting opens in all integral affine charts contained in V. It proves
density using the open part of each irreducible component outside all other components,
builds the cover with `Cover.mkOfCovers`, and identifies the sources by pasting pullback
squares. `splitting_partition_iso` proves the transport of partitions across those
isomorphisms. The final proof constructs the actual nilradical subscheme, proves its
inclusion surjective, applies the reduced result, and transfers the open and its density
through the homeomorphism.

Compilation: both delivered modules compile through lcompile.py, with no warnings.
The exact source statements of Stacks Tags 04DZ and 04DF were read online. The copied
literature checkout contains only citation metadata, so the new proof is explicitly
marked agent-written. WANTED: local etale-cohomology.tex, Tag 04DZ, and morphisms.tex,
Tag 04DF, for the new descent node. No files outside the sandbox were changed manually.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_dense_open_finite_noetherian_scheme_splitting`
(node `lem-weil-pbc-generic-finite-noetherian-scheme-splitting`).
No sorry remains in the item, including its two private helpers.

Added one hole:
`AlgebraicGeometry.Scheme.finite_splitting_descends_surjective_closedImmersion`
(node `lem-weil-pbc-finite-splitting-closed-immersion-descent`, module
`Sheaf.AlgebraicGeometry.FiniteSplittingClosedImmersionDescent`).
This is a decomposition, not a net proof gain: one hole closed, one added, net zero.
The remaining lemma only descends an existing local splitting over a fixed open.
It does not choose any dense open or prove affine generic splitting; these steps are
actually proved in the item. Its complete argument is in its docstring and node.

Edge cases checked: empty Y has no integral affine charts, and the cover construction
still covers its empty dense open. Empty finite sources use the zero-length partitions
provided by the affine theorem. No disjointness of affine charts is assumed or needed:
cover elements may overlap. The descent lemma includes empty covers and zero-length
partitions; surjective closed immersions and all their base changes preserve emptiness
and carry clopen partitions bijectively. The descent statement does not assume a
uniformly nilpotent defining ideal. General surjective closed immersions suffice by
04DZ and by universal bijectivity of their base changes.

## No longer needed

Removed the direct proof import
`WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance` from the item;
it belongs to the remaining descent lemma's proof and is imported there.
No library module is claimed pruned: this import remains transitively reachable.
The affine splitting theorem and the finite irreducible-components Mathlib leaf remain
needed. The original direct site-equivalence proof dependency is replaced by the new
descent node, whose proof still uses that equivalence and covering compatibility.

No pairwise-disjoint affine-chart assembly, separate finite enumeration of charts,
uniform nilpotence argument, or explicit empty-case lemma is needed by the proved
reduced-case construction. No existing unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier plan is mathematically usable; there is no disputed statement or changed
interface. It underestimates the Lean glue needed to lift etale covers, identify the
iterated pullbacks, and descend the universal-homeomorphism partitions. Those final
steps are isolated precisely by the new lemma. The finite irreducible-components node
is a Mathlib leaf, so it requires no separate project import. The existing affine theorem
is genuinely proved and is used, not restated.

The automatic blueprint ancestor lookup stops at the module-valued created.item of the
parent. The new node therefore inherits the parent's recorded blueprint ancestor and
via chain, adding the parent splitting node. The second reader should verify this
inherited provenance against the parent's existing record.

## New nodes

`lem-weil-pbc-finite-splitting-closed-immersion-descent`: finite etale-local splitting
across a surjective closed immersion over a fixed open. It has no Noetherian, affine,
reducedness or density hypothesis, and requires a splitting already given upstairs.
The three search kinds ran and are recorded in searches.jsonl; LeanSearch returned
Internal Server Error (recorded unavailable), while Loogle, LeanFinder and source grep
found no exact theorem. Blueprint/DAG searches found the general site equivalence,
covering compatibility and surjective closed immersion universal-homeomorphism result,
but no statement of splitting descent. No change record is needed: existing signatures
and visibility are unchanged, and no other module was adapted.

## Second reading by S3

1. **Visible changes and signatures.** I compared the delivered item module with the repository
version. The existing theorem signature and all existing declarations are unchanged; the added
descent module is a new declaration explicitly recorded by its node. No target statement or
definition was altered.

2. **Compilation and proof hygiene.** Both delivered modules compile with `lcompile.py` and no
warnings. The only remaining `sorry` is the named theorem
`finite_splitting_descends_surjective_closedImmersion`; it has a complete source-based proof
docstring and a matching DAG node. There are no axioms, unsafe declarations, hollow definitions,
or forbidden implementation commands. The main theorem's proof closes its original hole.

3. **Statements and new node.** I checked the new descent statement against the Lean type and
the fixed-open descent role it plays in the main proof. It is strictly weaker than the target:
it assumes a splitting upstairs and only produces the corresponding splitting downstairs. It
does not choose a dense open or restate the main theorem. The node records its source, proof
steps, dependencies, searches, and Lean declaration.

4. **Shortest route and pruning.** The main proof uses the existing affine splitting theorem,
the Mathlib irreducible-component result, and the nilradical reduction. The direct etale-site
import was removed from the item because it is needed only by the split-off descent theorem and
is imported there. No unused public import or old proof dependency was retained, and the unit's
realized route is preserved.

5. **DAG and provenance.** The main node's `proof`, `proof_deps`, and `proof_origin` match the
Lean proof. The new node is marked `split`, has the inherited blueprint ancestry, and its
statement and declaration agree verbatim. No existing node statement was changed.

I changed only this report section after the first worker delivery; no Lean source or DAG content
was changed during second reading.
