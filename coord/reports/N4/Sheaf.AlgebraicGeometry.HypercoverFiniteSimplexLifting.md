## What changed

Proved `AlgebraicGeometry.Scheme.hypercover_finite_simplex_lifting` in
`Sheaf.AlgebraicGeometry.HypercoverFiniteSimplexLifting`, with its existing signature and
visibility unchanged. The proof follows Stacks 01GN: obtain the chain from `SSet.add_simplices`,
apply the existing one-more-simplex theorem at each link, and compose the covering restrictions.
All added helpers are private and proved. No other Lean module changes.

The interface glue is explicit: pull compatible families along simplicial maps; obtain their
induced maps from the representing bijections; prove composition by evaluation on universal
components; identify an ambient subcomplex inside the next subcomplex using a nested-subtype
isomorphism; and transport representability along that isomorphism. Intermediate representing
pairs come from `exists_simplicial_hom_object`, whose universal property determines them up to
unique isomorphism. The proof handles arbitrary endpoint representing pairs and length-zero
chains by proving that restrictions along simplicial isomorphisms have sections and cover.

The local-lifting conjunct is proved directly, without another admitted lemma: decompose a point
into its component and arrow, pull back the component covering family in the small etale site,
and use its pullback equations. The index type is explicitly a subtype of the source index type,
so has exactly the required universe. No nonemptiness of this covering index is assumed.

Updated the existing DAG node's proof and proof dependencies to record the existence theorem,
the nested-subcomplex bridge, and the topology's pullback-stability proof. Removed the redundant
proof import `WeilConjectures.AlgebraicGeometry.SemiRepresentableObject`; it remains available
through the unchanged public import closure.

Validation: the module compiles through `lcompile.py` without errors or warnings. The required
`deliver3.py --no-push` is run as the final mechanical check. The public imports and all existing
signatures are unchanged. No change record is needed because no public interface changes.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.hypercover_finite_simplex_lifting`
(node `lem-weil-pbc-hypercover-finite-simplex-lifting`). Both conjuncts have complete Lean proofs.
There are no `sorry`s left in the item and no new holes or split-offs.

This is a proof from the existing stated dependencies, as required by stage 3. In particular,
`SSet.add_simplices`, `exists_simplicial_hom_object`,
`isSemiRepresentableCovering_simplicialHomRestriction_one_more_simplex`, and
`semiRepresentableCovering_comp_baseChange` remain the existing lower obligations; this delivery
does not claim that their transitive `sorry` dependencies have been discharged.

## No longer needed

Removed direct proof import `WeilConjectures.AlgebraicGeometry.SemiRepresentableObject` as
redundant with the unchanged public import `Sheaf.AlgebraicGeometry.SimplicialHomObject`.
The source module remains necessary for the statement definitions and is still imported
transitively; no library module is pruned from the targets' import closure by this removal.

The proof does not use node `lem-weil-pbc-etale-covering-base-change` as a separate leaf:
the covering-family pullback sieve identity and `GrothendieckTopology.pullback_stable` prove the
local-lifting clause directly. This dependency was removed from the item's DAG proof route.
The other original proof dependencies remain needed. The Hom-object existence node was added
explicitly to the route because intermediate representing pairs must be obtained before the
one-more-simplex theorem can be applied. No unused lower statement modules were imported.

## Where the brief, the DAG or earlier work was wrong

No false statement or mathematical route error was found. The DAG omitted the explicit use of
`lem-weil-pbc-simplicial-hom-object-exists` for intermediate members of the chain; it is now
recorded. Two interface details needed actual proofs rather than definitional rewriting:
`SSet.add_simplices` uses ambient subcomplex ranges, whereas the one-more-simplex theorem takes a
subcomplex of the successor; and the representing objects at equal/isomorphic endpoints may
be different formal coproducts. The private bridge and section lemmas resolve both.

The cited Stacks TeX files are absent in this read-only local checkout. The already-cited
source was checked via the official pages: https://stacks.math.columbia.edu/tag/01GN,
https://stacks.math.columbia.edu/tag/018S and https://stacks.math.columbia.edu/tag/01G3.

## Second reading by N4

1. **Signatures and visibility.** Compared the delivered module with the repository version.
The theorem signature and all existing declarations are unchanged byte-for-byte; the only
import edit removes a redundant proof-only import, so the public interface is unchanged. Verdict: pass.

2. **Proof validity.** Compiled the module with `lcompile.py`, searched the file for forbidden
constructs and `sorry`, and checked all 12 declarations with `#print axioms` in a scratch copy.
The only axioms are `propext`, `Classical.choice`, `Quot.sound`, and the permitted transitive
`sorryAx` from existing open dependencies. In particular the new local-lifting and section
lemmas have no `sorryAx`. All helper bodies are proved, and the target closes both conjuncts
without new holes. Intermediate representing pairs are chosen only from a universal property
that determines them up to unique isomorphism, and every comparison uses that property.
Checked the length-zero chain with different endpoint representing pairs and empty component
index families; neither needs an unjustified equality or nonemptiness assumption. Verdict: pass.

3. **Statements and split-offs.** No new public theorem or split-off statement was added. The
private helper statements are true interface lemmas used by the proof and introduce no DAG nodes;
the existing target statement remains exactly the node statement. Verdict: pass.

4. **Shortest route and pruning.** The proof uses the existing add-simplices, Hom-object
existence, one-more-simplex, and covering-composition results, while proving the needed
representability transport and local pullback lifting directly. The redundant direct
`SemiRepresentableObject` import and the unused covering-base-change leaf were removed and
recorded in the node/report. A fresh LeanFinder query on formal-coproduct covering lifts and
finite simplicial restrictions returned only zero/one-hypercover constructions, not a replacement
for this all-degree assertion. Searches of `lean/Sheaf`, upstream semi-representable objects,
and Mathlib simplicial subcomplexes found no existing theorem replacing these helpers.
The official Stacks pages 01GN, 018S, and 01G3 confirm the source route. Verdict: pass.

5. **DAG and unit route.** The node's `proof`, `proof_deps`, and `proof_origin` match the Lean
route, including the Hom-object existence dependency and direct Grothendieck-topology pullback
argument. Inspected `dag/units/sk-prop-h2.json`: its `realized` statement and step lists are empty,
and this support node realizes no unit statement or step. The node's add-simplices,
one-simplex-extension, and composition route is preserved without altering unit metadata.
Verdict: pass.

Changed during this second reading: added this review record and corrected the DAG proof
wording for length-zero chains: arbitrary endpoint representing pairs are isomorphic rather
than necessarily equal. No Lean proof or statement changes were needed. The inherited Lean
docstring still summarizes this case as an identity and cites the geometric base-change leaf
for local lifting; the actual proof instead uses the representing isomorphism and the topology's
pullback-stability axiom, as the updated DAG records.
