## What changed

Replaced the sorry in `AlgebraicGeometry.exists_singleComplexAffineSpectrumCoordinates`
without changing its signature, its public imports, or its docstring. The proof constructs
K0 and K0' as pullbacks along the inverse canonical affine spectrum isomorphisms. It
constructs phi0 using inverse spectrum naturality and the canonical universal derived
pullback composition comparison, then proves both quasi-coherence obligations using
`AlgebraicGeometry.derivedPullback_tensor_preserve_QCoh`.

Added `Sheaf.AlgebraicGeometry.AffineSpectrumDerivedCoordinates` for these explicit data,
`Sheaf.AlgebraicGeometry.AffineSpectrumStalkCondition` for the stalk transport obligation,
and `Sheaf.AlgebraicGeometry.AffineSpectrumBaseChangeComparison` for the direct-image mate
obligation. The target's proof-only imports are the two obligation modules and
`Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh`. Updated its DAG proof to follow
this construction and decomposition.

## Proved and sorry left

Closed the original hole by a compiling decomposition:
`AlgebraicGeometry.exists_singleComplexAffineSpectrumCoordinates`
(node `lem-pc-single-complex-affine-spectrum-coordinates`). The theorem's combination
proof is complete: it constructs the objects and morphism, proves their quasi-coherence,
and combines the separately stated stalk equivalence and morphism identification.

Two holes added, each exactly a public theorem with `:= by sorry`:

- `AlgebraicGeometry.affineSpectrumCoordinates_stalkCondition`
  (`lem-pc-affine-spectrum-stalk-condition`): only the stalk equivalence for the explicit
  coordinate data, with no quasi-coherence assumptions or direct-image conclusion.
- `AlgebraicGeometry.affineSpectrumCoordinates_comparison`
  (`lem-pc-affine-spectrum-base-change-comparison`): only the endpoint isomorphisms and
  actual base-change morphism equation for the same explicit data; it uses no stalk
  condition or quasi-coherence assumption.

There is no sorry left in the original module and no sorry in a definition. This is
one upper hole closed and two strictly smaller holes added (net -1), counted as a
**decomposition**, not a complete axiom-free proof. Each remaining theorem has a source,
a complete proof in words, its own module and its own DAG node.

The three explicit definitions in `AffineSpectrumDerivedCoordinates` are real
constructions. Choice is used only for the existing canonical composition comparison
pinned by its universal left-derived property, not to choose arbitrary coefficient data.

## No longer needed

None. No original import was removed. The original lower proof dependencies are still
needed by the two remaining transport obligations (or the explicit construction); they
are relocated to those nodes rather than claimed as globally pruned. Specifically, the
old direct dependencies `lem-pc-ringed-spaces-derived-pullback-composition`,
`lem-weil-pbc-module-stalk-pullback`, `def-pc-base-derived-tensor-cohomology-model`,
`def-pc-single-complex-base-change-stalk-condition`,
`lem-pc-stalk-comparison-coordinate-invariance`, and `def-pc-derived-base-change-map`
are no longer direct proof dependencies of the item: the new construction or transport
nodes retain them. No module is globally pruned. The quasi-coherence
step continues to use the planned pullback-preserves-quasi-coherence theorem.

## Where the brief, the DAG or earlier work was wrong

The planned `isIso_stalkComparison_iff_coordinates` compares representatives on the same
fixed square. Its signature alone does not transport the four schemes or their stalk
rings to spectrum coordinates. Similarly, pullback composition alone does not directly
state naturality of the derived base-change mate. The two new obligations isolate these
missing glue arguments instead of treating the existing results as stronger than they are.

The `blueprint_refs.py ancestor` command returns `None` for this recently created node,
whose created.item is a module name. The new nodes inherit its recorded blueprint
ancestor `lem-pc-rf-perfect-base-change` and prepend this item's node to its existing via
chain. A search of the whole blueprint for "spectrum coordinates" returned no match.
The unit's realization record has no statement or step nodes to bypass; its route stays.

Sources read: Stacks Tags 0DJ8 (affine spectrum reduction of the stalk condition), 0DJ9
(affine-open base case), and 08HY (canonical unbounded base-change map as a counit mate).
The spectrum naturality lemma and derived composition signatures were read in Mathlib
and the library. Searches found no existing four-scheme derived transport statement;
LeanSearch was unavailable (HTTP 500), recorded as unavailable rather than as a negative
search result.

Edge cases checked mathematically: empty affine schemes and zero rings cause no point
choices; the stalk condition is vacuous on the empty upper-left scheme on both sides.
Zero objects and a zero coefficient map are transported functorially. Identity squares
use the same unit/composition comparisons. All constructions use equivalences, hence
need neither a flat square nor a bounded complex. The new obligations quantify over
arbitrary derived objects, which is valid because this is coordinate transport only.

## New nodes

`def-pc-affine-spectrum-derived-coordinates`: constructs the two coefficient objects,
the canonical pullback comparison, and the coefficient morphism. Its source is the
canonical spectrum-coordinate reduction of 0DJ8 and composition of 0D5S. This is a
construction node with no proof hole.

`lem-pc-affine-spectrum-stalk-condition`: stalk invariance for the explicitly constructed
coordinate data, sourced to equation-bc and affine reduction in 0DJ8/0DJ9. Its proof uses
stalk pullback, exact stalks, the tensor-cohomology model and fixed-square coordinate
invariance, together with derived pullback composition.

`lem-pc-affine-spectrum-base-change-comparison`: naturality of the actual derived mate
for the explicit coefficient data, sourced to the affine reduction and the counit
construction in 08HY, with coherence in 0D5S. It is independent of the stalk obligation.

For all three nodes, LeanFinder and Mathlib grep found scheme-coordinate lemmas but no
matching derived transport declaration; LeanSearch was attempted and unavailable.
No interface change or forced adaptation was made, so no change record is needed.

## Second reading by Q3

1. Compared the delivered item module with the repository version. The existing theorem
   signature and all declarations before its proof are byte-for-byte unchanged; the proof
   only supplies the original existential tuple. Verdict: pass.
2. Compiled all four delivered modules with `lcompile.py --all`. The item has no `sorry`,
   and the only remaining holes are the two named transport theorems, each with a matching
   node and full source/proof documentation. No definitions contain `sorry`; no forbidden
   declarations occur. A scratch `#print axioms` check of all six delivered declarations
   found only `propext`, `Classical.choice`, and `Quot.sound` for the three definitions,
   and those axioms plus `sorryAx` for the two split theorems and the item. Verdict: pass,
   subject to the two explicitly split obligations.
3. Reviewed the three added interfaces. The coordinate objects and morphism are concrete
   pullback constructions; the stalk theorem asserts only invariance of `StalkCondition`,
   and the comparison theorem asserts only endpoint isomorphisms and the base-change
   equation. Neither adds quasi-coherence or invertibility hypotheses. Searches recorded
   in the nodes found no existing declaration with these statements. Independent searches
   used LeanFinder for derived equivalence and counit-mate invariance, Loogle for
   `CategoryTheory.conjugateIsoEquiv`, and Mathlib grep for derived-isomorphism and
   stalk/isoSpec transport. The hits provide generic mates and derived uniqueness, not
   either four-scheme transport statement. Local searches also found only fixed-square
   coordinate invariance and open-restriction transport. Identity squares, empty affine
   schemes/zero rings, and zero coefficient objects/maps are consistent with both new
   statements. The chosen composition family is the very family used by
   `schemeDerivedBaseChangeMap` and the stalk counits; its universal lift equation and
   coherence exclude arbitrary twists. Verdict: pass.
4. The item proof uses the explicit coordinate construction, the planned pullback
   quasi-coherence theorem, and the two strictly smaller transport obligations. The
   updated proof dependencies match those uses; no old dependency is silently claimed as
   proved by the item. Verdict: pass; the decomposition is mathematically transparent.
5. The DAG nodes agree with the Lean declarations and the unit realization is unchanged.
   The new nodes have sources, proof plans, searches, and the required Lean records.
   Verdict: pass.

Changed only this report by adding this second-reading record and explicitly listing
the relocated old direct proof dependencies under `## No longer needed`. No Lean or DAG repair was
needed after compilation.
