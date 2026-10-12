## What changed
Replaced the first worker's restatement `exists_etale_complex_class_rep_core` with a
real finite-filtration reduction. The existing theorem
`AlgebraicGeometry.Etale.exists_etale_complex_class_rep` keeps its exact signature
and docstring. Its proof now inducts down a finite filtration, lifts one graded
piece, represents the residual by induction, moves the two representatives to a
common stage of the filtered opposite category, and adds them using cocone
naturality. The length-zero case represents zero at any stage.

Added the new proof-only module
`Sheaf.AlgebraicGeometry.EtaleComplexGradedClassDescent`, with a named open theorem
`AlgebraicGeometry.Etale.exists_etale_complex_graded_class_rep`. It asserts a finite
decreasing target filtration with stage representatives modulo the next step;
it does not assert a representative of the whole class. Its docstring gives the
spectral-sequence construction, uniform stabilization bound, filtration endpoints,
and passage from stable-page representatives to graded lifts.

The main module imports this new module privately. Removed the two unnecessary
public Mathlib imports `Mathlib.AlgebraicGeometry.AffineTransitionLimit` and
`Mathlib.Algebra.Homology.HomologicalComplexLimits`; both modules compile without
them. Kept the two existing public WeilConjectures imports needed by signatures.
There are no definition or existing statement changes. The import-only change
record is `coord/changes/EtaleComplexClassDescent-imports.md`; it lists all 153
transitive importers. The sole direct importer already publicly imports both
removed Mathlib modules, so downstream public exposure is preserved.

## Proved and sorry left
`AlgebraicGeometry.Etale.exists_etale_complex_class_rep` has a complete proof body
(1 of 1 original local sorries removed), conditional on the new graded lifting
lemma. The delivery is partial, not an axiom-free proof of etale continuity.

The sole local sorry delivered is
`AlgebraicGeometry.Etale.exists_etale_complex_graded_class_rep`, node
`lem-weil-pbc-etale-complex-graded-class-descent`, in its own new module. It is
exactly a named theorem with `:= by sorry`, source and full natural-language
proof in the docstring. There are no hollow definitions or other new declarations.
Both modules compile without warnings. Explicit scratch `#print axioms` checks
for both public declarations give only `propext`, `Classical.choice`, `Quot.sound`
and `sorryAx`, the last expected from the open graded lifting theorem.

## No longer needed
The main module no longer directly imports:

- `Sheaf.AlgebraicGeometry.EtaleCohomologyLimitOfSchemes`
- `Sheaf.CategoryTheory.BoundedFilteredComplexSpectralSequence`
- `Sheaf.CategoryTheory.HypercohomologyFirstPage`
- `Sheaf.CategoryTheory.KInjectiveBridge`
- `Sheaf.CategoryTheory.SpectralSequenceComparison`
- `Sheaf.CategoryTheory.ExistsDirectedReindexing`
- `Sheaf.Paper.EtaleHypercohomologyPullbackFunctorial`

Six of these proof-plan imports are retained in the new open graded lifting module.
`Sheaf.CategoryTheory.SpectralSequenceComparison` is also removed there and replaced
by `Mathlib.Algebra.Category.Grp.AB`: its filtered-colimit preservation of homology
supports direct induction on spectral-sequence pages, using differential compatibility
and the page isomorphisms, followed by the uniform stabilization bound.
The two public Mathlib imports listed above are removed from both modules.

All nine OLD direct proof dependencies have been replaced in the main node:

- `def-sp-etale-dictionary`
- `def-sp-kinjective-bridge`
- `def-weil-pbc-etale-cohomology`
- `lem-weil-pbc-complex-spectral-sequence-comparison`
- `lem-weil-pbc-etale-cohomology-limit-of-schemes`
- `lem-weil-pbc-filtered-category-directed-cofinal`
- `lem-weil-pbc-hypercohomology-e1-pullback-functorial`
- `thm-sp-if-e1`
- `thm-sp-spectral-object-yields`

Eight remain dependencies of the graded lifting node.
`lem-weil-pbc-complex-spectral-sequence-comparison` is no longer needed by either
delivered node; the graded node instead uses
`lem-weil-pbc-filtered-colimit-abelian-groups-exact`. No old DAG node or project
module is claimed globally prunable. The main node now directly depends only on
`lem-weil-pbc-etale-complex-graded-class-descent`.

## Where the brief, the DAG or earlier work was wrong
The first worker's core conclusion was equality after applying the isomorphism
`eB` with otherwise identical hypotheses. Cancelling `eB` proves no mathematical
step of descent; that split is rejected as a restatement. Its copied DAG record
also depended on the original node, making a cycle, and had a placeholder rather
than a verbatim Lean statement. Removed that core theorem and its proposed node.

The replacement leaves the stable-page/graded lifting argument open, while
formalizing the separate final finite-filtration induction. The existing generic
comparison theorem exposes only a full abutment isomorphism, so its proof cannot
serve as a page-comparison dependency. The repaired plan uses filtered-colimit
preservation of homology directly: first-page continuity starts an induction,
differential compatibility identifies the short complexes, and preservation of
homology together with page isomorphisms advances the induction. Vanishing outside
s>=a and t>=0 persists; the uniform differential bound gives stable-page comparison.

## New nodes
`lem-weil-pbc-etale-complex-graded-class-descent`: finite target filtration and
lifting a coset modulo the next step, before combining graded lifts. The node
has the exact Lean signature, source (Stacks 0EZM and 015J), expanded proof,
its proof dependencies with filtered-colimit exactness replacing the final-abutment
comparison theorem, four fresh searches (LeanSearch unavailable; LeanFinder, Loogle and grep completed) and D2 creation metadata.
No fabricated review metadata is carried over. Import-only change record:
`coord/changes/EtaleComplexClassDescent-imports.md`. Its chapter and unit match the
original node (`sec-curve-estimates`, `sk-prop-h2`).

## Earlier second reading (a previous round; superseded)
1. Compared the delivered main module with the repository by `diff -u` and the
   declaration comparison parser. PASS: `statement_changed` is empty; the sole
   original signature and docstring are byte for byte unchanged. Only its proof
   and imports change. No target statement or definition changes.
2. Compiled both modules in import order through `lcompile.py --all`. PASS:
   no errors or warnings. Reviewed the source for prohibited declarations and
   hidden sorries: only the named new graded theorem is sorry. Explicit scratch
   axiom checks for both declarations show exactly the permitted standard axioms
   plus `sorryAx`; scratch copies were then removed.
3. Rejected and removed the equivalent core split. Reviewed the new graded
   assertion against Stacks 0EZM and 015J. PASS as a partial proof: the statement
   is true and supplies precisely the filtration endpoints and residual lifting
   needed by the formal induction. Checked p<a (length zero, zero abutment),
   p=a (one graded piece), and p>a (length p+1-a). Empty I is excluded by
   IsCofiltered. The stabilization bound uses the (complex,resolution) coordinate
   order, with r>max(t+1,s-a). Fresh leanfinder, loogle and grep searches (plus an unavailable LeanSearch call), plus
   local searches in both roots, found no existing graded-lifting declaration;
   generic colimit representative lemmas require the missing comparison first.
4. Reviewed from the whole-class conclusion down to graded pieces. PASS:
   the final finite induction is now genuinely formalized; imports are reduced
   in the main module and the remaining spectral-sequence route is documented
   on the open graded node. Listed every old direct dependency above. Inspected
   `dag/units/sk-prop-h2.json`: no realized entry names this technical node, and
   the Kummer/curve unit route is unchanged. No global pruning is claimed.
5. Read both delivered node records against the Lean. PASS: the main node uses
   only graded descent plus elementary finite induction; the new node carries
   the remaining spectral-sequence proof plan and verbatim Lean statement. The
   new node depends on first-page, convergence and pullback-functoriality
   statements plus filtered-colimit preservation of homology, not on the final
   abutment comparison theorem or the main node, avoiding
   the first worker's cycle. No unrelated node fields are changed.

Second reading repair: checked the direct induction on pages using filtered-colimit
preservation of homology and compatibility of the incoming and outgoing differentials.
The stable-page comparison follows from the uniform bound, without borrowing the
proof of the final-abutment comparison theorem. Blueprint ancestry now points to
the imported strict-henselization stalk formula via the original technical items.

Second reading changed: removed the restatement and circular core node; added a
source-backed graded lifting module/node; wrote the actual finite-filtration
induction; removed unused Mathlib imports; updated main proof metadata and report.

Preflight repair: recorded the unavailable LeanSearch call with the required
`unavailable` verdict, and added the required import-change record after inspecting
the downstream closure. The original theorem signature remains unchanged.

Additional downstream check: attempted a scratch single-file compile of the
unchanged sole direct importer against the sandbox overlay. It could not run
because the published local library lacks EtaleComplexClassVanishing.olean.
No downstream file was changed. Public-import preservation was checked from its
source; the delivered modules passed local and server compilation in deliver3.

Returned-delivery repair (X-49c64): replaced the borrowed comparison-proof route
with the direct page-homology induction described above. The graded module imports
Mathlib.Algebra.Category.Grp.AB instead of SpectralSequenceComparison. Checked the
incoming bidegree (s-r,t+r-1) and outgoing bidegree (s+r,t-r+1); for
r>max(t+1,s-a) both vanish uniformly. The new node records the unavailable search
verdict and traces its blueprint origin to the imported strict-henselization stalk
formula through the original three-node ancestry. Existing statements are unchanged.

## Second reading by D2

1. PASS. Independently diffed both modules against the read-only repository.
   The main declaration's entire signature is byte-identical, and its docstring
   is unchanged. There are no existing definition changes. The two removed public
   Mathlib imports have the declared import-change record; the sole direct importer,
   EtaleComplexCohomologyLimit, itself publicly imports both modules. The new graded
   module is imported privately, so no proof-only import is newly exposed.
2. PASS as a partial delivery. Ran lcompile.py --all on both modules: each compiled
   without errors or warnings. Compiled separate scratch copies with #print axioms
   for both declarations: exactly propext, Classical.choice, Quot.sound and sorryAx.
   Removed the scratch sources. The only delivered sorry is the named public graded
   theorem; no axioms, unsafe/opaque declarations, foreign implementations or hollow
   definitions occur. Read the induction: its zero case uses cofiltered nonemptiness;
   its successor uses B.w on both arrows to the common stage, then additivity and
   x = y + (x-y). Nat subtraction is justified by k+1 <= N.
3. PASS. Read [Stacks 0EZM](https://stacks.math.columbia.edu/tag/0EZM) and
   [015J](https://stacks.math.columbia.edu/tag/015J), and the actual continuity,
   first-page, bounded-filtration and pullback-functoriality declarations. The source
   hypotheses are qcqs stages, affine transitions and one uniform lower bound,
   precisely those retained here. The graded assertion isolates coset lifting and
   does not apply a renamed whole-class assertion. For p<a, N=0 requires the whole
   abutment to vanish; for p=a, N=1 leaves one graded lift; for p>a there are exactly
   p+1-a possible diagonal terms. Empty I is excluded by IsCofiltered. The incoming
   bidegree s-r falls below a and the outgoing t-r+1 below zero at the documented
   bound. Fresh LeanFinder search for filtered-cocone surjectivity modulo successive
   subgroups found generic colimit and quotient representative lemmas only; Loogle
   AddSubgroup, Function.Surjective found subgroup map/range results only; grep for
   hypercohomology and associated-graded surjectivity found no substitute. Also searched
   both repository Lean roots. No brief repair can close the spectral-sequence lemma.
4. PASS. The top proof now formalizes finite lifting rather than cancelling eB.
   The old nine proof dependencies are all accounted for under No longer needed;
   eight move to the open graded argument and the final-abutment comparison is replaced
   by the Mathlib filtered-colimit PreservesHomology instance. Inspected that instance
   in Mathlib.Algebra.Category.Grp.AB and its existing DAG leaf. Read sk-prop-h2's
   realized fields: this technical node realizes no unit step, and the Kummer route
   is unchanged. No globally unreachable module is claimed pruned. The plan imports
   in the open module support its documented proof; the main proof imports only its
   graded input beyond the existing signature imports.
5. PASS. The existing node changes only proof, proof_deps and proof_origin. Checked
   both proof_deps sets equal the unions of their steps' uses, and checked the new
   node's stored Lean statement verbatim against the module. The main node describes
   the actual zero/successor induction; the new node records page-homology induction,
   the uniform bound and graded lifting, with no dependency back on the main node.
   Source, searches, creation metadata, blueprint ancestry, chapter and unit are present.

This second reading changed only the report: added independent source, search,
signature, proof, DAG and axiom verification. No further Lean or node repair was needed.
