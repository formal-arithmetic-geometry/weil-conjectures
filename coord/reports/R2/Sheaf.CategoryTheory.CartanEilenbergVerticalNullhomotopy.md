## What changed

Repaired the returned delivery by importing
`Sheaf.CategoryTheory.CartanEilenbergComparisonCycleStage` with proof-only
`import all`. Its private helpers are available without changing either module's
public interface. Removed the duplicate declarations `CategoryTheory.bi_fac`,
`CategoryTheory.bi_factor`, `CategoryTheory.bi_zero`, `CategoryTheory.row_exact`,
`CategoryTheory.supportedIso_zero`, and `CategoryTheory.supportedIso_naturality`.
Also removed the duplicate private constructions `bi`, `row`, `rowHom`, and
`supportedIso`. The proof now uses the existing constructions and lemmas directly;
no renamed copies or replacement obligations were added.

The original delivery proves
`CategoryTheory.cartanEilenberg_vertical_nullhomotopy` with its complete signature
and original public imports preserved. Its other proof-only imports are
`Sheaf.CategoryTheory.Abelian.CompatibleNullHomotopyAssembly`,
`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution`, and
`WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns`.

The remaining private helpers construct cycle-column-boundary short exact
sequences, derive column quasi-isomorphisms and injectivity, and apply
`CategoryTheory.exists_compatible_nullHomotopies` twice at each horizontal degree.
The final induction retains the next boundary homotopy, so successive column
homotopies commute with the horizontal differential. Negative columns and
non-successive indices use the first-quadrant and shape hypotheses.

Updated the existing node's proof and proof origin to identify the reused helper
infrastructure. Its proof dependencies still name the compatible assembly lemma;
no use of the comparison-cycle-stage theorem itself is required. No other module,
existing public statement, definition, or visibility was changed.

## Proved and sorry left

Closed one hole: `CategoryTheory.cartanEilenberg_vertical_nullhomotopy`
(blueprint `lem-sp-ce-vertical-nullhomotopy`). No `sorry` remains in the item.
Added zero holes and zero new public obligations. All remaining private helpers
are proved. A scratch copy of the repaired module compiled with an axiom audit
reporting only `propext`, `Classical.choice`, and `Quot.sound`. This is a proof
from existing proved declarations, not a decomposition.
The compatible assembly dependency is
`CategoryTheory.exists_compatible_nullHomotopies`
(blueprint `lem-sp-ce-compatible-homotopy-assembly`).

## No longer needed

No original import was removed. All proof imports are used. The six duplicated
helper lemmas and four duplicated private constructions listed above are pruned
from this module and reused from `CartanEilenbergComparisonCycleStage`.

The planned direct dependency
`lem-weil-pbc-acyclic-map-to-injective-nullhomotopy` and its
`Mathlib.Algebra.Homology.HomotopyCategory.KInjective` route are not needed and
were removed from this node's proof dependencies. The proved source comparison
construction replaces that route. This does not claim that the generic acyclic-map
node is unused by other parents. No library module is withdrawn. The compatible
assembly dependency remains necessary; no other planned dependency is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated six private helper statements already proved in
`CartanEilenbergComparisonCycleStage`. They and their underlying duplicate
constructions have been removed. A compile probe confirmed that `import all`
exposes the existing private API, and the import-direction check found no cycle.

No mathematical statement error was found. The planned start with the zero
boundary homotopy is unnecessary: the row comparison already supplies an initial
boundary homotopy. The row-comparison step uses the existing source-library
construction without reindexing into integer degrees or using K-injectivity.
The unit route and target statements are unchanged.

The previous second-reading record predates this repair and has been removed so
that the next reader can record their review of the repaired delivery.

The dry run initially waited on the shared source-index builder lock. It was
restarted with the supported `WEIL_DELIVERY_CACHE_DISABLE=1` setting, which runs
the normal source scans; all delivery checks remain enabled. No tool was edited.

## Second reading by R2

1. **Signatures.** Compared the delivered module with the repository version.
   The existing public theorem signature is unchanged byte for byte. Added
   imports are proof-only; all added helpers are private. No existing definition
   or visibility changes. Verdict: pass.
2. **Proof.** The module compiles cleanly with the prescribed `lcompile.py`.
   It has no remaining `sorry` and no forbidden declaration mechanism. The
   scratch axiom audit was repeated and returned exactly `propext`,
   `Classical.choice`, and `Quot.sound`. Its data constructions
   are explicit; no arbitrary object is selected from an unproved existence
   theorem. Verdict: pass.
3. **Split statements.** There are no new nodes or split-off statements. The
   helper constructions from `CartanEilenbergComparisonCycleStage` are reused
   through proof-only `import all`, and no copy of their declarations remains.
   Verdict: pass.
4. **Route and pruning.** Read the proof top down: supported row comparison,
   compatible assembly for B → Z → H and Z → I → B, induction retaining the
   next boundary homotopy, then negative and nonsuccessive indices. This retains
   the unit route. The old direct acyclic-map dependency is listed under
   `No longer needed`; no original import was removed. Verdict: pass.
5. **DAG agreement.** The node's statement and Lean signature are unchanged;
   its proof steps and proof origin describe the actual row comparison and
   assembly induction. Its sole named proof dependency is the assembly node,
   whose theorem is directly used. The cycle-stage theorem itself is not used.
   Verdict: pass.

The second reader also repeated a semantic Lean Finder search for a null-homotopy
commuting with the horizontal differential. Its hits were ordinary injective and
projective resolution comparison homotopies, which do not supply horizontal
compatibility. A local source search found no duplicate of the remaining private
helper statements. No shorter direct theorem replacing the assembly was found.

Two documentation issues predate this delivery. The existing theorem docstring
still describes the old acyclic-map route and zero-boundary start; the actual
route is correctly recorded above and in the updated node. Also the node's
recorded unit, `sk-prop-av-pqf-finite`, concerns proper quasi-finite morphisms and
has empty `realized.statement` and `realized.steps` entries. This is an inherited
metadata mismatch, not a route change made by this proof. The unit record is
unchanged; this item is a tool for the spectral-sequence comparison argument
identified by its blueprint ancestry. Neither issue affects the Lean statement
or the checked proof.

Second reading changed only the report: recorded the review, its checks, and the
inherited documentation issues. No Lean repair was necessary.
