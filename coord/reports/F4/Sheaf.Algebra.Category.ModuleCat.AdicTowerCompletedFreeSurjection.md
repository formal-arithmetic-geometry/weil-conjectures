## What changed

Proved `ModuleCat.adicTower_completedFreeSurjection` in
`Sheaf.Algebra.Category.ModuleCat.AdicTowerCompletedFreeSurjection`, preserving its
signature and visibility. Added two fully proved private helpers:
`ModuleCat.coordinate_surjective` and `ModuleCat.compatible_preimages`.

The proof lifts the basis images of a finite free presentation of `T_0` into the
limit using Mathlib's surjective zeroth-projection theorem. A direct square-zero
argument propagates presentation surjectivity through each successor: if
`J = I^(n+1)`, then `J^2 T_(n+1) = 0` and the presentation range plus `J T_(n+1)`
is the whole module. Recursively correcting coefficients by elements of
`I^(n+1) A^d` produces an explicit adic Cauchy sequence for every limit element.
Finally, `AdicCompletion.piEquivFin` and finite linear combinations construct the
completed-ring linear map. The given scalar residue equation verifies its
coordinate values and proves surjectivity by limit extensionality.

Added proof-only imports of
`Mathlib.RingTheory.AdicCompletion.Functoriality` and
`Mathlib.RingTheory.Finiteness.Cardinality`. The second reader removed redundant
imports of `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic` and
`Mathlib.LinearAlgebra.Finsupp.LinearCombination`; their declarations are already
available through the retained imports.
Updated the item's DAG proof, proof dependencies and proof origin to this route.
No public interface, definition, target, or other module changed.

## Proved and sorry left

Closed the sole original hole:
`ModuleCat.adicTower_completedFreeSurjection`
(node `lem-weil-pbc-adic-tower-completed-free-surjection`).

Both private helpers are proved. No holes remain and no holes were added.
This is a proof, not a decomposition. Local compilation was clean, and
`#print axioms ModuleCat.adicTower_completedFreeSurjection` reported exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The successor estimate also covers `n = 0`, where `2(n+1) = n+2`.
The Cauchy sequence has its degree-zero term explicitly set to zero, so the
completion's exponent-zero quotient is handled. The construction accepts
`d = 0`, either extreme ideal, and the zero ring without additional hypotheses.
All choices are made in proofs from proved existence statements; no definition
chooses data from an unproved existence theorem.

## No longer needed

Removed both original proof-only imports:

- `Sheaf.Algebra.Category.ModuleCat.TowerLimitExactSurjectiveKernels`, node
  `lem-weil-pbc-tower-limit-exact-surjective-kernels`. Its general exactness
  theorem and its all-coordinate projection theorem are unused. Only the
  zeroth-coordinate projection is needed, supplied directly by Mathlib.
- `Sheaf.RingTheory.NakayamaNilpotent`, node `lem-weil-pbc-nakayama-nilpotent`.
  The successor square-zero range argument proves precisely the needed case.

The former import's auxiliary modules and nodes are consequently not needed
by this proof either:
`Sheaf.Algebra.Category.ModuleCat.TowerLimitInducedMaps`
(`new-tower-limit-induced-maps`) and
`Sheaf.Algebra.Category.ModuleCat.TowerLimitExactCoordinateMaps`
(`new-tower-limit-exact-coordinate-maps`).
The categorical free quotient tower, its presentation-kernel tower and a
categorical identification of its limit with the free completion are also
unnecessary; the explicit coefficient sequence replaces that glue.

These are removed dependencies of this item, not claims that the named modules
are unreachable from every other target. The finite-generation definition
`def-weil-finitely-generated-module` remains a dependency. No node realizing
any statement or step in `dag/units/sk-thm-p1.json` is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original plan is valid but asks for more
machinery than needed here. Surjectivity at a successor level follows directly
from its square-zero kernel ideal, avoiding identification of `T_n / I T_n`
with `T_0`. The completed-ring linear map can be constructed before proving
surjectivity, using Mathlib's completed finite-product equivalence. Explicit
Cauchy recursion then replaces general tower-limit exactness.

The existing public docstring is retained verbatim as the original source proof
sketch; the updated DAG and the private-helper comments describe the implemented
shorter route. The three search services were tried: LeanFinder found completion
lifting tools, Loogle found `AdicCompletion.piEquivFin`, and LeanSearch was
unavailable (Internal Server Error). Logged grep and local source searches found
no independent existing theorem proving this full statement. No new nodes or
forced adaptations were needed.

## Second reading by F4

1. Compared the entire delivered module with the repository using `diff` and
   compared the existing theorem signature byte for byte, from its name through
   its conclusion. It is unchanged; the original public docstring, visibility,
   universe and public imports are unchanged. There are no other delivered Lean
   modules, definitions, statement changes or change records. Verdict: pass.
2. Independently compiled the module through `lcompile.py`, then a scratch copy
   with `#print axioms` for the target and both private helpers. All three depend
   exactly on `propext`, `Classical.choice`, and `Quot.sound`. Scanned for `sorry`,
   `axiom`, `unsafe`, `opaque`, `implemented_by`, and `extern`: none. The finite
   generating map and recursive coefficient witnesses come from proved
   surjectivity statements inside proofs, and q is a concrete linear combination
   map. No data are chosen from an unproved theorem. Verdict: pass.
3. No statements are split off and no holes are added. Read both private helpers:
   the successor induction uses J squared annihilating the module, with
   2(n+1) >= n+2 also at n=0; coefficient correction lifts ideal multiples
   through a surjective linear map. The shifted Cauchy sequence handles exponent
   zero by the top submodule. For I=bottom all transitions are isomorphisms and
   corrections vanish; for I=top the annihilation hypotheses force all levels
   to vanish. For d=0 the same range argument forces every level to vanish;
   the zero ring presents no exception. Both helpers are proved, strictly
   intermediate claims, not renamed copies of the target. Verdict: pass.
4. Read the original Nakayama and tower-limit dependency declarations, and
   searched the library for completion/limit surjectivity and compatible lifts.
   A fresh logged `msearch.py ... grep` query for `AdicCauchySequence|surjective_π|
   piEquivFin` confirms the Mathlib ingredients; no independent full result
   was found. The direct square-zero calculation avoids general quotient
   Nakayama, and coefficient correction avoids categorical kernel towers.
   Checked each added proof import by removing it in a scratch copy.
   Functoriality and Cardinality are necessary; ConcreteCategory.Basic and
   Finsupp.LinearCombination are redundant and were removed together, then
   the resulting module compiled cleanly. The report lists both old proof_deps
   removed and the unchanged finite-generation dependency. Read
   `dag/units/sk-thm-p1.json`: none of the pruned nodes realizes its statement
   or a step, so the unit route is preserved. Verdict: pass after import cleanup.
5. Compared the old and new node records. Only proof, proof_deps and proof_origin
   differ. Read the new four steps against the Lean: generator lifting,
   square-zero range induction, compatible coefficient recursion, and the
   completed linear combination with hscalar and coordinate extensionality
   describe the actual proof. The sole retained proof_dep is finite generation;
   no Sheaf proof dependency is used. No new nodes require checking. Verdict:
   pass.

Second reading changed only the two redundant proof imports and this report.
The proof and DAG route were retained. Independently verified: one original
hole closed (`ModuleCat.adicTower_completedFreeSurjection`), zero holes added.
