## What changed
Proved `AlgebraicGeometry.IsCurve.assertions_of_reduction` without changing its signature.
Added and proved `AlgebraicGeometry.IsCurve.assertions_of_universalHomeomorphism`:
cohomology equivalences transfer C1-C5, and commuting pullback squares transfer C6-C8.
Corrected three reversed pullback equalities in the previous sandbox attempt.
The reduction proof supplies the curve instance using the homeomorphism on spaces.

## Proved and sorry left
The original module had one sorry, `AlgebraicGeometry.IsCurve.assertions_of_reduction`,
which is now proved. The new generalized transfer theorem is also proved.
No sorry remains in either delivered module; existing imported declarations retain
whatever proof status they already have.
Both modules compile cleanly with `lcompile.py --all`.

## No longer needed
Removed direct imports `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`,
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance` from the item.
Topological invariance remains used through the generalized transfer module.
The separate planned nodes `lem-weil-pbc-cohomology-pullback-functorial` and
`lem-weil-pbc-inverse-image-composition` are not direct dependencies of this route;
the square transport theorem packages their needed compatibility.
`def-weil-pbc-primary-torsion` is not a separate proof dependency: primary torsion
transport is proved directly using the geometric stalk linear equivalence.
No claim is made that these nodes are unreachable from all other targets.

## Where the brief, the DAG or earlier work was wrong
The previous report incorrectly said the generalized transfer theorem remained sorry.
Its proof was present but failed at three square equalities, now corrected.
The prior new-node proof dependencies incorrectly cited reduction properties for a
general universal homeomorphism. They now record the actual comparison tools.
Removed the obsolete change record: adding a new proved theorem changes no existing
statement or definition. Removed the stale second-reading section; a fresh second
reader must review this completed proof.

## New nodes
`lem-weil-pbc-universal-homeomorphism-assertions` records the proved transfer theorem.
Its statement includes closed immersion and universal homeomorphism, which implies
surjectivity; no reducedness, torsion, constructibility, or properness is added to
the theorem's hypotheses. Those conditions are transported only in the assertions
which assume them. Empty curves and all cohomological degrees are included.

## Second reading by W2
1. Compared the item with the repository using `diff`: its existing declaration
   signature and docstring are byte for byte unchanged. The other module is new;
   there are no changed definitions, hypotheses, conclusions, or target statements.
2. Both delivered modules compile cleanly through `lcompile.py --all`. Neither
   contains `sorry` or forbidden declarations. Scratch copies with `#print axioms`
   show only `propext`, `Classical.choice`, `Quot.sound`, and inherited `sorryAx`:
   these proofs use existing open comparison results, so this delivery closes the
   local theorem bodies, not their whole transitive axiom closure.
3. No statement is split off with `sorry`. The new transfer theorem is proved
   component by component, rather than assuming a renamed reduction statement.
   Checked identity immersions, empty curves, zero sheaves, degree zero, positive
   characteristic primary torsion, and nonreduced field base changes. The stalk
   equivalences preserve the same torsion witnesses; square transport gives the
   actual canonical pullback map. Searches with a different LeanFinder query,
   Loogle for bijections and additive equivalences, and `rg` across the curve
   modules found comparison tools but no existing bundled transfer theorem.
4. The proof uses the existing topological invariance, coefficient-forgetting,
   constructible pullback, and commuting-square tools. All proof-only imports are
   plain imports and each supplies a used declaration. Read the `sk-thm-p1`
   `realized` record: this auxiliary reduction replaces no unit statement or step.
   The old direct dependency `prop-weil-pbc-universal-homeomorphism-topos` remains
   needed through the new transfer theorem; the other three removed direct
   dependencies are listed under No longer needed. None is claimed globally
   unreachable.
5. Checked both node proofs, dependency unions, origins, declarations, and Lean
   signatures against the code. Corrected the reduction node's recorded signature,
   which contained literal Unicode escape strings. Removed copied Q2 review and
   landing stamps from the new node, made its statement self-contained with the
   coefficient ring and dependency citations, and removed its unused reduction
   definition statement dependency. Its proof dependencies match the actual proof.

Second reading changed node metadata and this report only; the compiled Lean proofs
were retained. No new sorry, statement correction record, or adapted module is needed.
