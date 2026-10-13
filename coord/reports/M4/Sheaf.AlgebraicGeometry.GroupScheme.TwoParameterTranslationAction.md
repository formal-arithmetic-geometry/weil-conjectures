## What changed

Repaired `Sheaf.AlgebraicGeometry.GroupScheme.TwoParameterTranslationAction` after the
landing was rejected by `tools/import_prune_check.py`. Removed the private declaration
`translation_fst`, whose statement duplicated the existing `dualNumbers_appLE_fst` statement
in `Sheaf.AlgebraicGeometry.GroupScheme.InvariantCoefficients`. Its proof is now an inline
local generic fact inside `translation_appLE`, so no duplicate module declaration is emitted.
All public definitions, theorem signatures, and the completed proof remain unchanged. The existing
local elaboration change record is `coord/changes/two-parameter-translation-local-elaboration.md`.

## Proved and sorry left

Closed the one repository hole:
`AlgebraicGeometry.GrpObj.twoParameterRightTranslation_commutator_app`.
Proved 1 of 1 original holed declarations; holes added: none; split off: none.
No `sorry` declarations remain in the delivered module. The theorem and its dependencies
use only `propext`, `Classical.choice`, and `Quot.sound` (no `sorryAx`).

## No longer needed

The private helper declaration `translation_fst` is removed. Its standalone duplicate node
was never present. No original import, proof-dependency node, or module is pruned:
`def-sc-group-scheme` and `def-sc-dual-numbers` both remain used. The added plain proof import
`WeilConjectures.AlgebraicGeometry.DualNumbersBaseChange` supplies the pullback theorem;
`InvariantCoefficients` imports it privately, so its declaration requires this direct import.
The public `InvariantCoefficients` import supplies the existing signatures and coefficient
operators. Both delivered imports are needed.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery introduced a private helper with the same statement as the existing
`dualNumbers_appLE_fst` declaration. Although the existing declaration is private and cannot be
referenced by name from this module, the duplicate declaration still violated the import-prune
check. Keeping the argument as a local proof avoids exporting or declaring the duplicate while
preserving the theorem proof.

## Earlier second reading (a previous round; superseded)

Pending independent second reading of the repaired delivery.

## New nodes

None.

## Second reading by M4

1. **Interface: pass.** Read the full repository/sandbox diff. Compared the three existing
   definitions (`twoParameterRightTranslation`, `epsilonSectionAction`, `deltaSectionAction`)
   byte for byte, including their bodies, and compared the entire existing theorem signature
   before `:= by` byte for byte. All match. Only private helpers, the proof import, local
   elaboration commands documented in the existing change record, and the theorem proof
   were added. No target statement, public definition, hypothesis, universe, or visibility
   changed.
2. **Proof: pass.** Compiled the delivered file with `lcompile.py` without errors or warnings.
   Compiled an exact scratch copy with `#print axioms` for all four existing public
   declarations and for the pullback, coefficient-addition, faithful-additivity, and
   reduction dependencies. The theorem and geometric definitions use only `propext`,
   `Classical.choice`, `Quot.sound`; the two coefficient operators use no axioms. No
   `sorry`, forbidden declaration, or hollow definition occurs in the delivered module.
   In particular the double lift is explicitly built using two proved pullback lifts.
3. **Split statements: pass (none).** No new hole or split-off module is introduced. Read
   the local geometric and ring helpers: the lift preserves both parameters; its
   composition law follows from pullback extensionality and group associativity; the
   four-coefficient decomposition holds for every commutative ring, including the zero
   ring and characteristic two. The inverse coefficient follows from the existing
   proved `invariantCoefficient_mul`, rather than a new assumption. Empty opens/schemes
   require no extra hypotheses, and identity points give zero coefficient operators.
4. **Route and pruning: pass.** Read the Lie-ring source paragraph in
   `WeilConjectures/AlgebraicGeometry/GroupScheme/Lie/Bracket.lean` and the pullback
   construction in `DualNumbersBaseChange.lean`. The proof calculates the actions of
   the epsilon and delta factors on constants, proves that both parameters are fixed,
   extends to all four coefficients, and composes the factors in the correct
   contravariant order. Searches with `rg` over `lean/Sheaf`, the group-scheme upstream
   files and `DualNumbersBaseChange.lean`, and an independent `msearch.py ... grep`
   query `dualNumbers.*(app|map)|commutator.*(section|pullback)` found no accessible
   replacement for the full identity. The existing generic first-coefficient theorem
   and projection-section helper are private to their modules; the inline local fact
   appropriately avoids the earlier duplicate declaration. Both imports are necessary
   and correctly public/plain. All original `proof_deps` remain used, so no node is
   omitted from No longer needed. Read `dag/units/sk-d-tangent.json`: its realized
   statement and steps are empty and remain untouched; this supporting proof does not
   bypass a unit.
5. **DAG: pass.** Read the delivered node and its diff against the repository. Its
   statement and Lean signature are unchanged. The four proof steps describe the
   implemented pullback lifts, composition, parameter and coefficient calculations,
   and inverse/composite section formulas. Their uses union is exactly `proof_deps`:
   the two original definition nodes, `lem-ag-dual-numbers-projection-pullback`, and
   `lem-ag-invariant-coefficient-add`. The latter two name the actual existing proved
   declarations used. `proof_origin` correctly identifies the implemented argument.
   No new node requires the new-node fields.

Second-reading changes: clarified the closed/added hole counts and import/pruning
accounting in this report; regenerated and compiled the scratch axiom check from the
current repaired module. No Lean proof, signature, definition, or DAG repair was needed.
Change record: `coord/changes/two-parameter-translation-local-elaboration.md`.
