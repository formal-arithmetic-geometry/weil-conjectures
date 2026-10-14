## What changed

Repaired the returned import collision within the three withdrawn scalar modules.
ScalarCupModuleCupCompatibility and ScalarExternalCupModuleComparison now import
Sheaf.Paper.ModuleCupResolutionData instead of
Sheaf.Paper.ModuleCohomologyCupProduct. Their hcup hypotheses spell out the exact
transparent definition of IsModuleCupProduct. No predicate or data definition is
duplicated, and the mathematical statements are unchanged. OldSignatureProbe.lean
checks that both previous named-predicate signatures still apply definitionally.
ScalarModuleCohomologyPullbackComparison is restored unchanged.

The external proof unfolds externalCup, applies scalarCup_moduleCup_compatibility,
and transports its two input classes with scalar_moduleCohomologyPullback_comparison
and congrArg₂. The node proof and dependencies now record precisely this reduction.
The cube unit route is unchanged; its realized list does not contain these nodes.

## Proved and sorry left

The complete reduction closes the item's one original hole:
AlgebraicGeometry.Scheme.Modules.scalarExternalCup_moduleComparison
(lem-sc-scalar-external-cup-module-comparison).
This is a decomposition through the two prerequisites retained from the returned
delivery, not a proof independent of their sorries. This repair adds no new holes.

Every retained sorry:

- AlgebraicGeometry.Scheme.Modules.scalarCup_moduleCup_compatibility
  (lem-sc-scalar-cup-module-cup-compatibility).
- AlgebraicGeometry.Scheme.Modules.scalar_moduleCohomologyPullback_comparison
  (lem-sc-scalar-module-cohomology-pullback-comparison).

Each remains a named public theorem with its source and complete proof in words.
There are no sorries in definitions or in the external comparison proof.
The batch axiom probe reports propext, Classical.choice, Quot.sound and sorryAx,
the latter from the two retained prerequisites. No additional axiom is introduced.

## No longer needed

Removed the public import Sheaf.Paper.ModuleCohomologyCupProduct from both the scalar
cup comparison and the external comparison. The proof no longer requires its node
def-sc-module-cohomology-cup-product as an executable dependency: the defining
formula is stated directly using def-sc-module-cup-resolution-data. Its existence
and uniqueness proof and the private ModuleCupPairingExists and
ModuleCupResolutionInvariance branches are unnecessary for this comparison.
In particular, this delivery no longer reaches the colliding
ModuleCupNaiveDerivedCompatibility and GlobalTensorPullbackMonoidalNormalization
branches through ModuleCohomologyCupProduct.
This is pruning from these modules, not a claim that those branches are absent
from every other target path. No other direct import is removed.

The scalar cup node drops def-weil-pbc-module-cohomology-fmap from proof_deps:
no pullback is used in that theorem. The pullback comparison node drops
 def-sc-module-cohomology-cup-product: no cup is used in that theorem.

## Where the brief, the DAG or earlier work was wrong

The prior attempt treated an upstream import edit as the only possible repair.
The public scalar hypotheses need just the transparent cup characterization, not
the existence theorem housed in the same module. Expanding that characterization
preserves its full strength while removing the collision without an upstream edit.

All six return points are repaired:

1. The cup comparison axiom/sorry probe now runs in non-module mode.
2. A non-module importer of ScalarCupModuleCupCompatibility now compiles.
3. The external comparison axiom/sorry probe now runs in non-module mode.
4. The external comparison imports its repaired cup prerequisite and compiles.
5. A non-module importer of ScalarExternalCupModuleComparison now compiles.
6. The external comparison imports the unchanged pullback prerequisite and compiles.

Evidence is in scratchpad/repair-verification/lean: the three individual non-module
import probes, BatchProbe.lean importing all three and printing their axioms,
and OldSignatureProbe.lean checking calls with the previous hypotheses. All compile
against this delivery's .lbuild. The three source modules compile in import order.

Change record: coord/changes/scalar-external-cup-module-comparison.md.

## Second reading by R1

1. **Statements and interfaces.** I compared all three delivered declarations with the
DAG records and the prior returned signatures. The target conclusion and all quantified
objects are unchanged. The two `IsModuleCupProduct` hypotheses are expanded exactly by
the transparent definition from `ModuleCohomologyCupProduct`; the change record documents
this definitional interface repair.

2. **Compilation and axioms.** I compiled all three modules in import order with
`lcompile.py --all`; they compile without errors. The only remaining `sorry`s are the
two named prerequisite theorems listed above, and no definition contains `sorry`.
The batch axiom probe reports only the standard axioms together with `sorryAx` from
those two retained prerequisite theorems. No forbidden declaration was found.

3. **Split statements.** The two retained prerequisite theorems are existing DAG nodes,
strictly below the target and required by the reduction. Their statements are true
resolution comparison claims, have source and proof docstrings, and no duplicate
predicate or hollow definition was added. The external target itself is closed by
composition, with no additional split-off statement.

4. **Pruning and route.** The external proof unfolds `externalCup`, applies the scalar
cup comparison, and transports both inputs with the scalar/module pullback comparison.
The pullback and cup-product existence modules are not needed by this proof; their
imports and proof dependencies were removed as recorded under `## No longer needed`.
The unit route record is unchanged and this target is not listed as a realized cube step.

5. **DAG agreement and search.** I checked that each node's `proof`, `proof_deps`, and
`proof_origin` match the Lean reduction and that the node statements match the delivered
interfaces. Mathlib/library searches found no existing declaration for these project
specific comparisons. The dry-run delivery checks the node, change record, report, and
all source modules together.

**Changes made during second reading:** no Lean proof changes were needed. I added this
review section; the delivered import repair and transparent-hypothesis adaptation remain
as documented in `coord/changes/scalar-external-cup-module-comparison.md`.
