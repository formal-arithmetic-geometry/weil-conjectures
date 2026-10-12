## What changed

Reduced `AlgebraicGeometry.formal_functions_stalk_structureSheaf` to the existing general
`formal_functions_stalk` and a new degree-zero dictionary. The proof establishes coherence
of the structure sheaf, applies the general theorem, completes the stalk equivalence,
transports the system isomorphism to its limit, and verifies the specified section formula.
Both existing signatures and docstrings are unchanged. Added proof-only imports of the
new dictionary, Mathlib completion functoriality, and the source-library locally-free and
quasi-coherent modules. The dictionary has proof-only imports for the existing proved
tensor-unit identification and the planned degree-zero cohomology and presheaf comparisons.
The general `formal_functions_stalk` is untouched. The node records the completed
specialization separately from its still-planned nine-step general argument.

## Proved and sorry left

Closed: `AlgebraicGeometry.formal_functions_stalk_structureSheaf`
(node `lem-weil-pbc-formal-functions-stalk`), by reduction, not an independent sorry-free proof.

Existing hole left: `AlgebraicGeometry.formal_functions_stalk`
(node `lem-weil-pbc-formal-functions-stalk`).

Added hole: `AlgebraicGeometry.formalFunctions_degreeZero_dictionary`
(node `lem-weil-pbc-formal-functions-degree-zero-dictionary`).
One upper hole closed, one lower hole added: net zero; this is a decomposition.
The new statement concerns only degree-zero identifications and their germ formula. It has
no properness or Noetherian hypothesis and makes no assertion about an isomorphism from a
completion to a limit. Its conclusion is therefore strictly a part of the argument.

## No longer needed

Removed direct proof imports unused by the implemented specialization:

- `Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge`
- `Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`
- `Sheaf.AlgebraicGeometry.CoherentFormalModule`
- `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportPullback`
- `Sheaf.AlgebraicGeometry.FlatBaseChangeMapSections`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMap`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`
- `Sheaf.AlgebraicGeometry.QuotientBaseChangeIdeal`
- `Sheaf.AlgebraicGeometry.SpecLocalRingCanonicalMorphism`
- `Sheaf.AlgebraicGeometry.TensorPullback`
- `Sheaf.AlgebraicGeometry.TheoremFormalFunctions`
- `Sheaf.Paper.HigherDirectImagePresheaf`
- `Sheaf.Topology.PresheafModuleStalkFunctor`
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`

The general theorem remains open, so its nine-step planned dependencies remain in the DAG.
No claim is made that the mathematics of those steps has been bypassed. These direct import
edges are unnecessary for the completed specialization. Some modules remain reachable
through other imports (including definitions); no claim of global unreachability is made.
No unit statement or realized proof step is bypassed; `sk-thm-p1` is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The degree-zero paragraph omitted the actual interface
identifications connecting the derived stalk and tensor-pullback cohomology with the ordinary
pushforward stalk and sections. The new dictionary isolates exactly that missing glue.
The local checkout contains literature lists but not the cited TeX files; Stacks Tags 02OD
and 01FB were read online. LeanSearch returned an internal-server error, recorded as
unavailable. LeanFinder and local Mathlib grep found generic stalk and right-derived-zero
facts, but no exact dictionary with this predicate and these systems. Blueprint searches for
02OD, 01FB and the degree-zero formal-functions phrase found no matching blueprint node.

Edge cases checked: the dictionary requires no positive-degree assertion, works for arbitrary
scheme morphisms, and the empty fibre has zero sections and zero degree-zero cohomology.
Its germ formula is conditional on the explicitly supplied whole-fibre containment. At n=0
the quotient is by m^1, consistently with the existing positive-level convention.
No arbitrary data is defined from an unproved existence theorem.

## New nodes

`lem-weil-pbc-formal-functions-degree-zero-dictionary`, module
`Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroDictionary`, states the ordinary-to-derived
stalk equivalence and the natural identification of degree-zero unit cohomology with fibre
sections, including the canonical germ formula. The docstring and node give the resolution
augmentation, tensor-unit and restriction-cancellation argument. Source: Stacks 02OD,
01E4 and 01FB. No interface change or change record is needed.


## Second reading by B2

1. **Visible interface: PASS.** Diffed the existing module against the repository and
   compared both theorem signatures byte for byte. They and their docstrings are unchanged;
   there are no definition changes, added hypotheses, weakened conclusions, or change records.
   All added imports are proof-only. No other existing Lean module is delivered.
2. **Lean proof and trust: PASS as a decomposition.** Compiled both modules in import order
   using lcompile.py, without errors or warnings. Printed axioms of both existing theorems
   and the dictionary in a scratch module; only the three permitted axioms and sorryAx occur.
   The two whole-proof holes are precisely formal_functions_stalk and
   formalFunctions_degreeZero_dictionary; there are no data definitions or forbidden commands
   in the new module. The specialization composes completion and limit isomorphisms in the
   correct directions; map_of and isoOfNatIso_hom_π prove the projection formula.
3. **Split-off statement: PASS.** Read FormalFibreCohomology, FlatBaseChangeOpenChoices,
   ModuleCohomologyFMapBasicProperties and the cited Stacks Tags
   [02OD](https://stacks.math.columbia.edu/tag/02OD),
   [01E4](https://stacks.math.columbia.edu/tag/01E4), and
   [01FB](https://stacks.math.columbia.edu/tag/01FB).
   The dictionary asserts only degree-zero identifications and their canonical germ formula;
   it neither assumes properness nor supplies the completion comparison. It is a strict
   intermediate part, not a renaming of either existing theorem. Checked empty fibres,
   identity maps, and n=0 (quotient by m, not by m^0). The containment hypothesis makes the
   restriction open equal to top. Augmentation-preserving restricted injective resolutions
   and the pinned unit square supply the choices required by IsFormalFunctionsTheta.
   New LeanFinder and Loogle searches, and rg searches of both library roots, found no exact
   dictionary. Generic rightDerivedZeroIsoSelf, the proved tensor-unit isomorphism, and stalk
   restriction identities are available; the tensor-unit fact is now used in the node plan.
4. **Shortest route, imports and unit: PASS.** The existing general theorem is used directly;
   the degree-zero coherence proof uses the library criterion and finite local freeness.
   No short existing theorem closes the remaining dictionary's resolution/germ compatibility.
   The 16 removed direct imports are exactly those listed above. All old proof_deps remain
   in the still-open general theorem's nine-step plan; consequently no old dependency node
   or globally unreachable module is claimed pruned. Inspected sk-thm-p1.realized: neither
   its statement nor its four realized step lists are changed or bypassed. Added only
   proof imports needed for the dictionary's remaining proof plan.
5. **DAG agreement: PASS after repair.** The parent node separately records the implemented
   specialization and the pending general proof. Each node's proof_deps is exactly the union
   of its step uses. The new node has its source, natural-language proof, searches, split
   status, creation metadata, blueprint ancestry, chapter/unit and verbatim Lean signature.
   Corrected the direction of the augmentation in its first step, and added the existing
   lem-weil-pbc-module-pullback-structure-sheaf to the second step and proof_deps.

Second reading changed the dictionary's proof-only imports and DAG plan/search records,
and this report. No Lean statement or completed proof was rewritten. Closed one of the
item's two holes and added one lower hole: decomposition, net zero.
