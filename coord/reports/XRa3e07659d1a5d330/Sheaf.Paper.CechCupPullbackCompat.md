## What changed

Repaired `Sheaf.Paper.CechCupPullbackCompat` within the two allowed source/record
paths. In `cechRefinement_composition_naturality`, apply
`cechRefinement_comparison_square` directly to the specified composite refinement.
Previously this proof constructed two auxiliary comparisons and two auxiliary cup
products, then used the first conjunct of `cechCupPullbackCompat`. Those products
were irrelevant to the comparison square but their existence proofs reached
`ModuleCupKInjectiveTarget` and `GlobalTensorPullbackMonoidalNormalization`, whose
generated instance declarations collide in the returned axiom probe.

The tuplewise composition proof, homology calculation, coefficient naturality
proof, public signatures, visibility, definitions and all docstrings are preserved.
Removed the unused proof-only import `Sheaf.Paper.CechComparisonMapNaturality`.
Updated the existing node's proof, proof dependencies and proof origin to reflect
the direct comparison-square argument. No dependency modules were edited.

Checked the revised module using only single-file `lcompile.py`, including a
compilation with temporary `#print axioms` commands for all seven public theorems
(43.3 seconds, exit code 0). These commands were removed before the final-file
compile (43.5 seconds, exit code 0). The axiom output contained only `propext`, `Classical.choice`,
`Quot.sound`, and existing `sorryAx` dependencies where indicated below. No custom
axioms were introduced. No global build, server compile, delivery, push, `.check`,
or second-reading evidence was created.

## Proved and sorry left

The collision repair itself adds or closes no holes. Relative to the supplied
repository baseline, the retained original delivery closes
`AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_naturality`; it adds no holes. The following six public
statements retain complete proofs:

- `AlgebraicGeometry.Scheme.Modules.cechCupPullbackCompat`
- `AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_naturality`
- `AlgebraicGeometry.Scheme.Modules.cechRefinement_coefficient_naturality`
- `AlgebraicGeometry.Scheme.Modules.cechCup_coefficient_naturality`
- `AlgebraicGeometry.Scheme.Modules.cechRefinement_composition_naturality`
- `AlgebraicGeometry.Scheme.Modules.cechCup_refinement_naturality`

The sole local hole remains the unchanged theorem
`AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_naturality`, with blueprint
`lem-sc-picard-cech-cup-pullback-compat` and its existing proof docstring.
`cechCupPullbackCompat`, `moduleCup_coefficient_naturality`, and
`cechRefinement_composition_naturality` depend on existing holed library theorems.
The other three proved naturality theorems have only the standard three axioms.
There are no new statements, split modules, or hollow definitions.

## No longer needed

Removed the direct proof-only import
`Sheaf.Paper.CechComparisonMapNaturality` and the direct proof dependency
`lem-sc-cech-comparison-map-naturality`. Its statement dependency record is
unchanged. This repair does not claim that the module leaves the global closure.

The composition proof no longer uses `exists_unique_cechCupProduct`,
`exists_unique_moduleCupProduct`, or the auxiliary degree-zero and tensor
comparison maps. It no longer requires the derived-resolution proofs beneath
cup-product existence, including the colliding `ModuleCupKInjectiveTarget` /
`GlobalTensorPullbackMonoidalNormalization` pair. `CechCupProduct` remains a public
import because the actual cup-product statements and proofs still need its API.
All other direct imports remain needed; in particular the delivered coefficient
proof still uses `ModuleCupCoefficientResolutionMaps`, whose source import closure
contains neither conflicting module.

## Where the brief, the DAG or earlier work was wrong

The previous report claimed that ordinary local compilation established the
absence of the returned environment collision. Ordinary compilation is not enough:
axiom inspection can load proof dependencies that ordinary elaboration leaves
unloaded. The current published artifacts also allowed the original proof's local
axiom inspection, so that local result alone cannot reproduce the broken-tip probe.
The repair instead removes the source-level route to those dependencies from the
composition proof and checks every public theorem's axioms locally.

The DAG's old composition step explicitly introduced auxiliary cup products whose
values it did not use. The existing refinement comparison-square theorem supplies
exactly the needed equality, with the same hypotheses and conclusion. Applying it
directly preserves the mathematical argument and avoids the unnecessary proof
closure. Independent broken-tip verification remains the reader's responsibility;
no delivery dry run was run because it would invoke the forbidden server checks.


## Second reading by XRa3e07659d1a5d330

I independently read request.json, delivery.diff, the entire repaired Lean module,
the node and report, the stage-3 contract, the comparison-square and coefficient
resolution interfaces, and the theorem-of-the-cube unit record. Verdict: pass.

1. Interface and mathematics: compared the delivered module against the supplied
   repository using both a textual diff and stage3_delivery.diff_module. Every
   existing declaration signature, definition body, visibility and docstring is
   unchanged; no public imports change. The retained coefficient proof lifts classes
   through surjective computing-resolution class maps, constructs the paired cycle
   by Leibniz, transports the three cycles, and applies the two cup characterizations.
   The replacement composition argument applies the comparison square with exactly
   the composite refinement and given comparisons; the cochain and pullback
   composition calculations are unchanged. No assumptions or conclusions change.
2. Compilation and trust: ran only local lcompile.py with LCOMPILE_REMOTE=0, each
   invocation limited by its default 60-second compiler timeout. The sole delivered
   Lean file compiled cleanly in 43.8 seconds. A scratch copy with explicit
   #print axioms for all seven public theorems and the maintainer's complete probe
   compiled in 37.3 seconds, reported SHEAF-PROBED 7, no SHEAF-AXIOM, and only
   SHEAF-SORRY moduleCup_pullback_naturality. Its one style warning is on the
   appended tool probe, beyond the delivered source. The three Cech coefficient/
   refinement naturalities use only propext, Classical.choice and Quot.sound;
   the other four have the documented existing sorryAx dependencies. No axiom,
   unsafe, opaque, extern, implemented_by, skipKernelTC or new sorry workaround
   appears. There is no hole in a definition. The reported import collision does
   not occur in the full local axiom probe.
3. Split statements: none added. The two added private helpers prove surjectivity
   of a composite of an epimorphism with isomorphisms, and closure of cycles under
   a Leibniz pairing, respectively. These hold in degree zero and for zero sections
   as well. Library search found analogous private helpers in
   ModuleCupRealizationEvaluation and ModuleCohomologyCupProduct, not an available
   public replacement; importing their existence machinery would undo this repair's
   pruning. The sole remaining local hole is the unchanged, documented public
   moduleCup_pullback_naturality theorem; it is not claimed as proved.
4. Route and pruning: the direct comparison-square argument is shorter and uses
   the already imported theorem. No auxiliary cup-product existence is needed.
   Source import-closure checks for CechRefinementComparisonSquare and
   ModuleCupCoefficientResolutionMaps reach neither ModuleCupKInjectiveTarget nor
   GlobalTensorPullbackMonoidalNormalization. The removed direct import and proof
   dependency are fully listed above; no global module pruning is claimed. The
   sk-prop-av-cube unit statement, steps and realized record are unchanged.
5. DAG agreement: proof_deps equals the union of the steps' uses, including the
   coefficient-resolution lemma and the direct comparison square. The Lean record
   preserves all seven public declarations and the original target statement;
   proof_origin describes the actual arguments. No new node or change record is
   required for a proof-only repair.

Second-reading changes: clarified the hole ledger relative to the supplied
repository (one retained closure, zero added holes), corrected the stale DAG
sentence saying both sheaf-cup naturalities remained unproved, and restored the
repository's historical reviewed_proof metadata rather than retaining an unrelated
compiler-pass annotation from the returned delivery. No Lean changes were needed.
