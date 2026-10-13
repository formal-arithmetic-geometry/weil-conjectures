## What changed

Proved `AlgebraicGeometry.exists_strictlyPerfect_evaluation_local_section`, keeping its
signature and both public imports byte for byte unchanged. The proof represents RN by
`Q.objPreimage`, constructs ordinary evaluation, applies the existing exact-source
comparison and strictly-perfect local Hom computations, and transports the ordinary
inverse through the comparison square. All new imports are proof-only.

The second reader removed the proposed duplicate new modules
`BoundedDualEvaluationRepresentativeComparison` and `StrictlyPerfectOrdinaryDualKFlat`
and their nodes. Their work is already supplied by the recently landed
`ExactSourceEvaluationLocalComparisons` and `StrictlyPerfectLocalHomComputations`.
The discarded drafts are retained only as scratchpad text, outside the delivery.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.exists_strictlyPerfect_evaluation_local_section`
(node `lem-pc-strictly-perfect-evaluation-local-section`). Holes added: zero.
No sorry remains in the delivered module. No new declaration or definition is added.
The proof depends on the existing open theorem
`AlgebraicGeometry.exists_exactSource_evaluation_local_comparisons`
(node `lem-pc-exact-source-evaluation-local-comparisons`) and other upstream obligations;
this does not claim independence from sorryAx.

## No longer needed

Removed direct proof imports:
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
  (`lem-pc-bounded-above-flat-kflat-site`).
- `Sheaf.Algebra.Homology.BoundedExactTermHomQuasiIso`
  (`lem-pc-bounded-exact-term-hom-quasi-iso`).
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact`
  (`lem-sc-finite-free-internal-hom-exact`).
- `Sheaf.Paper.DerivedInternalHomRestrictOpen`
  (`lem-sc-derived-internal-hom-restrict-open`).
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions`
  (`prop-pur-kinjective-resolutions-exist`).

The direct `StrictlyPerfectOrdinaryEvaluation` import is replaced by
`OrdinaryEvaluationDifferential`, which publicly imports it and provides the actual
chain-map construction. Its node remains used.

Other old proof_deps no longer directly used are
`def-pc-canonical-derived-tensor-hom-bijection`, `def-pc-perfect-complex`,
`def-pc-scheme-derived-tensor-structure`, `def-pc-tensor-complex-sheaves`,
`def-pur-derived-internal-hom` and `def-pur-hom-complex`. These definitions remain in
the statements and imported constructions; their modules are not pruned from the closure.
The exact-term Hom, finite-free exactness, restriction and resolution modules remain
needed beneath the reused computation/comparison lemmas. No closure-wide module pruning
is claimed. All four nodes directly used by the final proof are recorded in proof_deps.

## Where the brief, the DAG or earlier work was wrong

The first worker's new nodes duplicated work that has since landed in the local-retraction
branch. Independent searches using a different LeanFinder query and rg found the existing
exact-source comparison and the stronger local Hom computations. Both imports are acyclic,
confirmed by `tools/import_direction.py may`. Their shared compiled versions became
available after the green publication of 2026-10-13T12:31:37Z.
The unit `sk-thm-picard-duality` has empty realized statement/step arrays; this proof retains
the ordinary strictly-perfect evaluation route and bypasses no realized unit step.

## Second reading by X2

1. Compared the delivered module with the repository version. The existing theorem
   signature and public imports are byte for byte identical. Only proof imports,
   elaboration options, the proof and its explanation changed. No change record is needed.
2. Read the chain map and inverse-transport proof. No forbidden declaration, new data
   definition, or sorry remains in the item. Local compilation and axiom audit are recorded
   below; existing open dependencies may contribute sorryAx.
3. Reviewed both proposed split statements: the representative square did not assert
   invertibility and was mathematically a smaller model obligation, but it and the K-flat
   result duplicate existing library work. Removed both modules and both new nodes.
   The existing comparison handles arbitrary F; zero P, rank zero, empty opens and
   reversed support bounds introduce no missing hypotheses. No new statement is delivered.
4. Took the shorter existing-library route. Only three proof imports remain, each used
   in the final proof. The No longer needed section lists every displaced old proof_deps
   and distinguishes direct removal from closure-wide pruning. Checked the unit's realized
   record; its route remains unchanged. No arbitrary existence witness enters a definition.
5. Updated the item's proof steps, proof_deps and proof_origin to the final proof:
   local Hom computations, explicit ordinary evaluation, exact-source comparison,
   componentwise invertibility and the section identity. No new node remains.

Second reading changed: removed duplicate modules/nodes and private retraction helpers,
reused existing computations/comparison, constructed F and f explicitly, updated DAG,
proof explanation and report. The inverse cancellation argument was retained.

Validation: the revised proof compiled locally. A scratch-copy
`#print axioms AlgebraicGeometry.exists_strictlyPerfect_evaluation_local_section`
reported exactly `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`.
The first compile flagged only a missing explanatory comment for the heartbeat option;
that comment has been added. The dry run checks the final version and all-declaration probe.
Final dry run: `deliver3.py X2 Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalSection
--no-push` printed OK at commit `9d1ade798a`: compiles and passes preflight;
review class CODEX solely because the proof-route node file changes.
