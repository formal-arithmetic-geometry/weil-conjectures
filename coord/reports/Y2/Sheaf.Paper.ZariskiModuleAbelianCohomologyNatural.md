## What changed

Proved `AlgebraicGeometry.zariskiModuleAbelianCohomologyNatural_components` in
`Sheaf.Paper.ZariskiModuleAbelianCohomologyNatural`. All existing signatures and public
imports are preserved. The previously proved upper natural-isomorphism theorem is unchanged.

A module injective resolution becomes an exact, termwise-acyclic abelian resolution after
forgetting. Compare both theories with its section complex, using the existing natural
Ext-to-derived-sections comparison. Lift each module morphism to the chosen resolutions;
combine the injective-resolution, homology-forgetting, acyclic-resolution, and Ext naturality
squares. A proved private helper `resolutionForget_naturality` handles the generic
forgetting square without unfolding ringed-space definitions. Update the component node's proof, proof dependencies, and proof origin accordingly.
The module compiles through `lcompile.py`; the local heartbeat setting accounts for comparison
of the definitionally equal section complexes.

## Proved and sorry left

Closed the one baseline hole:
`AlgebraicGeometry.zariskiModuleAbelianCohomologyNatural_components`
(node `new-zariski-module-abelian-cohomology-components`).
`AlgebraicGeometry.zariskiModuleAbelianCohomologyNatural` was already proved and stays proved.
No sorry remains in the delivered module. No holes are added and no statements are split off.

The proof uses the existing named theorem `CategoryTheory.acyclicComparison_naturality`
(node `lem-sc-acyclic-comparison-natural`), which still has its own sorry in the baseline;
its module is imported, not changed. This is a proof from existing stated dependencies,
not a claim that the target closure is now axiom-free.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`: use the proved source-library
  forgetful exactness instances directly; node `lem-weil-pbc-module-sheaves-colimits-forgetful`
  is no longer a proof dependency of this component node.
- `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives`: use the ringed-space result;
  node `lem-weil-pbc-scheme-modules-enough-injectives` is not needed by this proof.
- `Sheaf.Paper.PQFCohomology`: no derived-category compatibility theorem is needed;
  `pqf-def-cohomology` remains a statement dependency, not an added proof dependency.
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence`: no direct use of
  the long exact sequence; it remains reachable through the acyclic-resolution dependency.
- `Sheaf.CategoryTheory.Sites.CohomologyDerivedEvaluation`: replace its objectwise positive
  comparison with `Sheaf.CategoryTheory.Sites.CohomologyRightDerivedSections`, which gives
  the needed functor-level comparison in every degree. Node
  `new-sheaf-cohomology-derived-evaluation` is unnecessary for this proof.
- `Sheaf.Topology.RingedSpaceModuleEnoughInjectives`: remove the redundant direct import;
  its theorem and node `lem-sc-ringed-space-module-sheaves-enough-injectives` remain used
  through the public import of `RingedSpaceModuleCohomology`.

The abandoned sandbox modules `ZariskiModuleAbelianCohomologyComponentsExist` and
`ZariskiModuleAbelianCohomologyComponentsNatural` are removed. Neither proposed new node
is delivered. Global pruning of modules reached elsewhere is left to the maintainer.
The unit `sk-prop-cd` has empty realized lists for this comparison; no unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox naturality statement quantified over an arbitrary family of objectwise
isomorphisms. That statement is false: in degree zero, on the point scheme Spec(Z), change
only the component at the structure sheaf by negation, leaving the component at its direct
sum with itself unchanged. The inclusion into the direct sum then violates naturality.
The repaired proof uses a specifically constructed resolution comparison, whose naturality
is established by the existing acyclic-resolution theorem. No such false statement is kept.

The earlier report credited the upper theorem as newly proved, although it is already proved
in the repository baseline. Its two proposed new modules also lacked source docstrings and
DAG nodes. The repaired delivery closes the actual baseline component hole without adding
any intermediate statements. The required `deliver3.py --no-push` dry run now prints OK: compilation and
preflight passed, with the second reading pending and nothing pushed. The optional local
axiom probe timed out at 60 seconds; deliver3 reports that the merge runs it again.
The regular compiler checks passed without warnings.

## Second reading by Y2

1. Interface: PASS. Compared the sole delivered Lean module with the repository by
   `diff`; both existing theorem signatures are byte-identical, and the upper theorem's
   proof and all public imports are unchanged. No definition, target, or statement changes
   are delivered. The only added declaration is a proved private naturality helper.
2. Proof: PASS. Independently compiled the module through `lcompile.py` in 27.2 seconds
   without warnings. Scanned for sorry and forbidden declarations: none occur in the
   delivered Lean source. Compiled a scratch copy with explicit `#print axioms` for both
   public theorems and the private helper in 27.0 seconds. The helper uses only propext,
   Classical.choice, and Quot.sound. Both public theorems use those axioms and sorryAx
   through existing open dependencies, including acyclicComparison_naturality; this is
   not an axiom-free closure claim. There is no data definition choosing an arbitrary
   witness from an unproved existence theorem.
3. Split statements: PASS, none added. Read the generic private helper and checked that
   its augmentation equation is exactly the premise of Mathlib's resolution naturality.
   The comparison uses an explicitly constructed family and one chain lift throughout.
   Degree zero uses the same acyclic-resolution isomorphism; positive acyclicity is only
   requested in degrees n + 1. Identity maps, zero maps, zero sheaves, and the empty space
   require no extra assumptions or exceptions.
4. Route and pruning: PASS. Read the resolution comparison, exact-forgetting instances,
   injective-module acyclicity, and Ext-to-derived-sections declarations. Independent
   grep, LeanFinder, and Loogle searches found the Mathlib injective-resolution and
   homology naturality lemmas already used, with no shorter applicable comparison for
   an acyclic noninjective abelian resolution. The new proof imports are private and
   each supplies a used declaration or instance. The report lists all six removed direct
   imports and the sole discarded old proof dependency; the other two old dependencies
   remain used. The unit sk-prop-cd has empty realized lists, unchanged: no realized unit
   step is bypassed. No global unreachability is claimed for these removed direct imports.
5. Nodes: PASS. The sole delivered node differs only in proof, proof_deps, and
   proof_origin. Its proof_deps is exactly the union of the steps' uses and matches the
   five project dependencies used by Lean. No new nodes or change records are required.

Second reading changed only this report, adding the independent review and successful
explicit axiom-check evidence. The Lean proof and node repair required no further edits.
