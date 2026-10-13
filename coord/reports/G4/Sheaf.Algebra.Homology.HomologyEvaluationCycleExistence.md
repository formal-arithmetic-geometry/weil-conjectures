## What changed

Replaced the sorry in `CategoryTheory.exists_homologyEvaluation_cycle` with a complete
proof from the chosen Hom-complex projections. Private helpers establish the cycle lift,
both boundary identities, the two cokernel descents, and the representative formula.
Added proof-only imports of `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree`,
and `Mathlib.CategoryTheory.Monoidal.Closed.Braided`. The target signature and unit
route are unchanged.

## Proved and sorry left

The candidate closes `CategoryTheory.exists_homologyEvaluation_cycle` (node
`new-b2-homology-evaluation-cycle-existence`): one original hole removed, zero holes
added, and no sorry remains in the delivered module. The complete abstract projection
theorem compiles with only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the redundant candidate import
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels`; its declarations are already
available through the required imports. No old proof-dependency node or library module
is pruned. The existing definitions, Hom-complex, internal Hom, and projection nodes remain
needed. No unit statement or proof step is bypassed. No new node or module is needed.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt encountered a stale published object for the public dependency
`HomologyEvaluationDefinitions`; compiling that source in the sandbox resolves the tool
failure. The proof and target statement are unchanged.

## Earlier second reading (a previous round; superseded)

The independent reading below supersedes this placeholder. The change record is
`coord/changes/HomologyEvaluationCycleExistence-instances.md`.

## Second reading by G4

1. Compared both sandbox modules with the repository using diff. The dependency
   `HomologyEvaluationDefinitions` is byte-for-byte identical and is present only to
   compile against its current source. The existing target signature is byte-for-byte
   identical. Its definitions and public import are unchanged. Verdict: pass.
2. Compiled both modules with `lcompile.py --all`, with no errors or warnings. Scanned
   both delivered sources for sorry and forbidden declarations: none. In a scratch copy,
   `#print axioms CategoryTheory.exists_homologyEvaluation_cycle` and the private
   `homologyEvaluation_of_projections` both show only `propext`, `Classical.choice`, and
   `Quot.sound`. The local instances use existing constructed structures, and all
   quotient witnesses are constructed by universal properties inside proved theorems.
   Verdict: pass; one original hole closed, zero holes added.
3. There are no split-off statements or new nodes. Read each proved private helper:
   the cycle lift, both boundary identities (including the negative-degree sign), the
   tensor-preserved cokernel descent, and the sectionwise representative formula are
   valid for arbitrary complexes, including zero complexes and empty opens. In
   particular, the proof never assumes sectionwise surjectivity of a sheaf cokernel.
   Verdict: pass.
4. Searched Lean sources by evaluation/cohomology and Hom/cokernel/cycles terminology;
   found no exact replacement for this internal sheaf-Hom evaluation theorem. The
   presheaf zero-left lemma is available upstream, but using it would add a proof import
   merely to replace the small existing private calculation. A Loogle search for
   `CokernelCofork.mapIsColimit` returned an unknown-identifier response; checked the
   actual Mathlib source instead. Existing Mathlib kernel/cokernel universal properties
   are used directly. Tested deleting the braided and kernels imports: braided is
   needed for tensorRight colimit preservation, while kernels is redundant. All old
   proof_deps remain used; the unit `sk-thm-picard-duality` realized record is unchanged
   and no unit step is bypassed. Verdict: pass after import cleanup.
5. Compared the node with the original and with the Lean proof. Only proof-owned
   fields are changed: the five proof steps accurately describe the projection choice,
   cycle lift, boundary calculations, cokernel descents, and representative formula.
   proof_deps is their union, including the tensor-Hom construction tool node;
   proof_origin records the actual argument. No statement or dependency-definition
   change is hidden in the metadata. Verdict: pass.

Second reading removed the redundant proof import and replaced the three private global
instances with private constructed structures registered using `[local instance]`, so their registration ends with this module. Updated this
report and `coord/changes/HomologyEvaluationCycleExistence-instances.md` accordingly.
The dry run initially flagged the global registrations; final validation checks the
local version. No existing declaration signature or definition changes.
