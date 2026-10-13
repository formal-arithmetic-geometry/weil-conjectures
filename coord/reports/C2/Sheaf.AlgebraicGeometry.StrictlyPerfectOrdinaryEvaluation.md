## What changed

Reduced `AlgebraicGeometry.isIso_localOrdinaryEvaluation_degree`, with its original
signature and docstring unchanged, to module-level finite-projective evaluation and
finite-support assembly. The proof extracts the two clauses of `IsStrictlyPerfect`
and applies the two lower theorems. Both new statements are strictly parts of the
argument: assembly assumes the module comparisons, whereas the module theorem
has no complexes, bounds, chain maps or totalizations.

Moved the evaluation constructions and the local preadditive instance to `Sheaf.AlgebraicGeometry.BoundedOrdinaryEvaluationAssembly`, publicly reexported
by the original module. No declaration is renamed and no type changes; the second reader replaced
the projection body with a definitionally equal expression, as recorded below.
No downstream source is edited. This avoids a cycle and a 60-second timeout from
inlining all the constructions in the assembly theorem statement. The definition
of `SheafOfModules.moduleDualEvaluation` is an actual monoidal-adjunction construction.

The change record is
`coord/changes/C2-ordinary-evaluation-construction-location.md`.
The original node's proof, proof dependencies and Lean declarations are updated.
All three sandbox modules compile in import order; the final dry run checks them again.
The second reader restored the module-evaluation proof-only import of
`FiniteFreeInternalHomExact`, replaced the assembly import of `PerfectComplex`
with `Mathlib.AlgebraicGeometry.Modules.Sheaf`, and removed the assembly module's
redundant direct `MonoidalClosed` and sheaf `Colimits` imports.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.isIso_localOrdinaryEvaluation_degree`
(node `lem-pc-strictly-perfect-ordinary-evaluation`).

Added two holes, both entire named public theorem proofs:

- `SheafOfModules.isIso_moduleDualEvaluation_of_retract`, node
  `lem-pc-finite-projective-internal-hom-evaluation`.
- `AlgebraicGeometry.boundedOrdinaryEvaluation_degree`, node
  `lem-pc-bounded-ordinary-evaluation-assembly`.

This is a decomposition, not a completed mathematical proof. One original hole
closed and two lower holes added; no sorry occurs in any definition.

## No longer needed

Removed the direct proof import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact` from the item.
Its coordinate calculation is still in the proof plan of the new module evaluation
node, so neither that node nor its module is claimed as globally pruned.

The item's direct imports of `HomComplex`, `MonoidalClosed`, `BifunctorShift`,
`Single`, sheaf `Limits`, sheaf `Colimits`, and `TensorClosed` now reach it through
the publicly imported assembly module. These are redundant edges, not modules
removed from the target closure. No planned mathematical node is globally pruned.

Exhaustive comparison with the old direct `proof_deps`: `def-pc-perfect-complex`
is still used directly through the two clauses of strict perfection.
`def-pur-hom-complex`, `def-pc-tensor-complex-sheaves`, and
`lem-pc-sheaf-modules-tensor-closed` are now used by the assembly statement
and constructions; `lem-sc-finite-free-internal-hom-exact` is retained in the
module-evaluation proof plan and its proof-only import. These four nodes are
no longer direct steps of the original theorem, but none is globally pruned.
The assembly module no longer directly imports `PerfectComplex`, `MonoidalClosed`,
or sheaf `Colimits`; the original module still imports `PerfectComplex` for its
hypothesis, and the other two remain available through required public imports.

## Where the brief, the DAG or earlier work was wrong

The listed finite-free internal-Hom exactness declaration supplies canonical Hom
coordinates, not the tensor-dual evaluation isomorphism itself. The missing evaluation
calculation and the Hom-product/tensor-coproduct assembly have separate new interfaces.
The unit record has empty realized statement and step arrays; the existing finite
sum and finite-free/retract route is retained inside the same unit.

Checked source: Stacks `cohomology.tex`, `lemma-dual-perfect-complex` (08DQ), last
finite-sum displays and finite-free/retract paragraph, and `lemma-Rhom-strictly-perfect`
(08DM). A source copy used for reading is in scratchpad, outside the delivery.

Edge cases checked mathematically: E=0 and rank zero give zero objects on both sides;
P=0 gives empty finite support; an empty open gives zero module sheaves; unbounded
F is allowed since only P controls the finite index set. Off-diagonal component
maps are zero and are not assumed invertible. The assembly hypothesis only concerns
the canonical module comparisons on the diagonal.

Searches: LeanFinder returned condensed-module and field-module hits, not this
sheaf comparison. Loogle with unqualified IsIso returned unknown-identifier/no hits.
The grep search returned graded and homological tensor inclusions, not the comparison.
LeanSearch failed with Internal Server Error and is recorded unavailable. Source
search found scheme `dualTensorHom` for locally free modules, which does not directly
cover arbitrary localized sites or match the specified currying formula.

## New nodes

`lem-pc-finite-projective-internal-hom-evaluation` states the canonical module
comparison for any retract of a finite free sheaf, with arbitrary second argument.
It is in its own new module and has the finite-free basis and retract proof in words.

`lem-pc-bounded-ordinary-evaluation-assembly` isolates the finite product/coproduct
calculation for a bounded P given invertible module comparisons. It has no
strict-perfection hypothesis. Its module also owns the unchanged evaluation
constructions required by its statement, reexported from the original module.

## Second reading by C2

1. **Existing interfaces: PASS.** Compared the item with the read-only repository
   using `diff -u`. The original theorem signature and docstring are byte-for-byte
   unchanged. A separate substring comparison confirmed that six evaluation constructions and the local preadditive instance are moved
   verbatim, including bodies and docstrings. The projection keeps its exact
   signature and docstring; its optimized body is definitionally equal to the
   old body, checked by a scratch equality proof using `rfl`. The change is declared in
   `coord/changes/C2-ordinary-evaluation-construction-location.md`; the original
   module publicly reexports the assembly module. No target, extra hypothesis,
   conclusion, or existing definition is changed. Compiled scratch copies of all
   three direct users, `OrdinaryEvaluationDifferential`,
   `StrictlyPerfectEvaluationComparisons`, and `StrictlyPerfectEvaluationModel`,
   unchanged against the delivered modules, in dependency order: all passed.

2. **Proof and data: PASS, with the two declared holes.** All three delivered
   modules compile with the required launcher, without errors or unexpected
   warnings (about 2, 12, and 3 seconds in the final source compile). A textual
   scan found exactly the two named theorem proofs `:= by sorry` listed above,
   no forbidden declaration or attribute, and no definition hole. Scratch
   `#print axioms` checks cover the original theorem, both lower theorems, the
   new module comparison definition, and all seven relocated declarations.
   The equality test and all three unchanged direct users compile against the
   optimized definitions. Every definition uses only `propext`, `Classical.choice`, and `Quot.sound`;
   the three theorems additionally use `sorryAx`, as expected from the two
   remaining proofs. The new evaluation map is built from actual symmetry,
   associativity, unit action, and the constructed tensor-Hom equivalence;
   it chooses no arbitrary existence witness. The existing Hom-complex
   projections are selected together with their product universal property
   from the now-proved `homComplex_exists`.

3. **Split statements and source: PASS.** Read the complete lower statements,
   their docstring proofs, and both new nodes against the last two sums and
   finite-free/direct-summand paragraph of `lemma-dual-perfect-complex` (08DQ),
   and the Hom product/sum calculation of `lemma-Rhom-strictly-perfect` (08DM)
   in the source copy. The module theorem concerns one finite-free retract and
   any second module, without complexes or support bounds. For a retract
   `i : E → L`, `p : L → E`, its inverse is precomposition with p, the free
   comparison inverse, then tensor of precomposition with i. Naturality and
   `i ≫ p = id` verify both identities. The assembly theorem assumes the
   diagonal comparisons and proves only the finite-support matrix calculation;
   strict perfection and the finite-free calculation are absent from its
   hypotheses. These are two strictly smaller parts, not a renamed target.
   Tested the argument for rank zero, E=0, P=0, empty U, a>b (all terms zero),
   a single supported degree, and unbounded F. Reindexing gives q=-r and
   p=r+n; the given predicate supplies zero off-diagonal entries, while the
   dual projection supplies exactly the asserted diagonal comparison.
   Repeated searches with new queries using LeanFinder, qualified Loogle,
   and grep (recorded in searches.jsonl and the new nodes). Inspected the
   upstream `homObjFreeIso`, `homObjFreeUnitIso`, and generic-site
   `dualTensorHom_app_bijective_of_iso_free`. The latter requires additional
   localized-site instances and gives presheaf section bijectivity for a free
   object, rather than this sheafified currying formula for a retract. The
   rigid-category hits require an exact pairing not yet constructed here.
   No exact duplicate or immediately applicable closure was found. Neither
   remaining calculation can be closed in a few minutes from these interfaces.

4. **Route and pruning: PASS as a decomposition.** The final proof extracts
   the two original strict-perfection clauses and combines module evaluation
   with bounded assembly. Reviewed every old direct proof dependency and
   listed where it remains needed under `No longer needed`; no globally
   pruned module is claimed. The finite-free/retract and finite-support route
   is retained. The unit record `sk-thm-picard-duality.json`, including its
   statement, single step, and empty realized arrays, is unchanged; no unit
   step is replaced. Moving the construction block supplies the required
   acyclic interface for the assembly theorem's own module; it does not
   divide an existing slow proof into files to evade a compile limit.
   One original hole is closed and two lower holes added: net -1, a
   decomposition, not a completed axiom-free proof.

5. **DAG agreement: PASS after import repair.** The original node changes only
   `lean`, `proof`, `proof_deps`, and `proof_origin`; its statement is unchanged.
   Its dependency union agrees with the written Lean composition. The assembly
   node additionally cites the already-proved Hom-complex projection interface
   used by the optimized construction. Both new
   nodes have the source, proof steps, dependency unions, search records,
   creation/provenance fields, chapter, unit, and matching Lean declarations
   required by the standing brief. Restored the missing proof-only import of
   `FiniteFreeInternalHomExact` in the new module-evaluation module to match
   its explicit finite-free coordinate proof plan. It is not a public import.

Changes by this reader: restored that proof-only dependency import; replaced
assembly's unnecessary `PerfectComplex` import with the scheme-module import
its definitions use; removed assembly's redundant direct `MonoidalClosed`
and sheaf `Colimits` imports; added the independent search records, exhaustive
old-dependency accounting, and this review. Repaired the timeout by choosing
projections from the existing `homComplex_projections_exists` theorem instead
of repeatedly unfolding its large existence specification. The optimized
projection body equals the original by `rfl`, and reduces assembly compilation
to about 12 seconds. No theorem statement, existing signature, constructed
object, or number of holes changed during the second reading.
