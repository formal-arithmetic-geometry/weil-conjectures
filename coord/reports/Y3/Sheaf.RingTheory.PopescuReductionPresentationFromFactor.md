## What changed

Corrected and proved `Algebra.exists_popescu_reduction_presentation_of_factor` in
`Sheaf.RingTheory.PopescuReductionPresentationFromFactor`: added the missing
`[FinitePresentation R A]` assumption from Stacks Tag 07CK. The direct Mathlib proof
constructs a finite presentation over `A/IA`, lifts equations and generator images,
checks evaluation using the factorization identity, and transports standard
smoothness along the reduced quotient equivalence. Added the proof-only import
`Mathlib.RingTheory.Extension.Presentation.Basic`. Updated the existing DAG node's
statement, Lean record, proof and proof origin, with a statement-change record.
The change record is `coord/changes/popescu-reduction-presentation-from-factor.md`.
No new modules, statements, definitions or nodes were added.

## Proved and sorry left

Closed the one hole: `Algebra.exists_popescu_reduction_presentation_of_factor`, node
`new-lem-popescu-reduction-presentation-from-factor`, for the explicitly corrected
statement. Zero new holes; zero split-off statements; no sorry remains in the
assigned module. This is a statement correction followed by a proof, not a proof
of the false original signature and not a decomposition.

Both the corrected module and its unchanged sole caller compiled without warnings
using `lcompile.py --all`. The unchanged caller was retained only in scratchpad,
not delivered; no forced adaptation is required. Axiom verification and delivery
preflight run through `deliver3.py --no-push`.

## No longer needed

Removed the redundant direct public imports
`Mathlib.Algebra.Category.CommAlgCat.Basic` and
`Mathlib.CategoryTheory.ObjectProperty.Ind`, and, at second reading,
`Mathlib.RingTheory.Ideal.Over` and `Mathlib.RingTheory.Smooth.StandardSmooth`;
the retained public core import already publicly supplies all four.
No DAG proof dependencies or project modules are
pruned: the original node had no proof dependencies. The core module remains
needed for the public definition `Algebra.reducedAlgHom`.

## Where the brief, the DAG or earlier work was wrong

The old statement omitted finite presentation of `A`, which the source assumes.
The existing dispute and its counterexample were correct: take `R = Λ = C = ℤ`,
`I = 0`, and `A = ℤ[x₀,x₁,…]`, with augmentation and the identity factor maps.
Any finite proposed relations involve only finitely many coefficient variables.
The evaluation condition supplies a unital map from their finite-support quotient
to `ℤ`, so it is nonzero. The displayed quotient freely adjoins infinitely many
unused variables, hence is not finitely generated over `ℤ`, contradicting standard
smoothness. The correction adds precisely `[FinitePresentation R A]`, required by
[Tag 07CK](https://stacks.math.columbia.edu/tag/07CK).
[Tag 00F4(4)](https://stacks.math.columbia.edu/tag/00F4) supplies finite presentation
over the intermediate finite-type algebra. The proof uses no square-zero condition
on `I`, since this part only lifts polynomial data through quotient maps.

The sole DAG citer `lem-weil-pbc-popescu-reduction-presentation` holds unchanged:
it already assumes that `A` is finitely presented over `R`. The sole Lean caller
has the same instance and compiled unchanged against the correction. No target
statement or target definition changes; the unit's realized statements and steps
are retained. The change record lists all downstream modules; none needs editing.

The earlier attempt was blocked by a missing compiled core artifact. That artifact
is now restored. Its candidate also had two elaboration faults, fixed by using
`IsScalarTower.of_algHom β` and `MvPolynomial.hom_eval₂` with explicit ring-hom
coercion for `δ`. No library rebuild or tool workaround was used.

The first dry run rejected `statement_change.by = "Y3 stage 3"`: the shared
node schema requires the historical spelling `"Y3 stage 2"` even for a stage-3
correction. Corrected that metadata field; the work and change record remain
stage 3. The other preflight requirement is the independent second reading,
which is reserved for the next worker by the brief.

Final verification: the corrected module and unchanged caller compiled again after
removing the redundant imports. `deliver3.py Y3
Sheaf.RingTheory.PopescuReductionPresentationFromFactor --no-push` printed
`OK (dry run)` on 2026-10-13: compilation, axiom probes and preflight passed except
for the independent second reading reserved for the next worker. Nothing pushed.

## Second reading by Y3

1. **Visible declarations: pass with the recorded correction.** Compared the sole
   delivered module and existing node against the repository. The only signature
   change is `[FinitePresentation R A]`, explicitly recorded in
   `coord/changes/popescu-reduction-presentation-from-factor.md` and in the node's
   `statement_change`. Checked the old infinite-variable augmentation counterexample
   and the finite-presentation assumption in Stacks Tag 07CK. The existing caller
   already has this instance; its signature and proof are unchanged. No target or
   definition is changed. This delivers a proof of the corrected intermediate
   statement, not of the false old statement.

2. **Proof and axioms: pass.** Read the scalar tower, finite presentation,
   coefficient and generator lifts, evaluation identity, kernel equality, and
   algebra equivalence. Compiled the final module together with a byte-identical
   scratch copy of its sole caller using `lcompile.py --all`. Both compiled without
   warnings. An explicit scratch `#print axioms
   Algebra.exists_popescu_reduction_presentation_of_factor` returned exactly
   `propext`, `Classical.choice`, and `Quot.sound`. The delivered Lean file has no
   `sorry`, prohibited declarations, or definitions. All chosen witnesses come
   from proved Mathlib theorems, not from unproved existence statements.

3. **Split statements: pass, none added.** Zero new holes and zero split-off
   statements. Checked the argument for empty generator or relation sets, `I = 0`,
   `I = top`, and zero coefficient or target rings: quotient surjectivity and
   finite presentation work without nontriviality assumptions. Searched Mathlib
   with `msearch.py grep` for polynomial evaluation through quotients and lifted
   presentations, and searched the project with different wording. The nearby
   standard-smooth quotient lifting and standardizer presentation lifting results
   solve different problems; no replacement for this whole theorem was found.

4. **Route and pruning: pass after import repair.** The proof uses the direct
   Mathlib finite presentation and evaluation route; no new project lemma is
   needed. The old node has `proof_deps = []`, so no old proof dependency is omitted
   from `No longer needed`. Read `dag/units/sk-thm-p1.json` and its `realized`
   statement and steps: this helper lies below those nodes and bypasses none.
   Removed two additional redundant public imports, `Ideal.Over` and
   `StandardSmooth`, already publicly exported by the required core. The sole
   remaining proof import is private. All public names remain available through
   the core; the unchanged caller compiled against the final import set.

5. **DAG agreement: pass.** The node's statement and `lean.statement` match the
   corrected signature; its three proof steps describe exactly the Lean argument,
   `proof_deps` remains empty, and `proof_origin` cites the lifting construction
   and finite-presentation permanence lemma. Only the allowed proof/Lean fields
   and the recorded statement-change fields differ from the repository. The sole
   DAG citer is recorded as still holding and already assumes finite presentation
   of `A`. No new nodes are required.

Second reading changed only the two redundant imports and this report, including
the complete import-pruning list. The mathematical proof needed no repair.
