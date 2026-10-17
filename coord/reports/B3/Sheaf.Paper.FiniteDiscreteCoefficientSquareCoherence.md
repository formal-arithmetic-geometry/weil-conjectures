## What changed

Proved `finiteDiscreteCoefficientPullbackIso_square` and the ordinary comparison
composition lemma `finiteDiscreteCoefficientSheafPullbackIso_comp`. The ordinary
proof transports normalized restriction composition through the equivalences,
takes mates, proves site restriction composition on components, and pastes by
naturality. The parent transports this identity through exact derivation, D+
inclusion and the exact-versus-left-derived replacements, then proves square
coherence by categorical cancellation.

The API caches the ambient comparison objectwise and specializes the generic
`FunctorComparisonSquare` predicate to exactly the original coefficient square
equation. `coefficientIsoTransThree_eq` identifies the new construction with the
old triple composite. No existing public declaration signature changes.

Repair of the returned delivery: the `## Users` table in
`coord/changes/B3-coefficient-composition-components.md` now includes the missing
`Sheaf.Paper.CoefficientExchangeFromComparisons` and all 24 current downstream
modules. Preserve current main's `coefficientDerivedAdjunction_eq`,
`coefficientAmbientSquare_app`, and both definitions' `no_expose` attributes. Add
`coefficientAmbientSquare_eq` so the completed square proof uses the hidden
construction through a proved equation. The unchanged returned consumer compiles
against both baseline and repaired API, with the same existing style warnings.
All three delivered modules compile without warnings (14.2, 10.3 and 20.7 seconds);
the unchanged `FiniteDiscreteDerivedCoefficientData` also compiles (12.6 seconds).

The retained composition proof hit a deterministic kernel reduction limit against
current main. Its mate composition calculation is now proved for arbitrary
adjunctions before direct specialization. This avoids unfolding concrete pullback
constructions and adds no hole or definition change. No downstream module needs
adaptation. The previous independent reading predates these repairs; the repaired
delivery requires its new independent reading.

## Proved and sorry left

Original assigned holes: 1. Closed:
`AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficientPullbackIso_square`.
Added holes: 0. Split off: 0. Net assigned holes closed: 1.

Also proved the ordinary-composition obligation:
`AlgebraicGeometry.ProEtale.CondensedRing.finiteDiscreteCoefficientSheafPullbackIso_comp`.
No `sorry` remains in any delivered Lean file. All private helpers and public API
lemmas are proved. There is no hole in a data definition.

Axiom checks of both completed theorems and the ambient-square equations still
include `sorryAx` inherited from current imported obligations, including
`finiteDiscreteCoefficientRestrictionForgetIso_linear`
(node `lem-weil-pbc-finite-discrete-restriction-linearity`). Those existing
statements, proof obligations and nodes are unchanged. The new generic
`coefficientIsoTransThree_eq` uses only `propext`, `Classical.choice`, and
`Quot.sound`. Baseline checks confirm the unchanged ambient-square API, derived
composition and restriction-composition theorems already have `sorryAx`. No new
axiom or hole is introduced.

## No longer needed

The parent no longer imports `Sheaf.Paper.DerivedSquarePasting`, nor depends on its
node `lem-weil-pbc-derived-square-pasting`. It uses the proved source-library exact
derivation and composition APIs directly from `MapDerivedCategoryMate` and
`FiniteCoefficient.Derived.RestrictScalars`. This prunes this proof route; other
parents may still use the removed dependency.

Removed redundant direct imports of the coefficient API and restriction-coherence
module from the parent. Restriction coherence is still used through the ordinary
composition lemma, so its node is not pruned from the import closure. The API is
already public through the canonical pullback interface.

The inherited adaptation of
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs` and its change
record are unnecessary and absent from this delivery. That source module remains
needed in its original form. No blueprint unit statement or realized proof step
is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned change record omitted the direct ambient-square consumer. It now
lists that consumer explicitly and preserves its component equation API. The
retained delivery also predated current main's hidden-definition equation APIs
and source import moves; this repair preserves those interfaces and updates its
proof imports. No mathematical statement is disputed or weakened.

The earlier concrete square and mate calculations caused expensive kernel
conversion. Generic categorical calculations followed by direct specialization
resolve that implementation issue. All exploratory split-off obligations have
been removed from the delivery; none is needed by the completed proof.

## New nodes

`lem-weil-pbc-finite-discrete-sheaf-pullback-composition` records the proved ordinary
composition equation. Its statement has no derived category, D+ inclusion,
left-derived replacement, or arbitrary square transport. The canonical
comparisons are unchanged. It uses the existing proved
`lem-pc-adjunction-square-composition` as a categorical tool. No new holed node is
introduced. The API node and assigned square node follow the implemented route.

## Second reading by B3

1. **Signatures and statements.** I compared the delivered item with the repository version. The target theorem signature is byte-for-byte unchanged. The API and ordinary-composition modules are newly delivered or explicitly covered by the change record; their existing public declarations retain their signatures. The specialized `CoefficientPullbackSquare` predicate expands to the former universally quantified component equation, with the same binders and morphisms. Verdict: pass.

2. **Proof and axioms.** I compiled all three delivered modules with `lcompile.py --all`; all compile without errors or warnings. There is no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` in the delivered files. The completed target and ordinary composition theorem use only the allowed foundational axioms, apart from `sorryAx` inherited from unchanged imported obligations. Verdict: pass.

3. **Split statements and DAG.** The only added theorem is the ordinary sheaf-pullback composition equation. It is strictly below the target, has a complete proof, a source, and a matching DAG node; it is not a restatement of square coherence. The API node records the new cached constructions and the change record records their users. No unproved split-off theorem or hollow definition was added. Verdict: pass.

4. **Route and pruning.** The proof uses the ordinary composition lemma, exact/D+ transport, and the source-library derived composition API, then applies the generic categorical square argument. The unit route is preserved. `DerivedSquarePasting` and its node are no longer used and are listed under `No longer needed`; no required restriction-coherence dependency was accidentally removed. Verdict: pass.

5. **DAG agreement and repair.** The target node proof and dependencies match the imports and declarations used by the Lean proof. The ordinary-composition node records its actual dependencies and proof origin. The API change record lists all downstream users, including `CoefficientExchangeFromComparisons`, and preserves the existing equation APIs and visibility. Changes made during this reading: none to Lean or DAG files; this section documents the checks required by the delivery tool. Verdict: pass.
