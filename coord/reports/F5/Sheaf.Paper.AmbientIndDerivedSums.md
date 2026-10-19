## What changed

Replaced the two proof holes in Sheaf.Paper.AmbientIndDerivedSums by complete proofs
with unchanged theorem statements. The proof uses the source HomologyCoproducts instance,
HomologyProperty truncation API, the stated IndCons sum theorem, the stated triangulated theorem,
and the actual localizing-closure intersection. Private proved helpers handle the empty sum,
cohomology sum closure, and shrinking the nonzero support of an existing larger coproduct.

Validation: a fresh single-file lcompile.py check against the current published build
compiled cleanly in 8.1 seconds (exit code 0). Both original theorem signatures remain
unchanged; the source contains no sorry and no line longer than 100 characters. Both
theorem docstrings describe the implemented route, including the support argument.
A fresh sequential lcompile.py --all check compiled the changed module (11.1 seconds)
and all three unchanged current consumers against its compiled overlay:
ProperIndConstructibleUnbounded (13.8 seconds), ProperUnboundedWindow (5.2 seconds),
and ProperUnboundedCoproducts (3.4 seconds), with no diagnostics.
The required delivery dry run is in progress.

## Proved and sorry left

Two original holes closed by compiling proofs:

- AlgebraicGeometry.ProEtale.indConstructibleDerived_sums_and_truncations.
- AlgebraicGeometry.ProEtale.indConstructibleDerived_sums_and_truncations_padicAlgCl.

Both correspond to det-ambient-ind-derived-sums. There are zero sorry tokens in the delivered
Lean source, no new split-offs, and no changed definitions. Existing imported theorem holes
remain their own items. Closed: 2; added: 0; split off: 0.

## No longer needed

Removed imports:

- WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible.
- Sheaf.Paper.LocalizingClosureExistence, replaced by Sheaf.Paper.LocalizingClosure.
- Sheaf.Topology.ProfiniteCondensedRing.
- Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible.
- Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses.
- Sheaf.CategoryTheory.SheafTensor.
- Mathlib.Algebra.Homology.Embedding.CochainComplex.
- Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale (added to the current
  source after the earlier attempt; this proof uses constantModelBoundedConstructible directly).

The route no longer invokes det-def-localizing-closure-existence or
lem-weil-pbc-ring-sheaves-grothendieck: the existing module-object Grothendieck instance and
proved derived coproduct-preservation instance supply the input directly. The localizing
intersection is used without the bundled existence theorem. The two obsolete tool approvals
are withdrawn. The node no longer needs lem-weil-pbc-truncation-cohomology as a separate input:
the source-library truncation lemmas already prove the derived formulas. It also no longer needs
the separate sk-def-sfb-bounded-constructible triangulatedness theorem or sk-def-sfb-sheaf-tensor
wrapper. Constant-model bounded constructibility itself is retained through its defining module.
No module is withdrawn from the library; these are dependencies pruned from this item's route.

## Where the brief, the DAG or earlier work was wrong

The coproduct and truncation arguments were already implemented in the proved source library.
The original proof plan did not name those APIs. The localizing predicate quantifies over a
larger indexing universe; the private support argument explicitly bridges that convention.
No mathematical statement was changed. The import change record is
coord/changes/F5-ambient-ind-derived-sums-imports.md; its Users table covers all three consumers. Empty sums, zero summands, arbitrary integer truncation
cutoffs and both coefficient rings are covered by the argument. A nonempty finite
subextension is written explicitly as the bottom intermediate field with its finite-dimensional
proof, since PadicAlgCl.FiniteIntermediateField has Nonempty but no recorded Bot instance.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
