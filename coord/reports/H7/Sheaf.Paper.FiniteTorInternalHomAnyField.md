## What changed

Replaced the body of `AlgebraicGeometry.Scheme.finiteTor_internalHom_constructible_anyField`
with a complete Lean proof from the locally closed finite-projective generator calculation.
The original statement, universes, hypotheses, visibility, and public imports are unchanged.
The proof constructs the thick bounded-constructible object property, proves its stability under
retracts, uses signed exactness of contravariant derived Hom and flat-model thick generation,
and obtains the specified canonical bounded-constructible étale origin.

Added `Sheaf.Paper.LocallyClosedProjectiveHomAnyField`, containing the remaining generator
calculation, and its DAG node. Updated only the parent's proof, proof dependencies, and proof
origin to follow the Lean argument. `import all Sheaf.SixFunctors.FlatModelGeneration` accesses
proved private constructibility comparison and retract helpers; it is a proof import.
No existing definition, theorem signature, attribute, or public import changes.

Both Lean modules compiled successfully through lcompile.py: the helper in approximately
5 seconds and the parent in 10.1 seconds. No slow-definition workaround was needed.

## Proved and sorry left

Original holes: 1. The hole in
`AlgebraicGeometry.Scheme.finiteTor_internalHom_constructible_anyField`
(node `lem-per-finite-tor-internal-hom-any-field`) is closed by the complete assembly proof.
There are zero `sorry` occurrences in the item module.

Added holes: 1, exactly
`AlgebraicGeometry.Scheme.locallyClosedProjective_internalHom_constructible_anyField`
(node `lem-per-locally-closed-projective-hom-any-field`). Its proof is exactly `by sorry`.
This is a decomposition, not a net proof: 1 upper hole closed, 1 strictly smaller lower hole
added, net 0 holes closed. The lower theorem treats only a degree-zero locally closed
finite-projective generator and has no étale-origin conclusion. It does not repackage the
original arbitrary first input. The nontrivial triangulated/retract/generation and origin
arguments remain proved in the parent. No definition contains `sorry`.

## No longer needed

Removed these direct private proof imports from the parent:

- `Sheaf.AlgebraicGeometry.ProEtalePullbackLocallyConstant`
- `Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle`
- `Sheaf.Paper.CohomologyInWeakSerreSubcategory`
- `Sheaf.AlgebraicGeometry.DiscreteNoetherianConstructibleSerre`
- `Sheaf.AlgebraicGeometry.NoetherianGlobalConstructibility`
- `Sheaf.CategoryTheory.RingedSitePerfectDuality`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.Paper.StratumAmbientHom`
- `WeilConjectures.ConstructibleSheaf.Pullback`
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`
- `Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility`

These removals are import cleanup, not claims that all these modules can be withdrawn.
Their geometry, support, pullback, perfect-duality, and direct-image arguments remain part
of the split generator node's proof plan, and some are also transitive imports of existing
proved tools. The old top-level tool approvals are retained because they still serve that
transitive argument. No existing node or module is withdrawn or claimed globally pruned.
The generic Serre/triangulated closure argument is now handled by already proved library
APIs rather than repeated. The finite-Tor hypothesis on the second input remains verbatim,
although only its bounded constructibility is used.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The DAG's eleven-step route is retained:
steps 1-7 and 9 form the remaining generator calculation; steps 3, 8, 10, and 11 are
implemented in the parent using existing APIs. The existing arbitrary-field étale Hom
finiteness theorem was considered as a shorter route, but transporting its fixed-coefficient
Hom through comparison to the exact intrinsic Hom in this statement requires additional
comparison work. The implemented generator route avoids assuming such an identification.

The remaining generator theorem was tested mathematically on empty schemes, zero inputs,
and n = 1. It requires no perfection, separable closedness, positive characteristic, or
absolute Galois cohomological-dimension bound. The support calculation factors the
immersion as open into its scheme-theoretic image followed by closed, in the same order
as the canonical extension in FlatModelGeneration.

## New nodes

`lem-per-locally-closed-projective-hom-any-field`, in
`dag/nodes/sec-deligne-laumon-a1/`, states precisely bounded constructibility of ambient
Hom from one locally closed finite-projective degree-zero extension. Its source is
Bhatt–Scholze Lemma 6.7.13, with 6.7.11 and 6.7.2. Its full proof plan, cited existing
nodes, Lean attachment, and three kinds of Mathlib search are recorded. No existing node
states this exact intrinsic generator calculation. No change record is required because
no existing declaration interface was changed.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteTorInternalHomAnyField": "7da2a6226a4e741e70c9cf8b771515193b3eb7d2", "Sheaf.Paper.LocallyClosedProjectiveHomAnyField": "25d56d8e333ec4b63b4128923cd401eab1c23ab9"}, "results": {}, "time": "2026-10-28T14:15:49+0800", "transitive": 0, "version": 1}
```

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
