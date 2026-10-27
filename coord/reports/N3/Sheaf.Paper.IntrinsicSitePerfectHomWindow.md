## What changed

Completed `WeilConjectures.finiteIntrinsic_sitePerfect_hom_window` in
`Sheaf.Paper.IntrinsicSitePerfectHomWindow`, preserving its signature and public imports.
Private proof helpers compare the recorded pro-etale Tor predicate with native derived Tor
amplitude, add tensor intervals, and reverse the interval under perfect duality.
The common representative-test argument is proved once over an abstract abelian category;
the concrete site supplies the existing native K-flat tensor comparison and resolutions.

The proof uses the existing ringed-site perfect-duality theorem, uniqueness of left adjoints,
and the source library's tensor bounds and t-structure orthogonality. The two perfect-duality
evaluation isomorphisms and biduality supply the adjunctions needed for the reversed interval.
The first clause also compares the specified intrinsic tensor unit with the ordinary
coefficient object. No definition, target, consumer, or adopted source module changes.
The node's proof, proof dependencies, and proof origin follow this route.
The completed module compiled without warnings in 53.7 seconds through `lcompile.py`.
Local irreducibility of the chosen closed structure, intrinsic tensor, and internal Hom prevents unfolding their
large constructions; universe parameters are aligned with the recorded finite internal Hom.

Mathlib searches (leanfinder, loogle, and grep, recorded in `searches.jsonl`) supplied no
matching derived-site theorem. Searching the adopted library found the already-proved
`DerivedCategory.torAmplitudeIn_tensor`, the one-sided tensor bounds, and the orthogonality
argument in `torAmplitudeIn_of_exactPairing`. The proof uses that argument directly with
adjunctions obtained from perfect evaluation, avoiding extra exact-pairing constructions.

## Proved and sorry left

Closed the single hole of `WeilConjectures.finiteIntrinsic_sitePerfect_hom_window`
(node `lem-sf-intrinsic-site-perfect-hom-window`). Added zero holes and split off zero
statements. No `sorry` remains in the delivered module. All private helpers are proved.

## No longer needed

Removed the unused trial proof import `Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`.
No original imports are removed: all three public imports are needed by the unchanged
statement. The local finite-projective-model and slice-descent route is unnecessary for this
node. Its following former direct proof dependencies are removed:

- `lem-pc-bounded-above-flat-kflat-site` (`Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`).
- `lem-pc-bounded-exact-term-hom-quasi-iso` (`WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso`).
- `lem-pur-site-restriction-module-adjunction-exact` (`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`).
- `lem-sf-flat-model` (`Sheaf.Paper.FiniteCoefficientFlatModel`).
- `lem-sf-site-perfect-tor-window` (`Sheaf.Algebra.Homology.SitePerfectTorWindow`).
- `lem-sfb-ringed-tensor-comparison-extension` (`Sheaf.Algebra.Homology.RingedTensorComparisonExtension`).
- `lem-weil-pbc-ringed-internal-hom-exact-restriction` (`Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`).
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` (`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`).
- `lem-weil-pbc-site-derived-tensor-descent` (`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`).

These are removed only from this node's direct proof dependencies. Some remain transitively
used by the existing perfect-duality theorem or other library results; no module is withdrawn,
and no claim is made that they are globally unreachable. The unit's site-perfect dual tensor
formula and sharper Tor interval are both preserved.

## Where the brief, the DAG or earlier work was wrong

The planned `lem-sf-flat-model` route does not directly fit the unrestricted scheme and
site-perfect hypotheses of this statement: its geometric/constructibility interface is
stronger. That does not dispute this statement. The existing abstract derived tensor bounds,
perfect biduality, and t-structure orthogonality give the required unrestricted argument.
Empty sites and zero objects cause no exception: the proof uses only universal vanishing
conditions, and the ordered interval conditions are transported explicitly.

The original docstring records the earlier local-model plan. The revised DAG and proof-body
comments record the actual adjunction route; its mathematical conclusion is unchanged.

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
