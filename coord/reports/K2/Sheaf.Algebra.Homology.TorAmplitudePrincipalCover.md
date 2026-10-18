## What changed

Proved `DerivedCategory.torAmplitudeIn_of_principal_cover` in
`Sheaf.Algebra.Homology.TorAmplitudePrincipalCover`, with its signature unchanged.
A proved private helper converts the acyclic-tensor base-change theorem into categorical
K-flatness. The main proof chooses a module K-flat resolution, uses exact localization
and its monoidal tensor comparison, applies local Tor bounds to each extended test module,
and descends homology vanishing. This works with independent derived-category universes,
unbounded complexes, arbitrary nonflat test modules, zero rings, and the empty cover.

Updated the existing DAG proof and dependencies to match this implementation.
The import-interface change is recorded in
`coord/changes/k2-tor-amplitude-principal-cover-imports.md`.

## Proved and sorry left

Closed 1 original hole: `DerivedCategory.torAmplitudeIn_of_principal_cover`
(node `lem-weil-pbc-tor-amplitude-principal-cover-glue`).
Added 0 holes; split off 0 theorems; 0 sorries remain in the delivered module.
The private helper `DerivedCategory.kFlat_extendScalars` is proved.
Single-file compilation passed, and `#print axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound` for the public theorem.

## No longer needed

Removed direct imports:
- `Sheaf.Algebra.Homology.DerivedChangeOfRings` (formerly public): ordinary module scalar
  extension is enough; no singleton-site equivalence or sheaf derived change of rings is used.
- `Sheaf.Algebra.Homology.KFlatResolution` and
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`: the already proved
  `CochainComplex.exists_quasiIso_flat_kFlat` supplies the module resolution directly.
- `Mathlib.RingTheory.Flat.Basic`: the categorical exactness API in
  `Mathlib.Algebra.Category.ModuleCat.Descent` supplies the needed flat tensor exactness.

The proof no longer depends on `lem-pc-kflat-resolution`; it instead uses the existing
proved node `lem-pc-source-module-kflat-resolution`. Removed the obsolete tool-use approval
for the former node. `lem-pur-derived-change-of-rings` is not invoked by the proof.
All other declared proof dependencies are retained: the tensor-model specialization,
localization flatness, flat tensor exactness, K-flat scalar extension, and localization-span
homology vanishing. No unit statement or step is bypassed. These are removals from this
module's imports/route, not a claim that these modules are unused elsewhere.

## Where the brief, the DAG or earlier work was wrong

The planned singleton-site specialization of the sheaf K-flat resolution is unnecessary:
the source library already proves the required ordinary-module resolution. The explicit
pure-tensor chain maps in the plan are already supplied by Mathlib's monoidal scalar
extension. No mathematical statement or definition required repair. There are no new nodes.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
