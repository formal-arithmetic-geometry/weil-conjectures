## What changed

Proved `SheafOfModules.FlatSingleTensor.ringed_flat_single_tensor_cohomology`
in `Sheaf.Algebra.Homology.RingedFlatSingleTensorCohomology`, preserving its
statement and all existing definitions. Added proved private helpers for the
single-summand totalization, simultaneous naturality, localization, and the
resolution normalization. No other Lean module is changed. The local proof commands are documented in
`coord/changes/ringed-flat-single-tensor-cohomology-proof-commands.md`.

A private dependent family type is parenthesized explicitly, and local backward
elaboration settings are used to keep categorical compositions definitionally
aligned. The derived-tensor definitions, and the ordinary and total tensor after their
chain-level calculations, are locally irreducible during proofs
to prevent expensive unfolding; their public bodies and attributes are unchanged.
The cohomology and localization isomorphisms are explicit private definitions,
with proved compatibility lemmas. This keeps large composite terms out of the
final naturality proof.

The degreewise comparison is the existing `mapBifunctorSingle₂Iso`; its homology
followed by `ShortComplex.mapHomologyIso` gives the specified comparison, with
`mapCyclesIso` and its quotient equation proving the cycle clauses. Naturality
of totalization is checked on its direct-sum summands, and naturality of homology
uses the existing exact-functor API for both cochain maps and transformations of
the tensor functor. Flatness is transferred through `siteSheafTensorRightIso`.

The proved flat-single normalization gives K-flatness and flat terms. The proved
fixed-factor tensor theorem gives the object comparison. Its naturality in the
flat sheaf follows first on flat-term K-flat representatives, then on all
complexes by cancellation along K-flat resolutions. Localization extends the
cohomology comparison and its naturality to the derived category. Naturality and
the representative normalization give the final formula for every resolution.
The node's proof and dependencies now describe this route.

## Proved and sorry left

Closed 1 of 1 holes:
`SheafOfModules.FlatSingleTensor.ringed_flat_single_tensor_cohomology`
(node `lem-fd-ringed-flat-single-tensor-cohomology`).

No holes remain in the item; no holes or new public statements are added.
This is a proof, not a decomposition.

## No longer needed

Removed the proof import `Sheaf.Algebra.Homology.SiteOneSidedTensorNormalization`
and the direct proof dependency `lem-trf-site-one-sided-tensor-normalization`.
The existing fixed-factor triangulated tensor theorem already gives the
normalized comparison on every complex. Its fixed-left-factor comparison,
K-flat resolution naturality, and localization prove the additional
both-variable naturality here. The old tool-use approval for the one-sided
normalization node is removed. This only removes a direct dependency of this
item; no module is withdrawn and no global unreachability is claimed.

The old proof dependencies `def-weil-sheaf-of-modules-category`,
`def-pc-kflat-complex`, and `lem-weil-pbc-site-derived-tensor-descent` remain
statement dependencies, but need no separate theorem application in this proof.
All existing public imports are preserved. The remaining proof imports provide
the flat-single theorem, additive tensor infrastructure, K-flat resolutions,
exact-functor homology, and localization.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error was found. The six-step plan can be shortened by
reusing the proved `flat_single_derived_normalization` and
`kFlat_fixed_tensor_triangulated` interfaces. The new dependency on
`lem-pur-flat-single-derived-normalization` is a tool for the K-flatness and flat
terms of L[0], not a replacement for the Fourier unit route. The fixed-factor
theorem is already a public statement dependency. No unit statement or unit
proof step is bypassed.

The final item compiled through `lcompile.py` with exit code 0 in 59.7 seconds,
without Lean warnings. The theorem signature and original definition bodies are
unchanged. No delivery from an interrupted attempt was recorded.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
