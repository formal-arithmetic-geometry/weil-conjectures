## What changed

Proved `AlgebraicGeometry.smooth_genericFibre_of_finiteJet_fitting` in
`Sheaf.AlgebraicGeometry.FiniteJetSmoothGenericFibre`, retaining its exact signature and
`Scheme.powerSeriesJetBaseMap` definition. Added proved private helpers for special-fibre
identification, properness, affine differential/Fitting base change, and the jet relation.
No other Lean module or public interface changes.

Repair of return at da1069bc2: removed the duplicate private `local_depth_eq`.
The already-required `WeilConjectures.AlgebraicGeometry.FibreCohenMacaulayLocus`
contains the same proved `depth_eq_of_ringEquiv`, with independent universes. Changed
that proof import to `import all` and applied its existing helper directly. This also
avoids adding an import of LCICohenMacaulayStalks or changing its private interface.

The proof follows Stacks examples-defos.tex, Tag 0E7T. The CM locus and dimension partition
reduce to constant fibre dimension. Affine base change gives t^(n-1)=b+t^n a. The opens
D(1-ta) cover by properness and make b invertible on the generic fibre. The pointwise
criterion supplies smooth neighbourhoods; Mathlib Zariski locality finishes.

Added proof imports for RelativeDifferentialsAffineSections, QuasicoherentFiniteTypeAffine,
IdealSheaf.Affine, and Finiteness.Cardinality. Updated the existing node's proof route.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.smooth_genericFibre_of_finiteJet_fitting`
(node `lem-sfb-finite-jet-smooth-generic-fibre`). Added 0 holes and split off 0 statements.
No `sorry` remains in the delivered module. The repaired file compiled successfully
through `lcompile.py` on the current library (19.3 seconds, exit code 0).
Existing imported theorem holes remain with
their existing nodes; this delivery proves the item from their declared interfaces.

## No longer needed

Removed duplicate helper `AlgebraicGeometry.local_depth_eq`; its regular-sequence
transport proof is supplied by the existing fibre-CM-locus module.

Removed proof imports:

- `WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete`
- `Sheaf.AlgebraicGeometry.SmoothEtaleLocalSource`
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`

Removed proof dependencies and corresponding obsolete tool approvals:

- `lem-weil-pbc-power-series-field-cohen-regular-complete`: localness suffices for
  properness; LaurentSeries already supplies localization at t.
- `lem-trf-etale-source-smoothness`: Mathlib Zariski source locality suffices.
- `lem-weil-pbc-open-immersion-etale`: the proof uses open immersions directly.
- `lem-sbc-smooth-relative-dimension-permanence`: ordinary smoothness and its Mathlib
  base-change instance suffice after the dimension bound establishes pointwise smoothness.

No module is withdrawn, and these nodes can still be needed by other consumers. The public
DthFittingSmoothLocus import remains because its differential finiteness and
quasi-coherence instances occur in the statement.

## Where the brief, the DAG or earlier work was wrong

No statement correction was necessary. Steps labelled elementary in the original plan
contained substantial affine interface work; this is now proved explicitly in private
helpers, using the existing affine differential-sections, finite-sections, and ideal-comap
nodes. Full geometric-fibre purity is unnecessary: the existing pointwise criterion accepts
the ordinary local fibre dimension obtained from the CM partition. The local-unit argument
is implemented using basic opens, avoiding a separate germ-extension theorem. Cases n=1,
d=0, empty source/special fibre, and arbitrary characteristic are covered uniformly.

Short-route searches: leanfinder returned standard-smooth and smooth-locus APIs, with no
finite-jet criterion; loogle for Fitting and smooth returned no hits; source grep found no
alternative finite-jet theorem. The unit record has no realized step bypassed by this route.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
