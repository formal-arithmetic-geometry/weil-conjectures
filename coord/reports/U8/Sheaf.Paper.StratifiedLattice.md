## What changed

Replaced the assigned stratification theorem's hole by a complete assembly proof from
etale-local lattice existence, finite etale stratification, pullback, and finite-cover
trace descent. The existing target signature is unchanged. No source-library module is edited.

Proved coefficient-generic private lemmas for the scalar-extension comparison around a
cartesian square, restriction of integral lattices to finite strata, conversion of the
upstream scheme stratification to the recorded stratification type, and their combination.
The comparison uses the actual pullback and composition isomorphisms.

Proved `AlgebraicGeometry.ProEtale.CondensedRing.spectralLisse_etale_lattice` from the
existing normed etale-local lattice theorem. Proved
`AlgebraicGeometry.ProEtale.CondensedRing.spectralFiniteEtaleTrace_lattice` from the
separate trace-image local-freeness assertion below, exact integral localization, the
localization counit and the integral push comparison. Its proof constructs the categorical
image and proves that the adjoint of its actual inclusion is invertible: scalar extension
of that inclusion is both monic and epic. No arbitrary rationalization is substituted.

Both spectral results use proved private coefficient-map congruences and bundled coefficient
diagrams. Equality of the normed and original field/algebra structures transports the whole
lattice property, avoiding large definitional comparisons of extension-of-scalars functors.

The remaining source result is
`AlgebraicGeometry.ProEtale.CondensedRing.continuousFiniteEtaleTrace_lattice`:
a finite etale trace is epic and its integral image is locally free. It assumes the finite
cover and the lattice upstairs; it asserts neither rationalization, stratification nor
etale-local existence. Its new module and DAG node retain the source's sheet-sum trace,
lattice-class sheaf and continuous finite-sum argument, with a complete proof in words.

Validation: `lcompile.py --all` compiled all four delivered modules without errors or
warnings (0.1, 4.1, 7.8 and 7.2 seconds respectively). The assigned theorem signature
was compared with the shared original and is unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.exists_stratified_lisse_integral_lattice`.
The new `spectralLisse_etale_lattice` and `spectralFiniteEtaleTrace_lattice` are proved.
Added one hole, precisely
`AlgebraicGeometry.ProEtale.CondensedRing.continuousFiniteEtaleTrace_lattice`
(node `lem-sfb-continuous-finite-etale-trace-lattice`).

This is a decomposition: one upper hole closed and one strictly smaller hole added,
net zero holes. The original module has zero remaining holes. Across the four delivered
Lean modules there is exactly one sorry, in the named public theorem above. No private
helper or definition contains sorry. Existing dependency holes remain with their owners;
they are not claimed as closed here.

## No longer needed

Removed direct proof imports `Sheaf.Paper.ContinuousCoefficientRealizations`,
`Sheaf.Paper.ContinuousEtaleLocalLattices`,
`WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit`,
`Sheaf.Paper.LatticeSheafLocallyConstant`, `Mathlib.LinearAlgebra.FreeModule.PID`,
`Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`, and `Sheaf.Paper.PadicIntegersInvertEll`.
Their local-lattice, splitting, classification, DVR and finite-sum inputs remain needed
below the new results; none of these modules is withdrawn. The parent no longer needs
the continuous coefficient realization through constant coefficients: the new transport
uses continuousIntegers_eq and equality of continuous coefficient diagrams directly.
The empty `Sheaf.AlgebraicGeometry.EtaleStratifiedFinite` import is replaced by
`WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite`, where the theorem lives.

The geometric assembly uses Mathlib's noetherian scheme instances, so no direct use of
`lem-sc-affine-noetherian-underlying-space` or `lem-sfb-noetherian-space-compact-subsets`
is needed. Exact integral localization replaces the fixed algebraic-closure interface
`det-prop-sfb-qlbar-colimit-x-invert-ell` in this argument.

The sheetwise `lem-sfb-lattice-pullback` and restricted-coefficient
`det-lem-coefficient-heart-common-stratification` interfaces are not applied directly:
`locallyFree_upperStar`, `pullIso`, and `upperStarComp` provide pullback and restriction
with the actual coefficient convention. The source unit's trace, lattice classification
and finite-sum route is retained in the trace-image node.

No module is claimed globally pruned. No quarantined module is changed or withdrawn.
`ContinuousLatticeIntersection` supplies only the generic pushed embedding and its
proved rationalization API; its intersection construction is not used.

## Where the brief, the DAG or earlier work was wrong

The listed etale-stratification duplicate module is empty; its declaration is upstream.
Existing local-lattice and trace interfaces use differing normed, WithAbs, lifted-field
and sectionwise presentations. Direct specialization exhausted kernel reduction budgets
when comparing coefficient maps and inherited field/algebra structures. Proved explicit
congruences and coefficient-diagram equality resolve this without altering definitions,
changing target statements, raising compile limits or splitting a slow proof.

The new assertions were checked on empty schemes, zero rank, varying ranks, identity
covers and covering degrees divisible by l. Trace uses sums and never divides by degree.
The remaining trace-image assertion is a proper source step; the parent additionally
proves geometric stratification and pullback, and the spectral finite-cover module
additionally proves rationalization of the actual inclusion and coefficient transport.

## New nodes

`lem-sfb-spectral-etale-local-lattice` is proved by the normed local-lattice result,
coefficient-map congruence, continuousIntegers_eq and coefficient-diagram transport.

`lem-sfb-continuous-finite-etale-trace-lattice` is the one remaining source assertion:
epimorphy of finite etale trace and local freeness of its integral image. Its node gives
the sheetwise trace, lattice-classification and continuous finite-sum proof.

`lem-sfb-spectral-finite-etale-trace-lattice` is proved from that trace-image assertion
by exact localization, the counit and push comparisons, image factorization and explicit
transport to spectral coefficients. The parent DAG now cites this spectral result.
No existing definitions, source signatures, public imports or consumers change.

The initial preflight requested LeanSearch in addition to Loogle/LeanFinder and grep,
and flagged the extra namespace open. Added the executed LeanSearch results to all three
new nodes and restored the original open command by qualifying pullback names.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
