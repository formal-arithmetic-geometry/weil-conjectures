## What changed

Filled `AlgebraicGeometry.Etale.etaleSumCounitScalar`, preserving its complete
public statement and all existing public imports. All three clauses have complete
proofs. No other library module, statement, or definition is changed.

The first clause follows directly from adjunction mates. The exact-localization
sum adjunction equals the mapDerivedCategory adjunction, as shown by comparing
counits on localized complexes. The scalar/pullback comparison is the mate of the
restriction-of-scalars square, using the proved canonical identification
`scalarPullback_eq`. The generic four-adjunction `scalarOpenInverseMate` and
`uniq_eq_conjugate` helpers identify its second transpose with the inverse of the
specified `sumCoefficientIso`. The mate counit identity and cancellation give the
required equality. These existing proved private helpers are accessed with
`import all`. Their statements are general category theory, without an
open-immersion hypothesis; using them for an etale map does not invoke the open
immersion theorem. The local proved adjunction-comparison and transport helpers
adapt the direct proof now present in `EtaleCounitScalarModel`; that module is
neither changed nor imported. A private noncomputable definition names only the
explicit composite of existing maps, with no witness choice or proof hole.

The second clause uses adjunction injectivity and `mateEquiv_counit`. For the
compact clause, a bounded flat representative on [min(a,b),b] proves that exact
pullback preserves finite Tor amplitude. A proved private equivalence between the
two existing bounded-constructibility predicates allows the source pullback API
to establish constructibility. Naturality and the existing compact coefficient
square then prove the claim for every compactification and normalization record.

Updated the existing DAG proof, dependencies and origin to describe the direct
argument and domain check. The current blueprint Charts route and its summation,
transpose and compact-normalization maps are preserved. The unit realization
record is empty, so no unit's realized step is bypassed.

Validation: the final direct proof, including unused-import cleanup, compiled cleanly
through `lcompile.py` in 42.9 seconds (exit code 0), with no warnings.
All Lean lines are at most 100 characters. The public signature and original public
imports are unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.etaleSumCounitScalar`
(node `lem-sp-etale-sum-counit-scalar`). Its three clauses have complete Lean proofs
from existing declarations. The private helper `boundedConstructible_iff_source`
is also fully proved. Added 0 holes; split off 0 statements. No `sorry` remains
in any delivered Lean file.

The existing `etaleProEtaleCoefficientCompatibility_sum` is applied with its
unchanged statement. No model theorem is assumed for the first two clauses.

## No longer needed

Removed these original proof imports from the item:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.PurEtaleScalarMateProjection`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients`
- `WeilConjectures.ConstructibleSheaf.Defs`
- `WeilConjectures.ConstructibleSheaf.Pullback`

The following original direct DAG dependencies are unnecessary:
`lem-sf-etale-flat-constructible`, `lem-weil-pbc-finite-type-over-noetherian`,
`lem-pc-kflat-resolution`, `lem-sp-etale-pullback-line-flat-model`,
`lem-sp-etale-counit-scalar-model`, and `lem-sp-etale-sheaf-fold-scalar`.
The source bounded flat representative suffices for the domain check; no termwise
constructibility, Noetherian argument, line tensor, K-flat resolution or chain
comparison is needed. The direct canonical-mate argument replaces the two model
and fold nodes. No module is withdrawn; transitive users remain intact.

Proof imports removed during development also include
`Sheaf.EtaleCohomology.Purity.Smooth.EtaleCounitScalarModel` and
`Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafFoldScalar`.

Removed obsolete top-level tool approvals:
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`lem-pur-etale-sum-flat-kflat`, `lem-pur-derived-change-of-rings`,
`lem-pc-kflat-resolution`, `lem-weil-pbc-independent-bounded-flat-kflat`,
`lem-weil-pbc-etale-inverse-image-restriction`,
`lemma-constructible-pullback-stratification`, and
`lemma-constructible-pullback-constant`, and
`lem-weil-pbc-finite-type-over-noetherian`. Their direct calculations are replaced
by the canonical mate identity or the proved source constructibility API.
This does not withdraw their declarations or other uses.

## Where the brief, the DAG or earlier work was wrong

The original seven-step docstring and the four-step model assembly are longer
than necessary with the now-proved canonical scalar-mate helpers. The direct mate
proof uses the same fixed comparisons and counits; it does not choose alternate
maps. The bounded flat model is needed only for the compact coefficient square's
domain. Its terms need not be constructible. Widening the Tor interval to
[min(a,b),b] handles unordered endpoints, including the zero object. No flatness
or projective dimension hypothesis on B/A, nonempty-fibre assumption, or extra
compactification/normalization condition is introduced.

No mathematical statement was disputed or repaired. The current item source exists;
the historical quarantine row does not require withdrawal or deletion.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
