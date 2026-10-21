## What changed

In `lean/Sheaf/Paper/AmbientCompleteRawSystem.lean`, filled five of the seven original
proof holes, preserving all existing declaration signatures, definitions, attributes,
and public imports. Added private proof imports of `Sheaf.Paper.PbcScalarExtension`
and `Mathlib.RingTheory.Localization.BaseChange`.

The completeness proof first identifies the two published completed coefficient maps.
The finite comparison is the sheafified constants-to-functions map, so its naturality
identifies the finite scalar maps. Uniqueness by finite limit projections then proves
that `pbcCompletedScalarMap` equals `pbcScalarCoefficientMap`. The existing theorem
`pbcScalarPreservesComplete` applies to exactly this tensor functor.

The integral unit and associator are componentwise lifts of the specified ambient
isomorphisms to the full complete subcategories. Their normalization equations hold
by construction; applying the faithful inclusion proves uniqueness. The
integral/rational comparison uses the prescribed inverse integral unit when the
fields agree and the chosen strict factorization equality otherwise.

For the rational associator, form the actual composite of the three integral/rational
comparisons and the localized integral associator. A proved private lemma extends
integral naturality to arbitrary localized arrows: `IsLocalizedModule.surj` clears a
single denominator, the corresponding scalar identity is invertible, and its image
can be cancelled. This works for arbitrary target functors and does not assume that
they are additive. Unchanged objects then give existence and uniqueness with exactly
the required component formula.

The complete module compiled through `lcompile.py` with exit code 0 and no warnings. No new modules or intermediate holes were introduced. The proofs
follow the existing declaration docstrings; the definition node has no numbered
proof plan to replace, and no dependency or construction route was changed.

## Proved and sorry left

Closed five original holes:

- `AlgebraicGeometry.Scheme.pbcAmbientCompleteTensor_preserves`.
- `AlgebraicGeometry.Scheme.pbcAmbientCompleteIntegralUnit_exists`.
- `AlgebraicGeometry.Scheme.pbcAmbientCompleteIntegralComparison_exists`.
- `AlgebraicGeometry.Scheme.pbcAmbientCompleteIntegralAssociator_exists`.
- `AlgebraicGeometry.Scheme.pbcAmbientCompleteRawAssociator_exists`.

Two original holes remain unchanged, both attached to
`def-sbc-ambient-complete-raw-scalar-system`:

- `AlgebraicGeometry.Scheme.pbcAmbientCompleteRaw_exists`: existence and strict
  uniqueness of rationalized tensor extension on the ambient complete category.
- `AlgebraicGeometry.Scheme.pbcAmbientCompleteRaw_laws`: additivity, literal identity
  transitions, both associator unit equations, and the four-field pentagon.

Added holes: zero. Split off: zero. This is a partial proof delivery, not a proof of
all the raw system laws. The existing dependency `pbcScalarPreservesComplete` is used
as stated; this report does not claim that all of its transitive dependencies are closed.

## No longer needed

None. No existing import, node, module, or declaration is withdrawn. Both original
public imports are required for the unchanged statements and canonical ambient
unit/associator. The two new private imports supply the completeness theorem and the
module-localization denominator argument respectively. The constructible raw scalar
system is not substituted for the ambient complete one.

## Where the brief, the DAG or earlier work was wrong

No statement or definition error was found. The recorded coefficient maps have
different presentations, so completeness preservation does not apply by reflexivity;
the delivery supplies a proved private equality rather than adding a comparison hole.

Searches: `msearch.py` LeanFinder for restriction of natural isomorphisms to full
subcategories found Mathlib `ObjectProperty.isoMk` and `liftCompιIso`; the Loogle
query `CategoryTheory.ObjectProperty.isoMk` confirmed its exact signature. Direct
`rg` in Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` found the analogous integral
unit/comparison/associator proofs in `FiniteStagePairCategory`, the ambient
`pbcScalarPreservesComplete` theorem in `PbcScalarExtension`, and the localization
base-change instance used with `IsLocalizedModule.surj`. `PbcFiniteRawScalarComparison`
and the finite-stage rational scalar system concern constructible stages and cannot
supply the two remaining ambient complete statements as written.

The new private proofs apply without excluding repeated coefficient fields, zero
objects, or zero localized Hom modules. The comparison proof treats equal and
unequal fields explicitly. The denominator proof only uses that a denominator lies
in the localized submonoid, including degenerate localizations.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
