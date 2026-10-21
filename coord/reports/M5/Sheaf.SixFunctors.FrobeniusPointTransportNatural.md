## What changed

Filled the three canonical object formulas and replaced the single sorry body of
`WeilConjectures.frobeniusPointTransport_natural` with a complete Lean proof.
All existing declaration signatures and both SigmaDerived definitions are unchanged.
There are no source-library edits, definition repairs or forced adaptations.

The chain-level argument uses the prescribed section values of sigma and naturality of
presheaf restriction. A generic localization argument gives the derived transformation.
The specified kappa comparison gives finite and integral transport naturality. Rational
naturality is proved directly: write a localized arrow as an integral arrow divided by
a scalar, prove that the denominator identity is invertible, and cancel its image.

The last two clauses use the new coefficient-passage lemma described below. Both files
compile through lcompile.py --all; the parent check before import cleanup took 34.5 s,
and the new statement module 5.7 s. The final compile after cleanup passed with no diagnostics. The first delivery preflight
requested the additional LeanSearch record and the scoped-attribute change record;
both were supplied before rerunning delivery.

## Proved and sorry left

Closed original holes:
- `WeilConjectures.frobeniusPointRationalPullbackEq`.
- `WeilConjectures.frobeniusPointQbarPullbackEq`.
- `WeilConjectures.frobeniusPointQbarFibreObjEq`.
- `WeilConjectures.frobeniusPointTransport_natural`: its eleven finite, integral and
  rational clauses are proved here; its two coefficient-passage clauses are reduced
  to the strictly smaller named statement below. This fourth closure is a decomposition,
  not a completed coefficient-passage proof.

Added and remaining hole:
- `WeilConjectures.frobeniusPointTransport_coefficient_passage`, node
  `lem-weil-frobenius-point-coefficient-passage`, in
  `Sheaf.SixFunctors.FrobeniusPointCoefficientPassage`.

Thus four original sorry bodies are closed, one separate sorry is added, and one hole
remains in this packet. The item module contains zero sorry. The new statement addresses
only coefficient passage and does not duplicate the parent's eleven proved clauses.

## No longer needed

The parent does not use `lem-weil-point-automorphism-restriction-natural` for finite or
integral naturality: its own sigma uniqueness clauses plus presheaf naturality suffice.
It also does not use coefficient descent for rational naturality: denominator cancellation
works for every rational arrow. The new coefficient-passage node still needs the generic
restriction, scalar-extension and descent lemmas, so none of those modules can be withdrawn.
The unit route is unchanged and no module or declaration is deleted.

Removed redundant private proof imports (their interfaces remain reachable through the
public statement imports or the retained comparison-natural import):

- `Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.Paper.FiniteCoefficientPoint`.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`.
- `Sheaf.Paper.IsomorphismComparisonScalarExtension`.
- `Sheaf.Paper.IsomorphismDerivedPullback`.
- `Sheaf.Paper.PointProEtaleSectionsExact`.
- `Sheaf.Paper.PointSectionsScalarExtension`.
- `Sheaf.TraceFormula.IsomorphismDerivedPullbackComparisonNormalization`.


## Where the brief, the DAG or earlier work was wrong

The previous DAG plan uses coefficient descent for rational naturality, but the actual
statement admits the shorter direct scalar-localization proof above. The remaining
coefficient-passage step has substantial normalization glue: the Frobenius integral
sections use lifted coefficient rings, whereas the generic scalar/descent interfaces use
unlifted coefficient rings. These functors are definitionally identified after scalar
restriction, but their derived comparison and size-descent normalizations still need a
proof. Scratch checks established the functor identification and a generic derived
postcomposition naturality lemma; the full bridge has not been proved. In particular,
it would be incorrect to claim the coefficient clauses follow by a direct exact of the
generic scalar theorem without these comparisons.

No statement was found false and no hypotheses or conclusions were changed. The parent
node's historical H5 record is not the current hole count: the live item copied for this
session had all four original sorry bodies.

## New nodes

`lem-weil-frobenius-point-coefficient-passage` isolates steps 3-4 of the inherited plan:
the explicit rational coefficient-extension square and common-stage algebraic-closure
naturality. Its module has one public theorem and one named sorry with the source and
complete natural-language proof. The three equality-proof arguments avoid importing the
parent module; they are the canonical object formulas already proved there and do not
assume the coefficient square or any parent naturality clause. Edge cases include zero
objects, identity coefficient extension, and morphisms represented only at a larger
finite common stage. The parent node now records the section/localization proof actually
written and this one remaining coefficient-passage dependency. Change record: `coord/changes/M5-frobenius-point-proof-elaboration.md` records the
section-scoped instance/reduction attributes that the static checker classified as an
interface change. No existing definition or statement was changed.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
