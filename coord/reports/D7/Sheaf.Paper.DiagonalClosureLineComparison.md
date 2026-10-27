## What changed

Replaced the hole in `diagonalClosure_lineComparison` by an argument constructing the
adjoint-normalized endpoint, the full-unit-normalized restriction square, and invertibility
of its mate on the single rational root line shifted by two. The original theorem signature
and public import are unchanged.

The line endpoint uses the existing flat single-complex comparison and transports it through
an ordinary normalized line isomorphism. Rational-line flatness follows from the existing
rank-one local freeness, signed tensor inverse, and internal/section module exactness API.
The full-unit assumption identifies the given cochain unit with the canonical one after
transporting its functor equality; no equality of shift structures is assumed.

The direct-image argument uses the actual canonical restriction square. Its normalization
is proved from the right-derived composition unit equations. The mate argument applies the
already proved
`isIso_derivedPushHom_padicAlgCl_of_boundedBelow` to the input with explicit lower bound -2.
This theorem has exactly the required qcqs hypotheses. Only small proved unit calculations
are reused locally; the scalar-basis/copower assembly is not duplicated.

Added `Sheaf.Paper.DiagonalClosureOrdinaryLine` for the ordinary geometric line comparison.
The fully proved endpoint assembly and generic cochain-square normalization live in
`Sheaf.Paper.DiagonalClosureLineEndpoint` and
`Sheaf.CategoryTheory.RightDerivedExactRestrictionNormalization`. Profiling showed repeated
checks of the categorical definitions; the Tate-line, standard localization and derived-functor
definitions are kept folded locally. In particular, folding scalar extension and its left-derived
functor prevents expansion of the balanced scalar construction during mate comparison. Model
transport is proved over abstract abelian categories and an abstract input complex; the
self-contained endpoint and unit calculations are compiled separately.
Updated the item's DAG proof to match this argument. No existing dependency interface changed.

Validation: all four modules compiled through `lcompile.py`; the item compiled in 41.8 seconds
with profiling enabled. Profiling and trace commands were removed for delivery. The delivery
tool performs the final compilation and packet checks on the clean files. The original
existential binder `line` is intentionally unused by the separate mate assertion; the
unused-variable linter is disabled only for the original theorem, preserving its signature.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalClosure_lineComparison`
(node `lem-diagonal-closure-line-comparison`). The item's module has zero remaining holes.

Added one hole:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalClosure_ordinaryLine`
(node `lem-diagonal-closure-ordinary-line`). This is only an ordinary scalar extension
isomorphism with its unit equation; it contains neither derived functors nor a direct image,
a shifted mate, a supplied derived model, or normalization on cochain complexes. Its
source and complete local-root-basis proof are recorded in its docstring and node.
This delivery is a decomposition: one original hole closed and one strictly smaller
hole added, not a net reduction of the hole count. The two additional modules have zero holes:
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalClosure_lineEndpoint` and
`CategoryTheory.rightDerivedExactRestriction_normalization` are proved, with complete
private helper proofs.

## No longer needed

No original import was removed. The existing public uniformizer-frame import supplies
`scalarRightDerived` and is retained.

The parent no longer directly needs `sk-prop-sfb-cartesian-coefficients`
(`Sheaf.Paper.CartesianCoefficients`), `sk-def-sp-tate-twist`
(`Sheaf.Paper.ProEtaleTateTwistsOfUniverses`), or
`def-sfb-comap-upper-star-iso`: there is no inverse-image comparison in the derived-square
construction. The ordinary root-line construction still uses the actual Tate constructions
through its own dependencies; none is withdrawn.

`det-lem-bounded-continuity-direct-image`
(`Sheaf.AlgebraicGeometry.BoundedContinuityDirectImage`) and
`lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact` are replaced as direct proof
dependencies by the proved `lem-sfb-qlbar-direct-image-comparison`
(`Sheaf.Paper.QlbarDirectImageComparison`). This supplies the bounded comparison for the
specified internal-module mate. The parent's proof also does not directly need
`lem-weil-pbc-condensed-qbar-derived-scalar-basis`,
`lem-weil-pbc-condensed-subfield-bounded-copowers`,
`lem-weil-pbc-coefficient-push-copower-criterion`, or `lem-grothendieck-derived-has-coproducts`:
these are the existing comparison theorem's dependencies. No unbounded continuity is used.

No module or upstream declaration is withdrawn. Exploratory imports of
`Sheaf.Paper.ProperIntegralRationalScalarComparison`,
`Sheaf.CategoryTheory.CoefficientPushCopowerCriterion`,
`Sheaf.CategoryTheory.GrothendieckDerivedCoproducts`,
`Sheaf.AlgebraicGeometry.CondensedQbarScalarBasis`,
`Sheaf.AlgebraicGeometry.CondensedSubfieldBoundedCopowers`, and the direct source
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` import were
removed before delivery. The last is already publicly supplied by the bounded comparison.
The new ordinary-line module needs only its coefficient-maps public import; an exploratory
endpoint public import was removed.

## Where the brief, the DAG or earlier work was wrong

The stated continuity plan is mathematically applicable, but the declared generic
ring-sheaf continuity theorem does not directly type the internal-module scalar mate.
The already proved `Sheaf.Paper.QlbarDirectImageComparison` supplies the exact canonical
mate and has the item's qcqs hypotheses. No new continuity assumption or change to the
proper-map source wrapper is necessary.

The compatible ordinary root-line scalar isomorphism, including its actual colimit-leg
normalization, was not supplied by any of the parent's stated dependencies. Local freeness
of the source and target alone does not prove this normalized comparison. That geometric
step is now stated separately. Its edge cases include the bottom field and empty schemes;
there are no additional geometric hypotheses.

## New nodes

`lem-diagonal-closure-line-endpoint` records the proved flat endpoint assembly, and
`lem-right-derived-exact-restriction-normalization` records the proved generic cochain-unit
calculation. Their files lie in the same DAG chapter as the item; neither adds a hole.

`lem-diagonal-closure-ordinary-line`, in
`dag/nodes/sec-six-functors-basics/lem-diagonal-closure-ordinary-line.json`, states only the
ordinary scalar extension isomorphism and its unit equation. Its proof uses compatible
rational root bases on the common root cover, the actual coefficient colimit, normalized
regular-module scalar multiplication, and local detection of isomorphisms. The comparison
is uniquely determined by the scalar adjunction and its underlying colimit leg. No new
mathematical data are chosen in a definition and no change record is required.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
