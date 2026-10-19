## Worker report

The module `Sheaf.Paper.SmoothProperPurityHypotheses` states the three clauses of
`lem-weil-smooth-proper-purity-hypotheses` with proof `sorry`; it proves nothing at
stage 2. The binders are the finite-field datum `D`, prime `l` with `[Fact l.Prime]`
and `hl : l ≠ D.p`, a proper geometrically connected `X₀ : Over (Spec (.of D.k₀))`,
and an algebraically closed coefficient field `Ω` with its field and algebra
instances. The explicit smoothness and pure-dimension hypothesis is
`hsmooth : D.IsSmoothOfPureDimension X₀ d`.

Clause 1 is rendered by the first existential: `G` is a functor between the two
`finiteTorFieldCoefficientCategory` common-stage constructible categories; `adj` is
an adjunction `zlCommonStageShriek ... ⊣ G`, with the specified identity
compactification `Compactification.ofIsProper X₀.hom`. No ambient exceptional
adjoint class occurs as a hypothesis. Clause 2 is rendered by the existential
`e`, whose domain and codomain are the two Frobenius pullback composites. Its
counit equation is the displayed `∀ K`: the map of `e.hom.app K` under the
compact-support functor followed by the adjunction counit equals the inverse of
`zlShriekFrobenius` followed by the Frobenius map of the counit. The next conjunct
exists `omega : sfCommonStageWeilComplex ...`; its carrier is exactly `G.obj` of
the constant algebraically closed Weil complex at the point, and its structure
is heterogeneously equal to `e.app` at that constant carrier composed with
`G.mapIso` of the constant Weil structure. Thus the canonical structure is
specified rather than chosen arbitrarily. Clause 3 is the final universal
quantifier over `compact : Bool` and `i : ℤ`; it asserts
`FiniteDimensional Ω` for the `.a` module of
`globalGeometricFrobeniusQbarCohomology` applied to the constant complex, for
both ordinary and compact support and every degree.

The item uses these recorded declarations: `WeilConjectures.FiniteFieldDatum`
from `Sheaf.Paper.FiniteFieldFiber`; `WeilConjectures.generalAlgebraicallyClosedConstructibleCategory`
from `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`;
`WeilConjectures.FiniteFieldDatum.IsSmoothOfPureDimension` from
`Sheaf.Paper.GeometricHypotheses`; the exceptional inverse-image interfaces in
`Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`;
`WeilConjectures.finiteTorFieldCoefficientCategory` from
`Sheaf.Paper.FiniteTorAmplitude`; compact support from
`AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport` in
`Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport`; `zlCommonStageShriek` and
`zlShriekFrobenius` from `Sheaf.Paper.CommonStageWeilShriek`;
`constantWeilAlgebraicallyClosedComplex` from
`Sheaf.Paper.ConstantWeilStructure`; `sfCommonStageWeilComplex` and its
Frobenius pullback from `Sheaf.Paper.SfWeilSheafComplex`; and the point/cohomology
interfaces from `Sheaf.Paper.CommonStageCompactWeilCohomology`.

The dependency `def-weil-global-geometric-frobenius` retains NZ's landed
`Sheaf.Paper.GlobalGeometricFrobenius` module and its original primary declaration,
recorded signature, authorship, and two finite-stage declarations. This delivery
appends the three algebraically closed declarations in `section Qbar`, with
independent universe `v`, to that same module. The dependency record lists all five
declarations. `globalGeometricFrobeniusQbar` is exactly the canonical
endpoint-transport, Frobenius-cohomology transport, and Weil-structure composite
for either support convention; the other two declarations take its homology in
every degree and package the resulting module and endomorphism. The item imports
`Sheaf.Paper.GlobalGeometricFrobenius` directly.

Searches for existing notions were made before writing. `msearch.py` Lean Finder
was queried with “smooth proper etale cohomology finite dimensional exceptional
inverse image Frobenius”; it returned only ring-theoretic Frobenius and étale
smoothness declarations, with no six-functor or finiteness theorem. Loogle was
queried for `FiniteDimensional, CategoryTheory.Adjunction` and returned no hits.
Mathlib grep for `dualizing|exceptional inverse image|WeilComplex` returned no
matches. Repository `rg` searches found the existing common-stage and compact
support declarations listed above, and no declaration of
`smoothProperPurityHypotheses`; the Qbar Frobenius extension was consequently
added as the authorized dependency repair. The combined dependency module and the item are checked with `scompile.py`.

Edge cases checked include `d = 0`, the point case, and a smooth proper elliptic
curve (ordinary dimensions 1, 2, 1 in degrees 0, 1, 2); geometric connectedness
excludes the empty scheme. `compact = false` and `compact = true` are both
handled by the Qbar Frobenius definition, and the item quantifies all
`i : ℤ`, including degrees outside the cohomological range. The hypotheses do
not impose an ambient exceptional-adjoint admissibility class.

No `STATEMENT-DISPUTED` flag is needed. The inherited stage-1 review records the
source error that ambient admissibility is false for elliptic curves; this module
retains the corrected unconditional constructible-adjunction statement.

## Dependency modules

`def-weil-global-geometric-frobenius`: the finite-stage operator cannot accept the
common-stage `sfCommonStageWeilComplex` required by this item. The extension is
appended to its existing `Sheaf.Paper.GlobalGeometricFrobenius` module, preserving
both landed finite-stage constructions and recording a superset of declarations.
The three added definitions use the canonical endpoint equalities and specified
support-dependent transports; none chooses an arbitrary Frobenius operator.

## Repair of H13 and H9

H13: removed `GlobalGeometricFrobeniusQbar.lean` from the packet, appended its three
definitions to NZ's existing module in `section Qbar` with `universe v`, and kept
NZ's binding with the two old plus three new declarations. The original two
signatures, bodies, and docstrings are unchanged. The item now imports the original
module, preserving ownership of the module used by `TwFrobeniusAction`.

H9: removed the six imports named by the return: `PoincarePointFiniteness`,
`PoincareDualitySetting`, `Etale.Derived.Package`, `FourierInversion.OtherSections`,
`ConstructibleExceptionalAdjunctionCoefficients`, and `SfIntrinsicCompactSupport`.
The theorem signature and proof docstring are unchanged.

## Self-check by Q127

This is the author's repair check; independent review belongs to the maintainer.
The unchanged statement still has all the field and geometric hypotheses, the
constructible right adjunction, the exchange isomorphism pinned by its counit
identity, the Weil carrier equality and structure `HEq`, and finite dimensionality
for both support conventions in all integer degrees. The dependency record owns
all five declarations in one module and preserves the original finite-stage API.

## Second reading by Q127

I reread the item node and `SmoothProperPurityHypotheses.lean` clause by clause. The
binders render the fixed finite-field datum, prime and inequality, proper geometrically
connected `X₀`, algebraically closed coefficient field, and the smooth pure-dimension
hypothesis without adding an ambient admissibility class. The first existential is the
constructible-category functor and its right adjunction to the identity compactification
shriek functor. The second is the Frobenius exchange isomorphism; its displayed counit
identity fixes the canonical mate. The `omega` conjunct gives exactly the transported
constant point carrier and pins its Weil structure by `HEq`. The final quantifiers cover
both support choices and every integer degree, with the Qbar global Frobenius action and
finite-dimensional coefficient module. The dependency module retains NZ's two landed
finite-stage definitions and adds exactly the three Qbar declarations needed by this
specialization. No mismatch was found and no statement change was made.
