## Worker report

Item: lem-zl-classical-normalized-two-fibre-comparison. Group NY, stage 2.
The delivery states the comparison, with one postponed theorem and real helper data.
The four modules separate the finite fibre data, finite scalar and common-stage
compatibility data, and the theorem. The theorem docstring contains all seven DAG proof steps verbatim
apart from line wrapping. The source was checked in Bhatt--Scholze 6.8.4(1),(4),
6.8.14(2), 6.8.15 and in the current blueprint's real-mixed-by-curves proof paragraph 1.

Hypotheses and objects:

- `D : FiniteFieldDatum` supplies p, a, q, the finite field and its algebraic closure.
  `[Fact l.Prime]` and `[Fact (l ≠ D.p)]` supply precisely the coefficient condition.
- `Ω`, its field, Q_l-algebra and `IsAlgClosure` instances supply the fixed coefficient
  closure. The recorded small point-fibre interface uses a common universe `u`;
  finite fields use the existing `pbcFiniteField` Shrink models, not new fields.
- `Y₀ : Over (Spec (.of D.k₀))` with locally finite type, quasi-compactness and
  separatedness is exactly the separated finite-type base scheme. `geometricBase`
  uses `(D.geometricFiber Y₀).left`. No k-linearity is imposed on geometric points.
  Frobenius in the node is background notation; no Frobenius equivariance is asserted.
- `E : Padic.FiniteCoefficientFields l Ω` is the finite subextension. The existing
  integers, coefficient uniformizer and continuous rational coefficient sheaf are used.
- `N : NormalizedFibre.Lattice` supplies the actual normalized finite locally free
  etale tower, its real proetale completion cone, quotient maps, and finite-free
  finite stalks. Its integral sheaf is not an arbitrary lattice chosen by existence.
- `K` is in the existing `rationalLisseHeartProperty` full subcategory. `φ` is the
  specified derived realization isomorphism to the degree-zero rational completion.

Clauses:

- `Stage.heart` identifies the entire sf/PBC finite-stage hearts under the recorded
  `(C.stage E).rational.functor`; it is an iff for every raw constructible object.
- `Stage.realization` compares the two actual ambient derived realizations naturally.
  `Stage.model K N φ` composes it with the supplied φ, yielding exactly the requested
  derived isomorphism, rather than only a statement about cohomology.
- `sfDerived` is the actual pullback followed by `pointRationalFibre`, its full
  inclusion and canonical carrier lift. `AtStage.degree_zero` says it is the single
  complex of `sfVector`. `Stage.pbcVector` is the specified normalized PBC fibre
  after the heart restriction of J.
- `AtStage.fibres` is a natural isomorphism on the full lisse subcategory for every
  geometric point. `AtStage.limit` identifies its PBC side with the existing
  `N.rationalFiber`, defined as extension of scalars of the actual inverse limit of
  finite-level etale stalks. Composing gives sf -> V <- PBC with the stated direction
  changed by inversion when needed.
- `AtStage.left_normalization` pins this isomorphism to the recorded normalized sf
  pullback and point comparisons. `AtStage.normalization` pins the limit map to the
  PBC chart prescription and the `PullLimit.projection` maps. No arbitrary stalk is
  commuted with an inverse limit.
- `AtStage.finite_free` asserts both finite generation and freeness over A.
- `AtStage.representatives` supplies the realized morphism for every system map and
  denominator. `AtStage.fractions` asserts both displayed squares have the same
  varpi^(-b) times `NormalizedFibre.rationalLimitMap` formula. Applying these equations
  to the same realized map proves independence of its fractional presentation.
  Naturality of `AtStage.fibres` applies also to maps supplied without a representative;
  the recorded full faithfulness of the completed-system comparison gives fractions.
- `Common` compares the actual common-stage sf point fibre on every realized finite-stage
  lisse model with the recorded common PBC fibre, naturally for every map. Its finite-stage square
  uses `commonVectorScalar`, fixed by the actual `pointQbarFibre` pair-object formula,
  canonical field tensor tower, and cohomology/scalar comparison. The PBC finite-stage inclusion is the actual `stageHeart`; the identification with
  common J is already fixed by `C.pair_functor` and `C.finite_functor`.
  `Scalars.square` additionally spells out the finite coefficient commuting square,
  comparing the canonical `finiteVectorScalar` with the normalized PBC scalar map.
  Its comparison under J is fixed after faithful continuous derived realization by
  the composite of the normalized sf `FieldNormalized.derived` and PBC
  `FieldChange.comparison`, conjugated by `Stage.realization`. The equality of the
  normalized coefficient maps and the equality of the characteristic-parameter/zero
  presentations are explicit. These characterize the canonical comparison, and are
  arguments to the universal square rather than arbitrary maps replacing it.
  Combined with the explicitly asserted `Coherence`, `UnitNormalization`, `Descent`
  and `LocalLimits` of the PBC fibre family, this states compatibility under finite
  extension and passage to Ω, including identity extensions and further enlargements.
  The displayed finite square and common-stage finite-model square both use the
  prescribed maps; they do not introduce unrelated vector-space isomorphisms.
- Rank zero and varying ranks are permitted in the existing lisse and lattice
  predicates; neither a positive rank nor a fixed global rank appears in the theorem.
  `geometricBase` adds only the inherited separation used by the existing fibre API.

The realization families, J, ω, comparison data and their normalization witnesses are
existential data in the conclusion, as in the recorded realization theorems. They are
not hypotheses on Y or K. All universes and variables are explicitly bound and every
module sets `autoImplicit false`. The file locally disables the competing finite-stage
`pbcRationalHasShift` instance where the fixed localized t-structure supplies its shift;
common-stage heart expressions use their existing stage-system shift.

Dependency declarations used (owner modules):

- `Sheaf.Paper.LisseIntegralSmallCoefficients`: the existing normalized adic diagrams
  and stalk limits, via `NormalizedFibre.Lattice`.
- `Sheaf.Paper.SfConstructibleHeart`: `sfRationalHeartProperty`,
  `sfCommonStageHeartProperty`; `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  the actual common-stage category and stage inclusions.
- `Sheaf.Paper.LisseRationalRealization`: `LisseRealization.Family`, normalized point,
  pullback and field-change data, `fibre` and `sections`.
- `Sheaf.Paper.FiniteFieldFiber`: `FiniteFieldDatum.geometricFiber`;
  `Sheaf.AlgebraicGeometry.FrobeniusDetailed`: background geometric Frobenius.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: coefficient integers,
  uniformizer and finite subfields.
- `Sheaf.Paper.RationalCoefficientCategoryComparison`: `FdCoefficientComparison`,
  its finite and common functors and their prescribed equality transports.
- `Sheaf.Paper.FiniteCoefficientPoint`: `pointRationalFibre`,
  `pointRationalFibreScalarIso`, `pointFibreTensorLift_existsUnique`, `pointQbarFibre`.
- `Sheaf.Paper.AdicNormalizedFibreExactness`: `NormalizedFibre.Assertions`, actual
  normalized `omega`, lattice `fiber`, `rationalFiber`, `rationalLimitMap`, `Represents`.
- `Sheaf.Paper.AdicFibreComparisonData`, `AdicFibreComparisonCoherence` and
  `PerAdicNormalizedFibreComparisons`: `Fibres`, `CommonAssertions`, `PullLimit`,
  `Coherence`, `UnitNormalization`, `Descent`, `LocalLimits` and normalized finite-stage
  inclusions/field embeddings. The first two modules have landed definition owners;
  the plain definitions in the last module are now owned by the new
  `def-zl-normalized-adic-fibre-limit-data`, recorded as `existing: true`.
- `Sheaf.Paper.NormalizedClassicalWeilRealization`: `zlRealizationBase`, supplying
  exactly the same geometric base. Its owner is added to stmt_deps.
- `Sheaf.Paper.ConstructiblePullbackTExact`: the actual point rational/common
  realizations and canonical finite-to-common component. Their new definition owner
  is `def-zl-constructible-point-realization-data`, recorded as `existing: true`.
- `Sheaf.Paper.FieldCohomologyScalarExtension`: `fieldDerivedHomologyIso`, the
  uniquely normalized scalar/cohomology map; its owner is added to stmt_deps.
- `Sheaf.Paper.DirectImagesConstructible`: the proved `finiteFieldDatumPrimeUnit`;
  its owner is added to stmt_deps. This adds no geometric assumption.
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`, Mathlib proetale/derived-category
  APIs provide the actual sites and derived objects. Original proof dependencies are
  imported plainly; the theorem's docstring lists every original step and citation.

Edge cases checked before and during writing: Y empty (no points; no chosen point),
rank zero (finite-free rank can be 0), distinct ranks on finitely many clopen pieces,
identity point map, arbitrary scheme map Spec k -> Y, denominator exponent 0 and
nonzero exponents, equal fractions, identity field extension, ramified extensions
(the recorded local-limit scalar data use the ceiling reindexing), and finite-stage
maps represented after further extension. No extra connectedness, positive rank,
nonemptiness, fixed rank or k-linearity hypothesis was added.

Searches:

- msearch leanfinder: "The normalized lisse adic realization identifies the sf point
  fibre and the PBC fibre with the rational inverse limit of finite level geometric
  stalks". Eight irrelevant scheme-normalization/stalk hits; no comparison theorem.
- msearch loogle: "AlgebraicGeometry.Scheme.ContinuousRational.NormalizedFibre.omega,
  WeilConjectures.pointRationalFibre". Project names are not indexed; no hits.
- msearch grep: `normalized.*[Ff]ib|[Ff]ib.*normalized`, AlgebraicGeometry: no Mathlib hits.
- msearch leansearch: "Lisse adic sheaf geometric point fibre inverse limit stalk tensor
  field natural isomorphism". Hits concern ordinary sheaf limits and tilde stalks;
  none compares these two recorded adic point functors.
- rg in WeilConjectures and Sheaf for the node id and normalized/two-fibre comparison
  names: no existing declaration of this statement. Existing adic fibre modules
  construct only the right-hand fibre; the finite coefficient point module constructs
  only the left-hand fibre. Their comparison through J is new here.
- Read all statement dependency node records and full recorded signatures/docstrings.
  Checked the added landed dependencies' transitive statement/proof closure: no cycle
  back to this item. The only direct citer is
  `lem-zl-classical-weil-filtration-heart-transport`.

No statement correction or dependency-record replacement is proposed.
The new definition nodes required for module ownership are listed below.
The supporting declarations belong to the three comparison-data definitions, carry
their owning blueprint and source docstrings, and are listed in their `lean.declarations`.

## New nodes

Preflight requires each supporting module to have its own owning node. The missing
comparison interfaces have therefore been made explicit definition nodes, rather
than leaving unowned helper modules:

- `def-zl-classical-two-fibre-data`: `ClassicalNormalizedTwoFibreData`, declaration
  `WeilConjectures.ClassicalTwoFibre.AtStage`, with `Stage` and the real base, fibre,
  scalar-component and inverse-limit normalization helpers. It bundles the finite
  comparison assertion; it asserts no existence before the parent theorem.
- `def-zl-classical-two-fibre-common-data`: `ClassicalTwoFibreCommonData`, declaration
  `WeilConjectures.ClassicalTwoFibre.Common`, the componentwise Ω comparison and its
  normalization square on actual finite-stage inclusions. Naturality follows from
  the square, the natural finite comparison, and the prescribed scalar components.
- `def-zl-classical-two-fibre-scalar-data`: `ClassicalTwoFibreScalarData`, declaration
  `WeilConjectures.ClassicalTwoFibre.Scalars`, the finite scalar commuting square
  with its J comparison characterized by the normalized derived realization square.

Each definition node records the actual LeanSearch, LeanFinder and Mathlib grep
outputs, the targeted project/DAG search and blueprint search, its source and
blueprint ancestor, explicit statement dependencies, and `import_flags: []`.
The original item's TeX statement and proof remain unchanged. Its statement
prerequisites gain these interfaces and the landed helper owners used above.

`def-zl-normalized-adic-fibre-limit-data` owns the existing real definitions in
`Sheaf.Paper.PerAdicNormalizedFibreComparisons`: `modelH0`, `finiteUnitMate`,
`IsPulledLattice`, the finite scalar quotient/unit constructions, the pull/scalar
chart and lattice predicates, `IsPullLimitNormalized`, `IsScalarLimitNormalized`
and `LocalLimits`. The main declaration is
`AlgebraicGeometry.Scheme.AdicFibreComparison.LocalLimits`. Its source is BS
6.8.4(1),(4), 6.8.14(2), 6.8.15; its exact existing declarations introduce no new
Lean module and no duplicate construction. Mathlib searches return general
profinite/inverse-limit facts, not these adic normalization predicates. The
project/DAG search finds the existing definitions in the theorem module, but no
definition node owning them.

`def-zl-constructible-point-realization-data` owns the existing plain definitions
in `Sheaf.Paper.ConstructiblePullbackTExact`: the finite and common realization
abbreviations, coefficient-model map, common-stage object identification and
canonical finite-to-common scalar component. The main declaration is
`WeilConjectures.constructiblePointCommonStageScalarComponent`. This is exactly
the actual tensor-tower component followed by the inverse of the existing point
object formula, not a replacement comparison. Its source is BS 6.8.14(2),
6.8.15 and the blueprint point-fibre convention. Mathlib searches find scheme
fibres and spectrum constructible sets, not these derived point composites;
project/DAG searches find only the existing theorem-module definitions, without
a definition owner. Its genuine dependency on
`lem-weil-derived-field-scalar-extension-tower` supplies `fieldScalarTower`, the
choice of the uniquely normalized natural tensor-tower isomorphism.

Both ownership nodes contain the actual search outputs and use `existing: true`
with the existing module names, as explicitly permitted in return L. The two
blueprint searches have no matching definition node. No dependency module or
statement correction is needed.

Validation: scompile.py checked every current delivered module separately in both its
sandbox and library import names; all four succeeded without warnings. There is one
postponed theorem, `normalized_two_fibre_comparison`, and no postponed definition data.


## Repair of returned delivery

Return L, immutable head `5a280e077d60`, required repairs (1) and (2).

1. Replaced `lem-per-adic-normalized-fibre-comparisons` in the item's statement
   dependencies with `def-zl-normalized-adic-fibre-limit-data`. Added the same
   owner to `def-zl-classical-two-fibre-data`, whose real normalization helpers
   use `modelH0`, `IsPulledLattice` and `finiteUnitMate`. The original theorem
   remains a proof dependency: its existence result is useful in the proof, but
   the statement quantifies its own fibre/comparison families and does not select
   an object constructed by that theorem.
2. Replaced `lem-a1-constructible-pullback-t-exact` with
   `def-zl-constructible-point-realization-data` in the item and in
   `def-zl-classical-two-fibre-data`. Also repaired the same ownership citation in
   `def-zl-classical-two-fibre-common-data`. The point realization abbreviations
   and finite-to-common scalar component now have the requested definition owner.
   No t-exactness theorem is used merely to name these plain composites.

The genuine dependencies `lem-weil-cohomology-commutes-scalar-extension` and
`lem-weil-structure-direct-images-constructible` remain. The former supplies
`fieldDerivedHomologyIso` by its uniquely normalized existence theorem; the
latter supplies the actual `finiteFieldDatumPrimeUnit` proof term.

Advisory, non-vacuity of `Scalars.square`:

- `_he` is available for every `e`. In
  `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`,
  `GeneralAlgebraicallyClosedCoefficients.scalarExtension_parameter_independent`
  applied to `p = 0`, `q = D.p`, with `Nat.Prime.ne_zero` and `hl.out`, has second
  component the equality of precisely the two `sfRationalScalarExtension`
  functors used in `Scalars.square`. Its proof is `rfl` with the existing
  transparency options. Transport `e` across this equality to obtain `eD`;
  equality elimination gives `HEq e.hom eD.hom`. This applies to every field
  inclusion, including the identity, and every object, including zero.
- `_hc` is forced by normalization, not an additional restriction on the families.
  `LisseRealization.FieldChange.normalized` in
  `Sheaf.Paper.LisseRationalRealizationData` and
  `ContinuousRational.FieldChange.normalized` in
  `Sheaf.Paper.ContinuousRationalDerivedRealization` both say, for every proetale
  object U, coefficient section s and point x, that the image evaluates to
  `i (rationalCoefficientValue ... s x)`. The underlying scheme of the two base
  records is definitionally `(D.geometricFiber Y₀).left`. Apply `Sheaf.hom_ext`,
  sectionwise extensionality, and `rationalCoefficientValue_ext` from
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientGeneralPullbackIso` to those two
  normalization equations. This gives precisely `_hc` for the same inclusion i.
  This argument includes empty proetale objects: extensionality of functions on
  the empty space still identifies their unique continuous functions.

Thus neither `_he` nor `_hc` can make the square vacuous. The parameter `b` is
supplied for all inclusions by the theorem's explicit `FieldNormalized` conjunct.
The faithfully realized equation `_hj` specifies the intended scalar mate under
J; it is unchanged from the independently checked mathematics. `Stage.realization`
remains an isomorphism as the node requires; its residual right-hand scalar
ambiguity is allowed by “is isomorphic”, as noted in the review.

The retained sandbox is the returned delivery. The read clone has none of its
four new modules; the current server source lookup for
`Sheaf.Paper.ClassicalNormalizedTwoFibreComparison` also reports the module
unavailable. Thus no competing landed copy needs to replace these statements.
The repair changes DAG ownership and report content, retaining the reviewed Lean
signatures and the item's original statement/proof. The prescribed delivery
wrapper will rebase this concrete repair on the current live branch.

Repair validation: all four delivered Lean modules passed scompile.py in their
sandbox and library names with no errors or unexpected warnings. The first
deliver2.py --no-push run passed preflight and compilation (d877ccd2464); a final
dry run follows the complete existing-declaration signature check.

## Second reading by NY

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
