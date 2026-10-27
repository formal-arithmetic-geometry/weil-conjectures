## Worker report

The delivery states `WeilConjectures.isomorphismPullback_tExact_coefficients` in
`Sheaf.Paper.IsomorphismPullbackTExactCoefficients`. Its proof is the only `sorry`.
The structures and predicates package the clauses of this one node. The integral associator and
unitor adapters contain real compositions of the existing normalized scalar maps;
the residue inverse is extracted from the given unit proof. No object or functor
is selected from an undetermined existence assertion.

The live `reviewed` PASS by NT-cc-NE-fa5229f71 reviews the stage-1 split.
The node had no `lean`, no `reviewed_lean`, and no repair note. This delivery adds
its first Lean record and leaves its statement and proof unchanged.

Hypotheses and objects:

- The prime is `(l : ℕ) [Fact l.Prime]`; the fixed algebraic closure is
  `(Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]`.
- `X Y : Scheme.{u}`, `g : X ⟶ Y`, and `[IsIso g]` give the stated isomorphism.
  `[IsNoetherian X] [IsNoetherian Y]` express noetherianity (including
  quasi-compactness); `_hDimX`, `_hDimY` bound topological Krull dimension.
- `hX`, `hY` state invertibility of l at every local ring. The actual
  `isomorphismPullbackResidueUnits` transports that unit through `W.residue w`
  to supply the uniquely determined residue-field inverse expected by the
  published pullback. These are conclusions of the given hypothesis, not
  additional assumptions.
- `E : AlgebraicallyClosedCoefficients.Index l Ω` is every finite subextension.
  `Coefficient.{u} l Ω E` is the existing Shrink model via its algebra
  equivalence, with the existing conjugated `coefficientInclusion`. Thus the
  closure universe v is independent of the scheme universe u, and no finite
  subextension, inclusion or identity case is excluded.
- Completed rings, quotient towers, uniformizers and integral objects are exactly
  those used by `sfIntegralConstructibleCategory`, `constructibleIntegralPullback`,
  `integralPullbackScalarComparison`, and `sfConstructibleIntegralScalarExtension`.
  Rational objects and arrows are exactly `sfRationalConstructibleCategory`, with
  its raw tensor Hom groups and no Karoubi envelope.

Conclusion, clause by clause:

- Mapping the integral category into the integral category is already the type of
  `constructibleIntegralPullback`; no unrelated functor is quantified.
  `S E` has `integral_linear` for the constant-section action of
  `Padic.coefficientExtensionIntegers`, `integral_exact` for distinguished
  triangles, and `integral_tExact` for both standard halves in every degree.
- `S E` has the natural derived isomorphism `comparison` from the exact termwise
  inverse image into that very completed pullback. `comparison_normalization`
  fixes its hom component to `inverseImagePullbackComparisonDerived` on each
  integral object. Consequently it is the canonical comparison, not an arbitrary
  natural isomorphism with the same endpoints. Its inverse is the lambda of the
  node. `shift_normalization` is `NatTrans.CommShift` with the termwise shift of
  `inverseImageIntegralDerived` and the inherited inclusion shifts; this fixes
  `integralShift` to exactly transport of the termwise shift through lambda.
- The integral standard halves are the existing `sfIntegralStandardClass`:
  vanishing of ambient cohomology above, respectively below, n. The rational
  halves are the existing `sfRationalStandardClass`: isomorphism closure of the
  integral halves. Preservation for `b : Bool` states both inequalities. This is
  precisely t-exactness for the bounded standard structures with those halves;
  the theorem does not assert or choose a different structure.
- `rationalDerivedPullback` is the already prescribed raw rationalization on
  objects and ALL tensor Hom arrows (`rationalDerivedPullback_existsUnique`).
  `rational_shift_normalization` localizes the integral shift at 1; the CommShift
  laws fix its values at every integer. `rational_exact` and `rational_tExact`
  give exactness and t-exactness of that prescribed functor.
- For every E≤L, `B E L h` has an integral natural isomorphism whose
  `integral_normalization` equals the existing `integralPullbackScalarComparison`
  on each object. This is the actual completed alpha from
  `scalarPullbackCompleted`, rather than chosen objectwise comparison maps.
- `B E L h` has `rational_laws`, the predicate
  `isomorphismPullbackRationalScalarLaws` applied directly to the existing
  `rationalPullbackScalarComparison`. Its second conjunct fixes that prescribed
  natural isomorphism's components to Q_L of the integral components. Naturality
  of this existing natural isomorphism quantifies over every rational morphism. The existing
  `sfRationalScalarExtension_existsUnique` sends a pure scalar tensor to its
  field-inclusion image; the existing pullback's pure-tensor formula fixes the
  other part. In particular the fraction u/varpi_E^n goes to the integral image
  of u times the image of varpi_E^(-n) in L, including ramified extensions. No
  restriction to integral arrows or a dense family of rational arrows is made.
- `integral_shift` states exact-natural-isomorphism compatibility with the
  normalized integral transition shifts. The first conjunct of `rational_laws`
  applies `isomorphismPullbackShiftSquare`, whose full definition is Mathlib's
  `NatTrans.CommShift` with the two composite shift instances supplied explicitly.
  It uses the same two chosen pullback shifts and existing normalized transition
  shifts, and quantifies over every integer shift and every object. It states
  the whole-map square, rather than agreement after taking cohomology. Both
  predicates contain real proposition definitions and introduce no new map.
- `IsomorphismPullbackCoefficientCoherence` gives `integral_unit`,
  `integral_tower`, `rational_unit`, `rational_tower` for the same family S and B.
  The unit equations express identity after the canonical tensor unitors (the
  tensor presentations do not make identity extension literally the identity).
  The tower equations use precisely balancing of ordinary derived tensor
  transported by the published completion comparisons and then rationalized.
  `isomorphismPullbackIntegralAssociator`, `sfIntegralScalarComp`,
  `GeneralAlgebraicallyClosedCoefficients.associator` are these canonical maps,
  not new existential associators. This is the completion-conjugated meaning of
  the prop-weil-pbc-scalar-extension associators explained in proof step 4.

Dependency declarations inspected and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, with the underlying existing integer,
  uniformizer and quotient constructions publicly retained.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`:
  `integralConstantToCompletionOfUniverses`, the limit lift of the quotient cone.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible`,
  `sfIntegralConstructibleCategory` (actual completeness and uniformly bounded
  constructible finite reductions).
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleLocalization`, `sfRationalCoefficientEquiv`,
  `sfRationalScalarExtension`, and their normalization specifications.
- `Sheaf.Paper.IntegralTStructure`: `pbc_integral_tstructure`;
  `Sheaf.Paper.LocalizedTStructure`: `pbc_localized_tstructure` are proof imports.
  Their old interfaces use the etale-origin completed category. This mismatch
  was already noted in the stage-1 review. Rather than substitute that category,
  the conclusion uses the existing intrinsic cohomological half predicates from
  `Sheaf.Paper.SfConstructibleHeart` (`sfIntegralStandardClass`,
  `sfRationalStandardClass`). T-exactness is preservation of those exact halves;
  no new existence theorem or private copy is needed. The general transport in
  `integralStratifiedPerfectDetailed` and the finite-type-only theorem
  `sfIntegralStandardTruncations` were inspected; no extra geometric finite-type
  hypothesis is added to this item.
- `Sheaf.Paper.DerivedPullbackTensorHom`:
  `constructibleIntegralPullback`, `rationalDerivedPullback`,
  `integralPullbackScalarComparison`, `rationalPullbackScalarComparison`, and
  the unique object/all-arrow normalization statements for these constructions.
- `Sheaf.Paper.IntegralScalarExtensionUniverses`:
  `integralScalarExtensionOfUniverses`, retaining the original completed scalar
  functor on equal-universe small coefficient models.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`:
  `scalarPullbackCompleted`, `scalarOperationsOrdinary_tower`.
- `Sheaf.Paper.PbcScalarExtension`: `pbcCoherentScalarExtension` and its
  balancing associators. `Sheaf.Paper.SfScalarExtensionComposition` supplies
  their actual intrinsic completion-conjugated forms `sfIntegralScalarComp`,
  `sfIntegralScalarUnit`, `sfRationalScalarComp`, `sfRationalScalarUnit`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `integralTransition`,
  `transition`, their normalized CommShift instances, `associator`, `unitor`.
- `Sheaf.Paper.InverseImagePullbackComparisonDerived`:
  `AlgebraicGeometry.ProEtale.inverseImagePullbackComparisonDerived`, with
  `inverseImageIntegralDerived` (exact sectionwise inverse image with the
  completed limit coefficient action) publicly imported from its owning module.
- The scheme-properties node is a convention/pointer collection; Mathlib
  `Scheme`, `IsIso`, `IsNoetherian`, `topologicalKrullDim` and stalks are used.
  Mathlib's `TStructure` definition and standard classes were inspected;
  `NatTrans.CommShift` and `Functor.IsTriangulated` render exact shifts.
- All stated proof dependency modules are imported, including the isomorphism
  comparison normalization, scalar realization, finite-free completed comparison,
  semilinear localization and DVR statement. The exact derived factorization is
  Mathlib `Functor.mapDerivedCategoryFactors`; it is already imported by the
  exact inverse-image interface. `lem-pod-completed-scalar-extension-texact` has
  no recorded declaration yet and therefore contributes no import.

Added statement dependencies are the already landed owning nodes for the standard
classes, small coefficient stages, scalar associators, and specified inverse-image
comparison: def-weil-constructible-standard-tstructure,
def-weil-algebraically-closed-coefficients,
lem-weil-scalar-extension-composition,
def-weil-inverse-image-pullback-comparison. No new node or dependency module is
required and no existing dependency binding is replaced.

Edge cases checked: g=id, X and Y different but isomorphic schemes, empty schemes,
zero objects, both Bool halves, arbitrary negative/zero/positive cutoffs and shifts,
E=L including h=le_rfl, repeated fields in towers, nontrivial ramification,
uniformizer-torsion integral arrows, and independent scheme/closure universes.
Inverting the source uniformizer uses its nonzero image in the target field, not
an incorrect equality with the target uniformizer. No arbitrary geometric map,
finite-type-over-field hypothesis, flat-cohomology hypothesis or Tor restriction
is inserted.

Searches for an existing statement:

- `msearch.py leanfinder`: "completed integral pullback along scheme isomorphism
  is t-exact and coherently commutes with rational coefficient extension".
  Eight hits, on integral scheme morphisms and unrelated pullback isomorphisms;
  none states this completed constructible coefficient package.
- `msearch.py leansearch`: "Derived pullback along an isomorphism with completed
  l-adic coefficients is t-exact and compatible with rational scalar extensions
  and shifts". Eight hits, including ordinary sheaf pullback identity and
  pullback-shift comparisons; none matches this statement.
- `msearch.py loogle`: initial unqualified mapDerivedCategory query reported an
  unknown identifier; the fully qualified quoted
  "CategoryTheory.Functor.mapDerivedCategory" returned twelve exact-derived-
  functor declarations, used by the termwise functor. The quoted
  "CategoryTheory.Functor.IsTExact" returned no hits. No complete match.
- `msearch.py grep`: `isomorphism.*(t.exact|completed)|semilinear.*localization|mapDerivedCategory`
  in CategoryTheory returned five unrelated Guitart/left/right derived hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`: searched the proposed full
  names, `sfIntegral.*[Tt]Structure`,
  `constructibleIntegralPullback.*[Cc]ommShift`,
  `rationalDerivedPullback.*[Cc]ommShift`, and isomorphism/pullback/t-exact
  phrases. The automorphism-stage equivalence is on finite-type geometric
  finite-field schemes, the constructible-pullback t-exact statement assumes
  the same finite-field setting, and field Weil shift data does not state
  t-exactness and this scalar family. None matches arbitrary isomorphic
  noetherian finite-dimensional schemes. The item id has no upstream match.
  Existing standard classes and normalized comparisons found by these searches
  are reused as listed above.

No statement correction and no STATEMENT-DISPUTED flag. The module docstring and
the theorem docstring preserve the eight-step proof plan, including the signed
whole-cone calculation and the all-fraction localization argument.

Validation: the complete module compiled cleanly with `scompile.py`, both in the
sandbox namespace and as `Sheaf.Paper.IsomorphismPullbackTExactCoefficients`.
The only postponed proof is the named main theorem. All variables and universes
are explicit; no auto-bound implicits, private definitions or local instances
are used. The generic shift-square helper only exposes Mathlib's existing
composite-shift definition, while the scalar-laws predicate only groups this
node's two rational-comparison clauses. They are owning helpers, not new notions
requiring separate DAG nodes.

The first dry run found a cycle from the optional added constructible-heart
node back to this item. A focused DAG search found the already landed
`def-weil-constructible-standard-tstructure`, whose lean record names exactly
`sfIntegralStandardClass` and `sfRationalStandardClass` in the same module.
Its full dependency closure was checked and does not reach this item. The
added dependency now names that definition node; no new node, private copy or
change to any existing dependency record was required. The theorem-node warning
for scalar-extension-composition concerns its canonical associator definitions,
which the statement uses; that node is already landed.

## Second reading by Q83

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
