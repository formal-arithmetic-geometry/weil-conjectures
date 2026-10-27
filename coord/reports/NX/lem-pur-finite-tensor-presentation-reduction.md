## Worker report

The delivery states finite coefficient reduction of all signed Tate twists, integer shifts,
tensor constraints, geometric pullback composition, and the canonical purity reassociation.
The source is the current main-20261015 blueprint proof Step 2 named in the item, together
with the item's nine expanded proof steps. The item statement is unchanged.

The module uses fixed-scalar coordinates of the published intrinsic derived category.
This is the specified `sfIntrinsicModuleEquivalence` / `sfIntrinsicDerivedEquivalence`,
not a replacement coefficient category. `finiteTensorReduction` is the actual left adjoint
of exact scalar restriction. `SupportedEtaleTensorOrigin.scalarPresentation` is its
unit-normalized comparison with the existing intrinsic `finiteReduction`. Every tensor
is the native tensor used by the recorded `ProEtale.derivedTensor`.

Hypothesis and clause correspondence:

- The algebraically closed finite-field base, prime different from its characteristic,
  finite coefficient extension, valuation-ring quotient and positive level n are the
  fields of `PurityFiniteSetting P`. Here n is `P.level`; `m`, `hm : 1 ≤ m`, and
  `hmn : m ≤ P.level` give exactly the two positive quotient levels. The ring map is
  `P.finiteReductionRingHom m hm hmn`, not a supplied arbitrary ring map.
- Separated finite-type k-schemes are the `Over`, `LocallyOfFiniteType`, `QuasiCompact`
  and `IsSeparated` structure-morphism binders of the final theorem. The morphism is
  over that base. The final `K` has the existing `finiteTorConstructible` predicate
  after the specified intrinsic realization. This is precisely the ordinary bounded
  constructible finite-Tor subcategory, not an adic or completed category.
- Preservation of that subcategory is the recorded `finiteReduction_preserves_ctf`
  in `Sheaf.Paper.FiniteReductionRootCharts`. Preservation of the *same* specified Tor
  interval is the existing `ProEtale.scalarExtensionFunctor_preserves_constructible_tor`
  in `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: its last conclusion retains its
  input integers a,b. These existing declarations are reused rather than duplicated.
- `finiteTensorFirstLine` transports only the published n+1 coefficient indexing to
  the actual positive level n. Its object is the ordinary integral line tensored with
  the actual coefficient quotient. `finiteTensorLine` uses the published
  `coefficientTwistLine`: ordered positive powers, zero unit, and internal dual powers.
  `finiteTensorFixedSheaf` and `finiteTensorFixedLine` only apply the specified inverse
  realization and the degree-zero single functor.
- `FiniteTensorLineMapsNormalized` gives the four determining ordinary equations:
  quotient on the zero line; balancing the integral tensor in degree one; ordered
  pure tensors on positive powers; and evaluation on negative powers. The HEq in degree one transports the predecessor indexing. In positive and negative
  clauses it only identifies the underlying section of exact restriction with the same
  section of the target line before taking a tensor or evaluation; it adds no choice
  or coefficient-flatness assumption.
  `FiniteTensorLineComparisonNormalized` fixes the derived arrow by its actual adjoint
  on single complexes. The uniqueness statements specify the objects subsequently
  extracted by `choose`; no object is selected from a bare existence assertion.
- `FiniteTensorCoreNormalized` is the complete K-flat representative/counit square.
  `finiteTensorCochainComparison` is the native scalar-first cochain comparison,
  carrying its ordinary balancing formula and total-complex signs.
- `finiteTensorTwistShiftComparison`, with all `r s : ℤ`, is a natural isomorphism in
  L between exactly Q(L(r)[s]) and (QL)(r)[s]. Its unique-existence statement fixes
  each component to the scalar shift, inverse binary tensorator, and specified line
  map, in that order. Thus its choice has no freedom beyond that formula.
- Tensor associativity and both unit equations are the `CoreMonoidal` fields of
  `finiteTensorCore`; `finiteTensorStructuralCoherence` gives symmetry and the native
  simultaneous tensor-shift square for arbitrary integer shifts. The native shifts
  include zero, addition and the two-order Koszul-sign laws.
- `FiniteTensorFrame`, `existsUnique_finiteTensorSheafProducts`, and `finiteTensorProduct`
  specify signed addition on coherent local bases and then through the canonical
  `cupSingleTensorMap`. The derived comparison is uniquely specified by the actual tensor-to-single arrow
  followed by that sheaf product. Its type has a named alias to avoid repeatedly
  expanding the derived monoidal instances during kernel checking. `finiteTensorTwistAdditionCoherence` is its reduction square
  for every pair of integers, including cancellation and zero.
- `finiteTensorPullbackComparison` is the fully faithful preimage of the *recorded*
  `finiteReductionPullbackComparison`, conjugated only by realization/scalar units.
  `finiteTensorPullbackTensor` supplies the finite quotient-ring finiteness proof
  internally for the published tensor-pullback map; it adds no hypothesis.
  `finiteTensorPullbackCoherence` gives its tensor square and its square with the
  existing `compositionFixedPullbackComp`, including identity/composable pullbacks.
- The positive presentation is tied to the actual integral-reduced line: its first
  site map is the existing root-projection-normalized `finite_tate_site_descent`
  composed with `sfOrientationFixedRootSheaf_existsUnique`. The positive-level
  transport is specified by HEq for every presentation n=predecessor+1. The first
  chart then uses exactly `finiteReductionRootTrivialization`; higher charts use
  the prescribed products and the zero chart uses the specified coefficient unit.
  The first ordinary chart is uniquely specified through the fully faithful single
  functor. All ordinary positive charts send the coherent ordered basis powers
  of that first-root generator to coefficient one. Their singles, with the native
  single/unit comparison, are the derived charts. Thus their basis normalization
  is exactly the ordered recursion fixed by the normalized signed products.
  `finiteTensorPositivePresentation` is uniquely fixed by those charts and the
  existing `finiteReductionPowerTrivialization` in every primitive-root chart.
- `finiteTensorPositiveReduction` is constructed from that presentation, the signed
  line comparison and its scalar shift. `finiteTensorPositiveReduction_chart` gives
  exactly eta=zeta^(ell^(n-m)), including the zero power and the coefficient-unit
  comparison. It introduces no ramification-index hypothesis.
- `finiteTensorTau` is the inverse native second-factor tensor-shift map on the
  actual degree-zero line. `finiteTensorTau_reduction` states its precise square.
  In the published purity presentation, the source comparison is the transport of
  `finiteReductionSourceComparison`; the target is independently constructed from
  binary reduction, the recorded pullback mate, and actual positive line reduction.
  The final `finite_tensor_presentation_reduction` equates their composites with the
  existing `smoothPurityReassociation`. `d : ℕ` and
  `[SmoothOfRelativeDimension d f]` give precisely nonnegative pure smooth dimension.
- No declaration assumes flatness of the quotient, a multiple of the ramification
  index, an arbitrary comparison isomorphism, or unrestricted internal-Hom base change.

Dependency declarations read and reused:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting` and its fields.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the recorded finite derived operations.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`:
  `AlgebraicGeometry.ProEtale.derivedTensor`, the native fixed-module tensor.
- `Sheaf.Paper.FiniteCoefficientReductionFlatModel` and
  `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`: the unchanged Tor interval and
  bounded constructible scalar-extension conclusions.
- `Sheaf.Paper.FiniteReductionComparisons`: `finiteReductionPullbackComparison`,
  `finiteReductionSourceComparison`, and the actual scalar-shift structure.
- `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted` (and its public originals):
  `finiteCoefficientTwist`, `coefficientTwistLine`, `purTwistIntegralOne`,
  `diagonalTwist`, and their actual quotient/tensor definitions.
- `Sheaf.Paper.FiniteReductionRootCharts`: `finiteReductionSetting`,
  `finiteReductionRingHom`, `finiteReduction`, and the section-normalized root charts.
- Additional recorded interfaces: `Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin`
  (`fixedScalar`, `scalarPresentation`, `proScalarExtensionRepresentative`);
  `Sheaf.Paper.SfCompactSupportRestrictionOfScalars`
  (`sfInverseRealizationRestriction`);
  `Sheaf.Paper.OrientationFiniteCoefficientTwists`
  (`sfOrientationFixedRootSheaf_existsUnique`);
  `Sheaf.Paper.FiniteTateSiteDescent` (`finite_tate_site_descent`);
  `Sheaf.Paper.SupportedCup` (`cupSingleTensorMap`);
  `Sheaf.Paper.PurityCompositionCoherence` (`compositionPullbackTensorFixed`,
  `compositionFixedPullbackComp`); and the native scalar monoidal/derived shift APIs.

Edge cases checked in the statement design: m=n; n=m=1; r=0; positive and negative r;
opposite signed powers; s=0 and negative shifts; d=0; zero input; empty scheme;
identity and composable pullbacks; and ramified coefficient extensions at levels not
multiples of the ramification index. In particular the dual clause is restricted to
invertible coefficient lines, and no local equality test on arbitrary derived arrows
is used. Primitive roots only characterize canonical maps and are not extra data in
the final theorem.

Searches actually run:

- LeanFinder: `derived coefficient reduction commutes with signed Tate twists shifts
  tensor reassociation`: eight generic shift/tensor hits, no exact node statement.
- Loogle: `"CommShift", "Monoidal"`: zero hits.
- Mathlib grep: `Tate.*reduc|twist.*coefficient|scalar.*[Tt]ensor` in CategoryTheory:
  zero hits. Source and Sheaf rg searches for the item id and finite reduction/twist/
  tensor names found partial interfaces, not the combined statement.
- LeanSearch: `canonical finite scalar reduction semilinear signed Tate line and
  K-flat tensor comparison normalization`: eight general ring/flatness hits.
- Loogle: `"scalar", "twist"`: zero hits. Mathlib grep and rg of WeilConjectures and
  Sheaf for `FiniteTensorLineMapsNormalized|finiteTensorCochainComparison|
  finiteTensorFirstLine`: zero hits.
- `tools/blueprint_refs.py search 'finite tensor reduction'`: zero blueprint nodes.
  DAG search found and prompted reading `def-pur-semilinear-tensor-presentation-data`
  (ordinary pushout tensor transport) and completed entire-system comparison nodes;
  these do not define this finite signed normalization datum.
- LeanSearch: `canonical signed Tate line reduction normalized primitive roots tensor
  shift comparison`: roots-of-unity facts, generic tensor sign instances and unrelated
  tactics, not this comparison. Loogle `"Tate", "shift"`: four unrelated hits.
  Mathlib and project searches for `finiteTensorPositivePresentation|
  finiteTensorLineComparison` found no existing declarations.

No STATEMENT-DISPUTED flag, statement correction, or unresolved mathematical fault
is claimed. The returned dependency-ownership defects are repaired below.

## Second reading by NX

The dispatcher explicitly prohibits starting other agents and assigns independent review
to the maintainer. This report does not claim an independent second worker's reading.
The author reread the node, source proof Step 2, imported signatures, and the full delivery
against each clause above. The review specifically checked the ordinary integral line,
negative dual evaluation, actual scalar-adjunction mate, root transition, shift signs,
and that the target comparison is constructed independently of the square being stated.

## New nodes

`def-pur-finite-tensor-reduction-data` defines the explicit finite signed line/reduction
coordinates and determining ordinary, derived-single, and binary representative equations.
Its source is the item's expanded proof Steps 2--6, with Stacks 07A4, 0FPT, 03EK and 03EM.
The searches above found general scalar/tensor constructions but no record of this
specialized normalized datum. All underlying coefficient objects, restrictions and
native tensor maps are reused. The generic equations avoid repeated elaboration of
large categorical instances; they do not change the maps or their normalizations.

`def-pur-finite-signed-reduction-comparisons` defines the canonical binary and signed-line
comparison families by the explicit uniqueness normalizations of the first new node.
It keeps the target coefficient action and uses no unspecified line isomorphism. Its
source is expanded proof Steps 2--6. It also owns the canonical natural twist/shift
isomorphism assembled from those maps. The combined ordinary and completed comparisons
found by the searches above do not provide these two-finite-level normalized families.

`def-pur-finite-tensor-comparison-equations` records the generic binary counit,
symmetry and simultaneous-shift equations, and the explicit twist/shift component
formula, together with single-product arrow
normalization. It also factors the native single/unit chart composite before specializing the
sheaf category. It separates categorical elaboration from the concrete coefficients;
its source and searches are those of the finite tensor normalization datum above.

`def-pur-finite-signed-twist-products` supplies the missing canonical signed addition
maps, fixed by coherent local bases and by the canonical single-complex tensor arrow.
It reuses the actual signed sheaves. Its source is expanded proof Step 5. The additional
LeanFinder query for canonical signed powers, tensor addition and primitive-root charts
returned eight unrelated scheme-section arithmetic facts; Loogle `"tensorRight", "mapIso"`
and Mathlib/project grep of the proposed product/site/chart names returned no hits.
The blueprint search `signed twist products` also returned no node.
The subsequently inspected `PurityTwistCancellation` contractions are for the root-defined
`tateFiniteLine`, including even shifts, rather than the ordinary integral-reduced line
required here; their frame and section declarations cannot be applied to this object
without precisely the canonical root bridge supplied separately. They are not duplicated
as another definition of the root line.

`def-pur-finite-root-tensor-presentation` supplies the canonical bridge between the
actual ordinary integral-reduced line and the already specified positive root-site
presentation. It uses the existing root-projection and realization comparisons,
then uniquely specifies the bridge in every primitive-root chart. Its source is
expanded proof Step 8; the same additional searches found no existing bridge.

`def-pur-finite-first-root-chart` owns the canonical first-line site comparison and
zero/first root charts, separated from the higher-power bridge so each module is
checked within the per-file limit. It has the same Step 8 source and the recorded
first-site/chart searches above. It fixes the actual site map for every positive
index presentation, rather than choosing an unspecified isomorphism.

`def-pur-finite-positive-root-charts` owns the ordinary and derived positive charts.
The first chart is fixed through the fully faithful single functor, and the ordinary
higher charts are fixed on coherent ordered root bases. These give the prescribed
power recursion because the signed products have that same basis normalization.
This is the Step 8 notion searched above; the existing root-defined twist charts
have different endpoints. Separating this from the presentation bridge keeps each
file independently compilable within the prescribed limit.

`def-pur-finite-tensor-fixed-comparisons` supplies the fixed-scalar coordinate
interfaces for the recorded intrinsic pullback and purity-source maps. Every map
is the specified realization/scalar-unit conjugate; the target is independently
binary reduction followed by pullback and the actual line reduction. This is the
Step 7--9 coordinate notion identified in the original scalar/tensor searches,
which found only the intrinsic interface. A further LeanFinder query for canonical
fixed-scalar derived reduction/pullback through an equivalence returned eight
ordinary free-module pullback facts. Loogle `"preimageIso", "mapDerivedCategory"`
and Mathlib/project/DAG grep of the proposed map names returned zero hits.
It also supplies the actual finite-ring
tensor-pullback map without an additional finiteness hypothesis.

`def-sp-finite-scalar-realization-presentations` records existing definitions in
`Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin`, with primary declaration
`AlgebraicGeometry.ProEtale.SupportedEtaleTensorOrigin.scalarPresentation`.
It adds no Lean file and no new comparison. The finite rings, map, scheme,
realization equivalences, exact restriction, left adjoint, sectionwise identity,
and the specified unit/counit mate render every clause of its statement.
The source is the blueprint finite-reduction proof Step 2 and the existing
00YV/03DA/06YY constructions. The new node records the actual search outputs:
LeanSearch returned eight ordinary scalar/unit facts; Loogle for
`"leftAdjointUniq", "mapDerivedCategory"` returned zero hits; Mathlib grep for
`scalarPresentation|restrictionPresentation|sfIntrinsicDerivedEquivalence`
returned zero hits. Source grep found the published definitions at lines 98
and 110, with no upstream WeilConjectures match. DAG grep found these names
owned only by the supported-origin theorem. Blueprint search for
`scalar presentation` returned zero nodes. Thus the repair adds the missing
definition ownership and reuses the exact published maps.
Edge cases include identity ring map, empty scheme and arbitrary finite
commutative rings; the definitions require no flatness or finite-type scheme
hypothesis and preserve the original site/coefficient universes.

## Validation

All nine modules compiled cleanly in the server confirmation, each within its
60-second limit. The prescribed deliver2.py dry run passed compilation and
server preflight on 2026-10-23 (commit 6584536867b); no mathematical or Lean
source changed after that check. Resumed checks
removed diagnostic heartbeat limits and factored the single/unit chart composite
through a generic helper. Transparency-respecting elaboration avoids repeated
expansion of derived monoidal structures; the scalar-restriction shift instance uses
the published exact functor through explicit unfolding. The cochain and zero/first
root-chart expressions are exposed abbreviations of exactly their specified composites.
The shifted root chart and positive-reduction composite use the same abbreviation
strategy, preserving the actual native shift and line comparisons.
The root-presentation normalization is the equivalent whole-isomorphism equation:
e equals its specified root chart followed by the inverse shifted positive chart.
This avoids repeated kernel expansion of hom endpoints without changing the
canonical comparison or its normalization.
Basis vectors in the positive chart normalization use `finiteTensorFrameBasis`,
which fixes the section module before applying the same basis to zero. No mathematical
condition changed.

Additional preflight search: LeanSearch query `canonical signed Tate coefficient line products finite reduction root charts derived pullback comparison` returned eight
root-system and scheme carrier/residue-field pullback facts, none defining the
signed coefficient products, normalized root charts or derived comparisons. This
search is recorded in each of the five relevant new definition nodes.


## Repair of immutable head aa2aa128e2c9

1. H2 composition owner: the item and
`def-pur-finite-tensor-fixed-comparisons` now cite
`def-pur-composition-comparisons`, the existing definition owner in
`Sheaf.Paper.PurityCompositionCoherence`, instead of
`thm-pur-composition-coherence`. The declarations used are
`WeilConjectures.PurityFiniteSetting.compositionFixedPullbackComp`,
`compositionPullbackTensorFixed`, `CompositionPullbackTensorType`,
`compositionTwistShift` and `compositionShiftedPullback`. Their full signatures
and normalization docstrings were reread. The fixed tensor and compositor data
are chosen from their locally normalized unique-existence statements; the
composition theorem's equality is not an input.

2. H2 scalar owners: the item, `def-pur-finite-tensor-reduction-data` and
`def-pur-finite-tensor-fixed-comparisons` now cite
`def-sp-coefficient-scalar-representatives` and the new existing-declaration
node `def-sp-finite-scalar-realization-presentations`. They no longer cite
`lem-sp-supported-etale-tensor-origin` in stmt_deps. The finite-ring abbreviations
`fixedScalar f T` and `fixedRestriction f T` are definitionally exactly the
recorded `proFixedScalar f.ulift T` and `proFixedRestriction f.ulift T`.
The new owner records `scalarPresentation`, `restrictionPresentation`, and the
retained lift/finite-ring abbreviations from that same published module. The
restriction square is obtained by exact derived transport of the sectionwise
identity realization/restriction square. The scalar square is its actual
left-adjoint uniqueness comparison with the prescribed realization unit and
counit. No theorem about supported etale origin is used. Existing ownership
was checked against `def-sp-et-proet-coefficient-transport`: that node owns the
different `CoefficientCompatibility.scalarPresentation` and support transport,
not these `SupportedEtaleTensorOrigin` declarations.

3. `lem-amb-finite-tate-site-descent` is retained as requested: the first root
site comparison chooses its uniquely characterized constructed comparison,
which is part of that node's statement. No replacement is needed.

The eight new modules and item module are retained from the returned head;
only JSON ownership/citations and this report change. The item statement,
proof and proof_deps are unchanged; all clauses and edge cases in the worker
report still apply. The base item has neither of the removed theorem
stmt_deps: both were added by the returned packet. The sandbox's eight other
new definition nodes are still absent from the current base, so their owner
citations can be repaired directly without changing an existing dependency node.
No independent second reading is claimed. The maintainer's advisory about the
degree-one HEq of the line maps remains advisory; its statement and construction
have not changed in this ownership repair.
