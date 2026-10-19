## Worker report

This delivery retains `Sheaf.Paper.DerivedPullbackTensorIso` and repairs the returned
H2/H3 findings. The mathematical node statement, its hypotheses, and its proof
plan are unchanged. Its statement dependencies gain the canonical comparison
definition nodes described below. The main statement is `WeilConjectures.derivedPullbackTensorIso`. Its conclusion now explicitly includes the finite associativity, unit, signed braiding, composition, and quotient reduction equations, together with integral and rational scalar-extension squares.
All theorem proofs are `sorry`; definitions have actual data or use a theorem
whose displayed characterization uniquely fixes the object being defined.

Hypotheses and clause correspondence:

- `l : ℕ` and `[Fact l.Prime]` give the prime. `E : Type u`, its field and Padic
  algebra structures, and `[FiniteDimensional (Padic l) E]` give the finite
  coefficient extension. The recorded coefficient ring and uniformizer supply
  the finite rings; `n : ℕ` denotes the positive exponent `n + 1`.
- `{X Y : Scheme.{u}}`, `f : X ⟶ Y`, and the two pointwise `Invertible` instances
  give precisely the arbitrary scheme morphism and invertibility of l. No
  properness, smoothness, Tor bound, or nonempty hypothesis is added.
- `Ω : Type v` with its field, Padic algebra, and `IsAlgClosure` instances supplies
  the algebraically closed coefficient field, with its independent universe.
- `FinitePullbackTensorComparison` takes arbitrary objects of
  `proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))`. Its values are
  isomorphisms in the ambient finite derived category. In particular bounded
  constructible inputs are included; boundedness of their tensor is not asserted.
- `IntegralPullbackTensorComparison`, `RationalPullbackTensorComparison`, and
  `CommonStagePullbackTensorComparison` use the recorded full integral
  constructible, raw rationalized, and common-stage categories and their recorded
  pullback and tensor functors. Each value is an `Iso`, so all inverse identities
  hold. The final theorem states existence of four natural isomorphisms whose
  components are exactly these canonical values.
- Four `NatIso` existence conjuncts assert naturality in arbitrary morphisms
  of the product categories and include the inverse identities. Their component
  equalities fix the isomorphisms to `canonicalFinitePullbackTensor`,
  `canonicalIntegralPullbackTensor`, `canonicalRationalPullbackTensor`, and
  `canonicalCommonStagePullbackTensor`.
- The finite canonical family is the small-site ringed-topos tensor comparison; the main conclusion also states its associativity, unit, signed braiding, composition, and quotient-change equations. The integral and rational scalar-extension equations quantify over every finite extension `L/E` and algebra map `ι`, including ramified and identity cases. The finite canonical family is the small-site ringed-topos tensor comparison,
  conjugated by the unit-normalized intrinsic realization and the recorded
  K-flat tensor-model comparisons. The representative equations fix the actual
  map and every tensor-model component, rather than an arbitrary isomorphism.
- The integral family is the actual `coefficientSequenceLimit` image of
  `pullbackTensorSystemComparison`, with the reduction/limit counits and the
  uniquely specified strict Roos realizations. Those realizations fix both cone
  coordinates. `canonicalIntegralPullbackTensor_reduction` is now an equation
  containing `reduction.map (canonicalIntegralPullbackTensor ...).hom.hom`
  itself, the actual tensor and pullback reduction comparisons, and that same
  system comparison. Evaluating this equation and using the final explicit
  `pullbackTensorSystemComparison_evaluation` equation gives the finite-reduction
  square for the actual integral comparison at every positive exponent.
- `canonicalRationalPullbackTensor_existsUnique` fixes the rational hom to the
  localization of the integral hom. The main conclusion repeats this equality
  for the chosen μR and μI.
- `pullbackTensorAtCommonStage` includes all four recorded transition comparisons.
  The common-stage canonical family is uniquely prescribed as the corresponding
  `ofHom` class at every larger common finite coefficient field.
- The finite associativity, signed braiding, both unit, and composition equations
  occur in `canonicalFinitePullbackTensor_associativity`, `_braiding`, `_unit`,
  and `_composition`. The braiding is normalized on total generators by
  `(-1)^(pq)`.
- The three higher associativity and braiding predicates in the main conclusion
  use fixed canonical isomorphisms. The integral associator and braiding are
  uniquely characterized after coherent reduction; the rational maps are their
  actual localizations; the common-stage maps are their prescribed rational
  representatives at every larger field. There are no freely chosen α or β
  witnesses in those compatibility predicates.
- All three higher unit predicates are final conjuncts. Each states the two
  actual μ unit equations with the canonical left and right unitors. The integral
  unit is the actual derived limit of the coherent ring unit; integral unitors
  are uniquely fixed after reduction. Rational units and unitors localize these
  maps. Common-stage unitors are the specified rational representatives, with
  the coefficient-ring scalar comparison and tensor-stage comparisons inserted.
- All three higher pullback-composition predicates are final conjuncts. Each
  equation inserts the composition comparison on the tensor input and its two
  tensor factors. Integral composition is the recorded finite-reduction-normalized
  `integralPullbackComposition`; rational composition localizes it; common-stage
  composition is fixed at every finite stage with its pullback transition maps.
  Raw `HEq` between arrows with different composition endpoints has been removed.
- `canonicalFinitePullbackTensor_quotient` is the actual square for every `n ≤ m`,
  including equality, using the normalized quotient tensor and quotient/pullback
  comparisons. `canonicalIntegralPullbackTensor_scalar` and
  `canonicalRationalPullbackTensor_scalar` are the actual scalar-extension squares.
  Together with the all-stage `ofHom` normalization they include scalar extension
  into Ω and ramified finite extensions.

Dependency declarations used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, through `finiteCoefficientRing`.
- The scheme-properties aggregate has no private replacement: `Scheme`, scheme
  morphisms, `Scheme.residueField`, and `Invertible` are the existing notions.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`:
  `AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible`; the finite
  theorem is stated on its ambient derived category, as the node requires.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and
  `sfIntegralConstructibleCategory`.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory` and
  `sfRationalConstructibleLocalization`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`:
  `generalAlgebraicallyClosedConstructibleCategory`, `stageSystem`, and `ofHom`.
- `Sheaf.Paper.DerivedPullbackTensorHom`: the eight recorded pullback/tensor
  functors, the finite tensor models, and the integral/rational/common-stage
  scalar-transition comparisons.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`: the normalized ordinary and
  completed scalar comparisons underlying the preceding restricted comparisons.
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`:
  `proEtaleCanonicalTensorComparison`;
  `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `proEtaleConstantRingComparison_isIso`;
  `Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange`:
  `sfIntrinsicDerivedPullbackComp`; `Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport`:
  `sfIntrinsicConstantModuleAdjunction`; `Sheaf.Paper.IntegralPullbackComposition`:
  `integralPullbackComposition`.

The actual Stacks 07A4 text was reread: it applies to arbitrary derived inputs
and derives the comparison by totalizing the ordinary module comparison on
flat-term K-flat representatives. It imposes no geometric or Tor-dimension
restriction. The integral, rational, and algebraically closed constructions follow
exactly the recorded operation conventions.

Edge cases checked: exponent one (`n = 0`), empty schemes, zero objects and arrows,
identity and composable scheme maps, equal finite quotient levels, identity
coefficient extension, ramified coefficient extensions, and enlargement of an
already common finite stage. The equations retain all these cases.

Searches retained from the saved packet: LeanFinder, “derived pullback commutes
with derived tensor product” (ordinary pullback/localization hits); Loogle,
“pullback, tensor, derived” (scheme helpers only); msearch grep,
“pullback.*tensor|tensor.*pullback” in Mathlib (no four-level theorem); rg in the
upstream WeilConjectures and side Sheaf trees (recorded operations and generic
ringed-topos comparisons, no theorem with the complete statement). Repair searches
for pullback composition found `IntegralPullbackComposition` and the existing
localized construction in `LocalFrobeniusTrace`; the former is reused directly.
Searches for the new helper names in the side and upstream sources found no
existing declarations. The canonical comparisons are now factored into the two definition nodes below.
There is no dependency-node replacement.

## Repair of returned H2/H3 findings

H2: `pullbackTensorSiteSmall` and `pullbackTensorSequenceSmall` are included in
the `lean.declarations` of their respective finite and completed definition
nodes. Both modules are publicly imported by the main module. The declaration
lists cover every named instance, definition, abbreviation, and theorem.

H3: the main conclusion includes integral, rational, and common-stage composition
with their actual endpoint transports; higher associativity, signed braiding, and
both unit equations on those same canonical comparisons; and the actual integral
reduction square followed by its finite evaluation equation. The earlier saved
repair used unconstrained existential associators/braidings and raw heterogeneous
composition equations. Those have been replaced, not merely documented.

The initial retained-packet dry run failed by the 60-second compile limit.
Profiling located missing public imports that triggered expensive elaboration
recovery, plus unnecessary transparent instance search through residue fields.
The modules now explicitly import the canonical small-site and intrinsic
realization interfaces and supplies the existing scheme-invertibility instances
explicitly in the comparison formulas. The per-file limit is unchanged. Proof imports are synchronized to the currently
recorded modules, including the newly landed K-flat total tensor model.

## New nodes

`def-pur-finite-pullback-tensor-comparison` owns
`Sheaf.Paper.FinitePullbackTensorComparison`: the comparison-family types, the
finite canonical comparison normalized by flat-term K-flat representatives, and
the signed symmetry and finite coherence equations. It retains the same
23 declarations from the previous combined module; none was replaced by an
arbitrary isomorphism. Its source is Stacks 07A4 and 06YS, with the recorded
intrinsic realization and operation conventions.

`def-pur-completed-pullback-tensor-comparison` owns
`Sheaf.Paper.CompletedPullbackTensorComparison`: the strict coherent-system
comparison, fixed Roos realizations, actual derived-limit integral comparison,
its rational localization and its common-stage class, with finite evaluation,
quotient and scalar normalization. It retains the same 93 declarations from the
previous combined module. It depends on the finite definition node and the
original operation declarations. Its source is Stacks 07A4 and 0941 together
with the node's recorded integral-operation conventions.

For the finite definition node, the prime, finite coefficient extension, scheme
map, positive exponent and invertibility conditions are the binders of
`canonicalFinitePullbackTensor`. Its body is the composite of
`pullbackTensorFiniteRealization`, `pullbackTensorFiniteModelIso`, and
`proEtaleCanonicalTensorComparison`; `pullbackTensorFiniteRealization_existsUnique`
fixes the ordinary-unit normalization. `pullbackTensorBraiding_existsUnique`
fixes the signed total representative. The four initial comparison-family
abbreviations render its type clauses, and the finite coherence theorems render
its final normalization clauses.

For the completed definition node, `pullbackTensorSystemComparison_existsUnique`
fixes the coherent representative map, while the reference tensor and pullback
model existence/uniqueness theorems fix their two Roos coordinates.
`pullbackTensorReferenceComparison` applies the actual limit functor and counits;
`canonicalIntegralPullbackTensor` conjugates only by those fixed models.
`canonicalRationalPullbackTensor_existsUnique` specifies the localized hom, and
`canonicalCommonStagePullbackTensor_existsUnique` specifies the representative
at every larger stage. The three quotient/scalar square theorems and
`pullbackTensorSystemComparison_evaluation` express the remaining clauses. Their
object categories and all hypotheses are the original recorded ones, including
arbitrary finite ambient derived objects, ramified extension and independent
algebraic-closure universe.

These definitions were missing as standalone reusable notions. They were already
constructed in the saved combined module. Repeated combined-file timeouts led to
factoring those constructions, preserving every declaration name and formula,
so every delivered module can be compiled separately within the unchanged limit.
The main theorem and its higher coherence maps remain in the original module
(62 declarations). The 178 named declarations are accounted for across all three
node records.

New-node searches: LeanSearch queried the canonical natural isomorphism between
derived pullback of tensor and tensor of pullbacks; LeanFinder queried canonical
finite and completed comparisons normalized on K-flat representatives and
coherent reductions; Loogle queried the expected comparison names; Mathlib grep
queried `pullback.*tensor|tensor.*pullback` under `CategoryTheory`. The exact
responses are retained in each node's `mathlib_searches`. Grep of the upstream
and side sources found none of the three canonical-family/helper names. DAG and
blueprint searches found uses of the comparison, with no separate definition of
these normalized comparison families. Existing generic constructions are reused.

## Second reading by Q45

I compared the node's hypotheses and all its clauses with the equations described
above. The repaired higher compatibility predicates use fixed normalized finite, integral, rational, and common-stage
associators, braidings, and unitors. Composition includes both transports. The
integral reduction predicate contains the actual completed μ, rather than only
the coherent-system μ. The finite evaluation equation then identifies its finite
component with the canonical finite comparison. The main theorem retains all four
bifunctorial natural isomorphisms and their component equalities to the canonical
families. Using `NatIso` packages naturality and the inverse laws without
re-elaborating those laws separately. No mathematical
statement correction, new hypothesis, or excluded edge case was introduced.

## Validation

All three delivered files passed `scompile.py Q45
lem-pur-derived-pullback-tensor-iso <finite> <completed> <main>` separately, in
dependency order, with exit 0 and no warnings. The final library-path checks
took 13.7 s, 39.7 s and 40.0 s respectively, within the unchanged 60-second
per-file limit. Declaration ownership, verbatim signatures, node dependency
citations and 100-character line widths were also checked.

The required `deliver2.py Q45 lem-pur-derived-pullback-tensor-iso --no-push`
dry run passed: `OK (dry run): commit 9a34da2d38 passes the preflight and
compiles; nothing pushed`. No Lean source or node record changed after that
successful dry run.

## Repair addendum (2026-10-18)

The returned H3 issue is repaired in the statement signature itself. The finite
conjunct now states the normalized associativity, unit, signed braiding, and
pullback composition equations, and the quotient conjunct quantifies over every
`q ≤ m`, including `q = m`. The integral and rational conjuncts quantify over
all finite coefficient extensions `L` and algebra maps `ι : E →ₐ[Padic l] L`.
The existing nonfinite composition, associativity, signed braiding, unit, actual
`reduction.map` square, and finite evaluation equations remain in the same
conjunction. The finite and completed comparison modules expose proposition-form
condition definitions so these equations are rendered as types rather than proof
terms; their node declaration lists were updated accordingly.

The proposition wrappers contain the equations verbatim from the corresponding
canonical theorem declarations. They add no hypotheses: the only new binders are
finite quotient levels, extension data already required by the scalar square, and
objects quantified by the source statement. Edge cases checked again are `q = m`,
`m = 0`, identity scalar maps, ramified finite extensions, identity pullback, zero
objects, and empty schemes.
