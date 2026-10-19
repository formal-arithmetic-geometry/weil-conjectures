## Worker report

The module `Sheaf.SixFunctors.GraphFrobeniusPointExchange` states
`WeilConjectures.TraceFormulaCoefficientConventions.graphFrobenius_point_exchange` with
`sorry`. All helper definitions have actual data. No theorem is proved, no definition
is hollow, and the original node statement and proof are unchanged. Two already landed
statement dependencies are added: `def-trf-finite-ordinary-pullback` and
`lem-trf-frobenius-open-square`. They supply the existing canonical ordinary pullback
and power semilinearity, respectively; neither is restated.

The source read is main-20261015, sec-trace-formula/sk-d-weil,
`prop-trf-graph-frobenius-operator.proof.md`, Step 2, together with all six proof steps
of this node. The module docstring explains the coordinate convention, and the theorem
docstring records all six proof steps and the nodes they use.

Clause-by-clause correspondence:

- The finite-field tuple p,a,q,k₀,k is `T.datum : FiniteFieldDatum`. Its structure stores
  primality, positivity of a, q=p^a, cardinality of k₀, and its specified algebraic closure.
- The prime l unequal to p and chosen algebraic closure of Q_l are
  `T.coefficients`; its fields include `different` and the prime instance. The actual
  finite extension is `T.extension`. `T.coefficientField` is the recorded small model
  retaining the extension via the specified algebra equivalence. The quotient
  `A=O_E/varpi_E^n` is `T.coefficientRing`, with `T.level_pos : 1 ≤ T.level`.
  `graphPointCoefficientFinite` uses the recorded finiteness theorem for exactly
  that quotient, not an additional assumption.
- `graphPointSmallFibre` and `graphPointFibre` are the same recorded point-sections
  functor derived into coefficient localizations of hom universes u+1 and u+2.
  The former explicitly uses `HasDerivedCategory.ofIsGrothendieckAbelian`, exactly
  the instance stored in the recorded point transport. `graphPointLocalizationLift`
  derives the identity of the unchanged module category between these localizations.
  `graphPointFibreComparison` is the canonical exact-derived-composition comparison
  followed by the right identity comparison. Conjugating the recorded point arrow
  preserves its restriction/insertion/tensor-unit formula and changes no coefficient.
- The proper finite-type model Y₀ is `T.X₀`, with the finite-type and quasi-compact
  fields of T and `[IsProper T.X₀.hom]`. T's separated field is already implied by
  properness, so using the coefficient conventions does not strengthen the hypotheses.
- Y is `T.geometricBaseChange`, exactly `(T.datum.geometricFiber T.X₀).left`.
  The structural map a_Y is `T.structureMap`; s is `Spec (.of T.datum.k)`.
- The geometric field automorphism gamma is the dependency's inverse arithmetic
  Frobenius. Its Spec is `(frobeniusPointIso T.datum).hom`, and its action on Y is
  `T.datum.geometricGaloisFrobenius T.X₀`. Both are the recorded constructions.
- Positive m is `(m : ℕ) (_hm : 1 ≤ m)`. The endomorphism monoid `HPow.hPow`
  makes every occurrence a genuine m-th iterate. The leading underscore only suppresses
  the expected unused-binder warning for a hypothesis on an unproved theorem.
- The relation a_Y g^m = h^m a_Y is supplied directly to `graphPointExchange`. It extracts the
  power semilinearity clause of the existing `frobenius_open_square`, specialized to
  the identity open immersion of T.X₀. This introduces no open hypothesis on a_Y.
- `graphPointExchange T m` is `FrobeniusExchange.finiteExchange` on this exact square.
  This is the intrinsic-coordinate ambient mate used in the recorded finite Frobenius
  exchange. Its transpose is the canonical pullback comparison followed by pullback
  of the counit. The tensor-coordinate version in the dependency is its conjugate by
  `openSquareDerivedPullbackModel`, not a different or freely selected exchange.
- `graphPointTransportPositive` reindexes the recorded `frobeniusPointTransportFinite`
  from successor levels to arbitrary positive levels by matching the level before
  forming its coefficient categories. Its zero branch eliminates the impossible
  hypothesis 1 ≤ 0 using Mathlib; the successor branch is exactly the recorded arrow.
  `graphPointTransportOne` applies this at T's level and conjugates only by the
  canonical comparison between localization sizes. Level 1 is the API's index 0.
- `graphPointTransportPower` composes these recorded restriction/insertion/tensor-unit
  arrows with the canonical `sfIntrinsicDerivedPullbackComp` comparisons. On the
  canonical sectionwise inverse-image model, restrictions compose to restriction along
  h^m; the distinguished comma coprojections compose to the distinguished coprojection,
  and x tensor 1 tensor 1 maps to x tensor 1. Thus it is the specified iota^(m), not
  a transported arbitrary isomorphism. Its m=0 branch is the canonical identity
  pullback normalization, used only to define the recursion. Its power-order cast
  uses `pow_succ'`; `End.mul_def` reverses categorical composition, exactly as required.
- `graphPointSections` aliases the recorded `finiteOrdinarySectionsFunctor` with
  its specified structural map; its body is `proEtaleConstantDerivedDirectImage a_Y A`
  followed by `(pointFiniteSections k A).mapDerivedCategory`. This is the ambient
  finite-coefficient Fib_s Ra_Y* functor and the recorded finiteOrdinarySections object.
  Its target is `DerivedCategory.{u+2} (ModuleCat.{u+1} (ULift.{u+1,u} A))`, the
  existing size-lifted coefficient-module presentation of D(A). No coefficient
  automorphism is introduced.
- `graphPointExchangeComposite` is iota_(Ra_*M) followed by Fib_s(e_(m,M)); the
  categorical notation `≫` reads in this order, matching the displayed TeX composite.
- `graphPointOrdinaryPullback` uses the existing `finiteOrdinaryPullback`: derived
  adjunction unit followed by the canonical direct-image/global-sections Leray
  identification. Its final factor is the canonical unit-preserving comparison from
  tensor pullback to the intrinsic pullback used by e_m and iota. Hence the two sides
  have the same pullback object. The coefficient map is precisely the constant-section
  identification fixed by the dependencies, including its action on the scalar 1.
- The first conjunct of `graphFrobenius_point_exchange` asserts the required equality
  for every `M : T.boundedConstructibleFiniteTor.FullSubcategory`. The second
  asserts the commutative naturality square for every pair M,N and every morphism
  `f : M ⟶ N`, using the full-subcategory underlying morphism `f.hom`.
- Semilinearity is retained throughout: no binder asserts that g^m is a morphism over
  k; `finiteOrdinaryPullback` explicitly accepts any scheme endomorphism.

Recorded dependency declarations used (their source modules and full relevant signatures
and docstrings were read):

- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`,
  `FiniteFieldDatum.geometricFiber`, `FiniteFieldDatum.CoefficientDatum`.
- `Sheaf.Paper.TraceFormulaCoefficientConventions`:
  `WeilConjectures.TraceFormulaCoefficientConventions`, `coefficientRing`,
  `geometricBaseChange`, `structureMap`, `boundedConstructibleFiniteTor`.
- `Sheaf.SixFunctors.SchemeFrobenius`:
  `WeilConjectures.FiniteFieldDatum.geometricGaloisFrobenius`.
- `Sheaf.SixFunctors.FrobeniusSquareCartesian`:
  `WeilConjectures.FiniteFieldDatum.frobenius_square_cartesian` (underlying square).
- `Sheaf.Paper.DerivedPullbackTensorHom`: `WeilConjectures.finiteDerivedPullback`,
  the finite intrinsic pullback used by the recorded point transport.
- `Sheaf.Paper.SfCommonStageDirectImage` reexports `Sheaf.Paper.SfDerivedDirectImage`
  and `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`, giving
  `AlgebraicGeometry.Scheme.proEtaleConstantDerivedDirectImage`, the actual finite
  K-injective right derived direct image.
- `Sheaf.Paper.FrobeniusGeometricExchange` reexports `FrobeniusSquareExchange` and
  `SystemOperationExchangeRealization`: `WeilConjectures.FrobeniusExchange.finiteExchange`,
  `finiteTensorExchange`, `finiteDirect`, `frobeniusDirectFinite`. The first is the
  intrinsic-coordinate mate underlying the others, and supports arbitrary powers.
- `Sheaf.SixFunctors.FrobeniusPointTransport`:
  `WeilConjectures.frobeniusPointIso`, `frobeniusPointTransportFinite`, with its
  sigma, complex representative and x tensor 1 comparison.
- `Sheaf.Paper.FiniteCoefficientPoint`:
  `WeilConjectures.pointFibreFinite_exact`, point-section exactness and size convention.
- `Sheaf.Paper.CommonStageCompactWeilCohomology` reexports `OrdinaryCompactCohomology`:
  `WeilConjectures.finiteOrdinarySections`, the same ambient Fib_s Ra_* object.
- Added landed dependency `Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback`:
  `WeilConjectures.finiteOrdinaryPullback`, `finiteOrdinaryLeray`,
  `finiteOrdinarySectionsFunctor`, `finiteOrdinarySectionsComparison`.
- Added landed dependency `Sheaf.AlgebraicGeometry.FrobeniusOpenSquare`:
  `WeilConjectures.FiniteFieldDatum.frobenius_open_square`, power semilinearity clause.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange` (reexported by the
  exchange): `AlgebraicGeometry.Scheme.openSquareDerivedPullbackModel`, the unique
  unit-preserving coordinate identification. `ProEtaleOpenSquareExchange` gives
  `sfIntrinsicDerivedPullbackComp` and `sfIntrinsicDerivedPullbackId`.

All recorded proof-dependency modules are imported, with proof-only imports nonpublic.
In particular the general derived-adjunction fraction theorem, exact point evaluation,
sectionwise inverse image, canonical composition, module inverse/direct image,
right-adjoint preservation of K-injectives, and Mathlib's
`CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous` are retained.

Edge cases checked:

- The empty proper scheme and zero M remain admitted; the relevant sections are zero
  and both maps coincide. No inhabitedness or nonzero-rank hypothesis appears.
- Level n=1 is included: the positive-level helper matches it as 0+1 and calls
  the recorded transport at index 0.
- m=1 is included. The identity normalization in the recursive zero branch cancels
  the canonical pullback composition, giving the recorded one-step transport.
- The statement only quantifies m≥1, as the node says, although the helpers cover m=0.
- Y₀=Spec k₀ yields the point transport itself. For Y₀=Spec F_(q²), odd powers permute
  the two geometric components on both sides; this tests that the semilinear base map
  is retained and no illicit k-linearity or coefficient automorphism was introduced.
- All site and coefficient universes retain the existing pro-etale convention (site
  objects u+1, arrows u; coefficient modules u+1 and derived localization u+2).
  The finite extension is the recorded small model, not an independent small universe.

Searches made before writing:

- `msearch.py ... leanfinder`: “The direct image Frobenius base change exchange followed
  by point transport equals ordinary cohomology pullback”. Eight hits, including
  `SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom` and
  `AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`; none states this
  finite pro-etale Frobenius/point-transport identity.
- `msearch.py ... leansearch`: “Frobenius base change exchange point transport cohomology
  pullback”. Eight generic base-change hits, beginning with `IsBaseChange.basis_repr_comp`;
  no matching statement.
- `msearch.py ... loogle`: “CategoryTheory.Adjunction.unit, CategoryTheory.NatTrans”.
  One unrelated `TopCat.adj₂_unit` hit.
- `msearch.py ... grep`: `[Ff]robenius.*[Ee]xchange|[Pp]oint[Tt]ransport` in
  Mathlib/AlgebraicGeometry. Zero hits.
- `rg` in the named upstream WeilConjectures and shared lean/Sheaf trees for Frobenius
  point exchange, graph Frobenius, ordinary pullback and cohomologyPullback found the
  trace-formula graph definitions, graph-unit comparison and its already landed
  `FiniteOrdinaryPullback` dependency; none states the item's equality.
- The upstream trace-formula Frobenius module was additionally inspected: its graph,
  relative-Frobenius and compact-exchange declarations do not state this point identity.
  The item id and proposed declaration names were searched in the upstream tree and
  `dag/lean_names_upstream.json`; no binding or name collision was found. Existing
  sibling `GraphFrobeniusUnitComparison` was read and its canonical ordinary-pullback
  dependency was reused rather than copied.

No STATEMENT-DISPUTED or mathematical statement fault was found.

## Author check

Author's second pass, with the node and module open; the independent maintainer review
remains independent of this self-check. The clause mapping above checks every hypothesis
and conclusion. In this pass I replaced an initial local power-square induction with the
already landed `frobenius_open_square` semilinearity clause, and corrected the explicit
universe application on `finiteOrdinaryPullback`. I checked that the first side really
uses the recorded finite mate and point transport, while the second really uses the
unit/Leray construction; the definitions do not identify these two arrows by fiat.
I checked the orientation of End multiplication, pullback composition and the terminal
coordinate comparison, and that the naturality equation is on the full finite-Tor
constructible subcategory. No source statement, theorem hypothesis or conclusion changed.

## Compilation notes

The first overlay checks encountered a missing published transitive artifact for
`Sheaf.Paper.IntegralScalarExtensionConstructible` and then
`Sheaf.Paper.CompletedAdicCoefficientDatum`, before reaching this file. Both sources
are present. Explicit proof-only imports before the exchange modules ask the prescribed
wrapper to compile these existing transitive dependencies in the private overlay. This adds
no declaration, mathematical hypothesis, or alternate coefficient construction.

## Saved-packet self-check (2026-10-18)

The resumed worker retained the saved module and compared its node delta with the
current shared node: only `lean` and the addition of the two already-landed statement
dependencies differ. There is no released repair note for this item. The current
coefficient conventions, ordinary-pullback unit/Leray definition, finite exchange mate,
finite point transport, and power semilinearity declarations were reread against the
saved construction. The theorem keeps properness, positive level and positive iterate,
quantifies over the recorded finite-Tor constructible category, and states both the map
equality and its naturality. The canonical change of localization size changes neither
coefficients nor site universes. The source Step 2 and the node's six proof steps were
checked against the module docstring. No mathematical statement change was needed.

The required initial dry run returned two concrete diagnostics: no inferred
`HasDerivedCategory.{u+1}` instance for the coefficient module category, and the
unscoped `maxHeartbeats` style warning. The current server sources of the point
transport and the Grothendieck-derived-category construction were read through
`scompile.py --source`. A sandbox diagnostic traced instance search: an imported
larger-localization instance is selected before the localization-universe constraint
is checked. The final repair explicitly supplies the existing
`HasDerivedCategory.ofIsGrothendieckAbelian` in the two small-localization signatures,
their exact-derived functors, and the composition comparison. A positive-level helper
matches the level before forming its categories, avoiding dependent rewriting of
elaborator-generated proof constants. Its successor branch is the recorded transport,
and its impossible zero branch uses Mathlib's `Nat.not_succ_le_zero`. No new instance,
category construction, mathematical hypothesis or theorem clause is introduced. The unscoped heartbeat
option was removed. Temporary diagnostic probes are confined to `scratch/` and are
not part of the delivery.

Validation after the repairs: `scompile.py NQ lem-trf-graph-frobenius-point-exchange`
compiled the sandbox and final library module names cleanly (24.0 s and 25.1 s),
with no warnings. The theorem signature was compared verbatim with `lean.statement`;
all delivered lines are at most 100 characters and the sole `sorry` is the item's
named theorem. The positive-level helper is included in `lean.declarations`.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
