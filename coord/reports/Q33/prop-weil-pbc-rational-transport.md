## Worker report

The module `Sheaf.Paper.PbcRationalTransport` defines the generic tensor extension
`CategoryTheory.ScalarLocalization.transport` and states
`CategoryTheory.ScalarLocalization.transport_exact` for arbitrary R-linear
pretriangulated triangulated categories. The theorem states additive and localized
linear transport, a localized shift comparison making the extension triangulated,
uniqueness from integral objects and scalar-one arrows, and unique extension of
every natural transformation with components `1 ⊗ η.app K`. It then states the
finite-field scheme specialization `WeilConjectures.pbcRationalTransport` and the
specified four-operation exchange `WeilConjectures.pbcRationalExchange`. The tensor
formulas, object maps, coefficient equivalence, and shift witnesses are explicit;
all theorem proofs are named `sorry`s with source and blueprint docstrings. The
reported dependency declarations and edge cases are listed below.

## Return repair: generic transport and specialization

The returned H3 point is repaired by adding the generic theorem
`CategoryTheory.ScalarLocalization.transport_exact` to the module and making it the
primary declaration recorded in the node. It quantifies over arbitrary pretriangulated,
triangulated R-linear categories C and D, arbitrary R-linear additive exact F, and
their raw scalar localizations. Its conclusions render: additive and localized-linear
tensor extension; existence of a localized `CommShift ℤ` under which the extension is
triangulated; uniqueness among additive localized-linear functors agreeing on integral
objects and scalar-one arrows; and unique extension of every natural transformation
with components `1 ⊗ η.app K`. The generic statement uses no scheme, no prime, no
finite extension, and no proper-base-change hypothesis.

The module also retains `WeilConjectures.pbcRationalTransport` as the finite-field
scheme specialization and `WeilConjectures.pbcRationalExchange` for the four supplied
proper-base-change operations. The specialization records the canonical lifted
coefficient ring, uniformizer, E-linear action, completed constructible categories,
localized shift comparison, and the specified exchange components. Thus the delivery
contains both the node's arbitrary-category transport assertion and its paper-specific
specialization.


The item is stated in `Sheaf.Paper.PbcRationalTransport`, by
`WeilConjectures.pbcRationalTransport` and its four-operation application
`WeilConjectures.pbcRationalExchange`. Every theorem has proof `sorry`.
The extension functor and natural transformation have actual tensor data.
The current published `PbcIntegralCategory` and `PbcRationalDerivedCategory`
are imported unchanged. The obsolete category definitions from the earlier
sandbox attempt have been removed from the delivery.

Hypothesis and clause correspondence:

- The prime is `(l : ℕ) [Fact l.Prime]`. The finite extension is `(E : Type u)`
  with `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`.
  `PbcIntegralRing l E` and `pbcUniformizer l E` are the recorded universe lifts
  of the valuation ring and uniformizer. Their use is forced by the published
  category's coefficient universe; no site universe is identified with another.
- Each of `X, Y, X', Y'` has type `Scheme.{u}`, is Noetherian, has the explicit
  natural upper bound `∃ d : ℕ, topologicalKrullDim T ≤ d`, and satisfies
  `∀ t : T, IsUnit (l : T.presheaf.stalk t)`. These are exactly the hypotheses
  of the imported integral and raw rational categories.
- Integral objects are the actual `PbcIntegralCategory l E T ...`, the full
  subcategory over the completed coefficient sheaf with intrinsic completeness,
  uniformly bounded constructible reduction models, and compatible étale origins.
  All ambient derived morphisms are retained. The rational category is the
  imported `PbcRationalDerivedCategory`, literally raw scalar localization.
- `pbcRationalCoefficientEquiv` is the localization map induced by
  `ULift.ringEquiv`, composed with the recorded fraction-normalized equivalence
  from uniformizer localization to `E`. `pbcRationalLinear` uses this map for the
  E-action on the actual tensor Hom groups. Tensor factors are scalar-first,
  identified with the source's Hom-first convention by `TensorProduct.comm`.
- The supplied integral functor `F` has `[F.Additive]`,
  `[F.Linear (PbcIntegralRing l E)]`, `[F.CommShift ℤ]`, and
  `[F.IsTriangulated]`. These are exactly the Mathlib realizations recorded by
  `def-weil-linear-functor` and `def-weil-triangulated-category`.
- `pbcRationalExtension` is constructed by `ScalarLocalization.transport`.
  Its object map is `K ↦ ⟨F.obj K.obj⟩`; its Hom map is
  `(F.mapLinearMap R).baseChange (Localization.Away p)`. The main theorem states
  additivity, E-linearity, and the formula `a ⊗ f ↦ a ⊗ F.map f` for every
  integral morphism and localized scalar: the input is written as
  `a • (pbcRationalization ...).map f`, definitionally the scalar-one tensor
  multiplied by a, hence exactly the tensor `a ⊗ f`. Taking scalar one gives
  agreement on integral maps. This construction uses the existing scalar-localization
  composition; it does not introduce another rational category.
- The uniqueness clause quantifies over every additive E-linear functor `H`
  agreeing on integral objects and scalar-one arrows, and concludes equality
  with the constructed extension. `HEq` compares arrows whose endpoints are
  given equal, without introducing arbitrary endpoint isomorphisms.
- `HasExactPbcRationalTransport` says there is a coherent shift comparison for
  which the extension is triangulated, with shift-one component exactly
  `1 ⊗ (F.commShiftIso 1).hom.app K`. This is the localized comparison in the
  node. Its HEq accounts for the wrapped objects of scalar localization.
- For every second exact integral linear functor `G` and every supplied
  `η : F ⟶ G`, the last clause states `∃! e` between the two constructed
  rational extensions with all components `1 ⊗ η.app K`. These tensor formulas
  use `HEq` with endpoints fixed by the explicit object map. The generic helper
  `transportNat` has exactly those components and uses the named naturality
  theorem for its proof field.
- `pbcRationalExchange` takes the four actual integral functors `Rf`, `Rf'`,
  `Lg`, and `Lg'`, with the same exactness and linearity assumptions, and the
  specified `Ex : Rf ⋙ Lg ⟶ Lg' ⋙ Rf'`. Its first four conjuncts assert their
  localized exactness. E-linearity for each is supplied by the main theorem.
  Its last clause asserts a unique transformation between the corresponding
  composites with components `1 ⊗ Ex.app K`. Thus it transports the specified
  exchange. No scheme map or preservation theorem is assumed implicitly.

The integral zero object, shifts, and distinguished triangles are inherited
from the actual ambient derived category via the supplied prerequisite
`pbcIntegralUniformComplete_isTriangulated`. The rational structures are witnesses of
the recorded scalar-localization triangulation theorem: its shift-one functor
is the actual tensor-induced endofunctor, its Q comparison is normalized to the
identity, and its distinguished triangles are exactly isomorphic Q-images.
These structural witnesses are fixed once per category, independently of `F`.
Their characterization determines the localization structure up to its standard
exact identification; the functor and exchange morphisms themselves are explicit
tensor maps, not choices from mere existence.

Dependencies read and reused:

- `Sheaf.Paper.PbcRationalCategory`:
  `AlgebraicGeometry.Scheme.pbcIntegralLinear`, `PbcRationalCategory`,
  `pbcRationalization`, and `PbcRationalDerivedCategory`; and its imported
  `Sheaf.Paper.BoundedConstructibleComplete` declarations `PbcIntegralRing`,
  `pbcUniformizer`, `pbcIntegralDatum`, and `PbcIntegralCategory`.
- `Sheaf.CategoryTheory.ScalarLocalization`: `ScalarLocalization`, its actual
  composition, category/linear instances and tensor-induced shift `map`.
- `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`:
  `CategoryTheory.ScalarLocalization.exists_triangulated_scalarLocalization`,
  including its full shift normalization and distinguished-image characterization.
- Mathlib `CategoryTheory.Linear.LinearFunctor`: `Functor.Linear`, paired with
  `Functor.Additive`; `CategoryTheory.Triangulated.Functor`: `CommShift` and
  `Functor.IsTriangulated`; `LinearAlgebra.TensorProduct.Tower`:
  `LinearMap.baseChange`; `RingTheory.Localization.Defs`:
  `IsLocalization.ringEquivOfRingEquiv`.
- `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`:
  `Padic.coefficientExtension_localization_uniformizer`, whose fraction formula
  specifies the coefficient equivalence used here.
- The prerequisite's imports retain the recorded proof plan: completed adic
  coefficient/tower/intrinsic-completion modules, exact countable products,
  constant-section and completion comparisons, finite-level site comparison,
  pullback coherence, derived stalk conservativity, finite constructible
  triangulation, bounded-below comparison, and canonical tensor pullback.

Edge cases checked: the empty scheme satisfies the stalk condition vacuously
and has an allowed natural dimension bound; its zero models use the empty
stratification. Zero objects, zero maps and transformations, identity functors,
identity/composite exchanges, scalar zero, and negative/zero/positive shifts
are retained. Uniqueness is E-linear uniqueness, so it does not incorrectly
claim uniqueness among nonlinear functors. No finite Tor amplitude, local
projectivity, nonempty scheme, or arbitrary preservation condition was added.
The generic tensor helpers allow distinct source/target object and Hom
universes. The specialized scheme/category universe follows the published
size convention, retaining the small site's different object and Hom universes.

Searches made and inspected:

- `msearch.py leanfinder`: “An exact linear functor extends uniquely to the
  category with scalar localized Hom tensor modules, together with natural
  transformations” returned generic categorical-localization linearity results
  such as `Localization.functor_linear_iff`, `functor_linear`, and `linear`;
  none states this raw tensor construction and its prescribed exchange.
- `msearch.py loogle`: `CategoryTheory.ScalarLocalization.map,
  CategoryTheory.Localization.functor_linear_iff` returned zero hits (the
  project-specific scalar-localization name is unknown to that index).
- `msearch.py grep`: `scalar.*localization|localization.*triangulated|liftNatTrans`
  in CategoryTheory found generic localization/triangulation and natural
  transformation infrastructure, without the full item.
- `msearch.py leansearch`: scalar extension of an exact linear functor with
  unchanged objects and tensor Hom maps was unavailable (Internal Server Error).
  This is recorded as unavailable, with no mathematical verdict attached.
- `rg` over Mathlib and the upstream project, `grep -rn` for the item's blueprint
  id, and `rg` over `lean/Sheaf` found no existing transport theorem. The existing
  scalar-localization `map` is an endofunctor construction, so it cannot supply
  the cross-category functor or four-operation exchange of this item.
- For the unstated triangulation prerequisite, `msearch.py leanfinder` returned
  generic derived/acyclic triangulation lemmas; `loogle
  CategoryTheory.ObjectProperty.IsTriangulated` returned the exact full-subcategory
  framework; `grep uniform.*constructible|constructible.*complete` in CategoryTheory
  returned zero hits. The DAG already has the precise completed uniform-tower
  node, so no new node or different constructibility definition was introduced.
- Current server sources were read through `scompile.py --source` for the raw
  rational category and the two comparison modules. The integral-triangulation
  source at `PbcUniformCompleteTriangulated` was unavailable. The current
  `UniformCompleteTriangulated` source has now been read, and its unlifted
  interface is distinguished from this item's lifted one below. No coefficient
  or completion construction is repeated here.

The blueprint item and the source corollary were read from the server literature
copy because the read-only local clone omits fetched literature. The item states
exact functor/natural-transformation localization. Stacks Derived Categories
`proposition-construct-localization` (Tag 05R6) explicitly gives uniqueness of
the localized shift and image-triangle structure and exactness of Q.

No statement is disputed, and no statement correction is needed.

## Dependency modules

`lem-weil-pbc-uniform-complete-triangulated` now has a recorded unlifted-coefficient
interface, which does not directly apply to the lifted coefficient category used
by this item (see the current prerequisite interface repair below). Under §1(B),
this delivery supplies `Sheaf.Paper.PbcUniformCompleteTriangulated`,
with the statement
`ObjectProperty.IsClosedUnderIsomorphisms
  (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)) ∧
ObjectProperty.IsTriangulated
  (PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E))`.
The hypotheses are exactly the node's prime, finite coefficient extension,
Noetherian finite-dimensional scheme, and invertibility condition. The first
conjunct is ambient isomorphism closure; Mathlib's second predicate includes
zero, all shifts, and cone closure. Its full-subcategory instances give the
inherited triangulation and exact inclusion. The docstring includes all eight
recorded proof steps, including uniform bounds, compatible étale witnesses,
normalization, the Koszul signs, and every vertex position. Only `lean` is
changed in this node. The item cites it as an additional statement dependency,
as authorized by the human's unstated-prerequisite instruction.

The current published `prop-weil-pbc-site-comparison-finite-level` and
`thm-weil-pbc-site-comparison` interfaces are reused unchanged. During earlier
repair rounds their compiled imports were unusable, so this sandbox carried
source recompilation copies. The fresh second reader opened both current
server sources: their definitions, statements and modern imports agree with
those copies. The final two-file compilation checks their usability without
redelivery. Their two redundant module and node copies are removed from the
delivery, and no published comparison record is overwritten.

The historical validation and repair sections below describe earlier four-file
packets. The final inventory is the item module and its one lifted-coefficient
uniform-triangulation dependency module, as recorded in the fresh second reading.

## Earlier second reading (a previous round; superseded)

I independently read the node, the delivered Lean, the saved full blueprint source
`scratchpad/blueprint-source.md`, and the source corollary in
`scratchpad/uniform-source.md`. I read the Stacks `proposition-construct-localization`
passage (Tag 05R6) in `scratchpad/localization-source.tex`: its hypotheses are a
pretriangulated category and a compatible multiplicative system, and its conclusion
uses the induced shift and exactly the triangles isomorphic to integral images.
The specialized raw scalar-localization theorem supplies those structures here.
There is no statement correction: the sandbox item's mathematical statement and
proof remain identical to the shared node. No target statement changes.

Here is my object, hypothesis, and conclusion checklist, in source order.

1. Prime ell, finite E/Q_ell, valuation ring and uniformizer: `(l : ℕ)
   [Fact l.Prime]`, `(E : Type u) [Field E] [Algebra ℚ_[l] E]
   [FiniteDimensional ℚ_[l] E]`, and the published `PbcIntegralRing l E`,
   `pbcUniformizer l E`. Verdict: exact. I opened their definitions in the current
   server `BoundedConstructibleComplete` source. The ring is the ULift of the
   actual integer ring, the uniformizer is its ULift, and the ideal in
   `pbcIntegralDatum` is its actual principal ideal. No field replaces the
   integral ring. `pbcRationalCoefficientEquiv` transports through ULift and the
   fraction-normalized `coefficientExtension_localization_uniformizer`, whose
   signature specifies x/pi^n explicitly; the resulting E-action is canonical.
2. The integral categories and their raw rationalizations: `X Y : Scheme.{u}`,
   `[IsNoetherian X] [IsNoetherian Y]`, the dimension bounds `hX, hY`, and
   invertibility conditions `iX, iY` introduce exactly the bases on which
   `def-weil-pbc-rational-category` defines them. Verdict: exact, with no extra
   properness, nonemptiness, finite Tor dimension, or projectivity condition.
   I opened `PbcIntegralCategory`, `PbcIsBoundedConstructibleComplete`,
   `PbcBoundedConstructibleComplete`, `PbcRationalDerivedCategory`, and
   `pbcRationalization` in the current server sources. The integral property is
   the conjunction of intrinsic completeness, uniform constructible reductions,
   and compatible etale origins; morphisms are all ambient morphisms. The
   rational category is `ScalarLocalization`, not its Karoubi completion.
3. A supplied exact integral-linear F between those categories: the binders
   `F : PbcIntegralCategory ... X ... ⥤ PbcIntegralCategory ... Y ...`,
   `[F.Additive] [F.Linear (PbcIntegralRing l E)] [F.CommShift ℤ]
   [F.IsTriangulated]`. Verdict: exact. The two linearity classes together say
   that Hom maps are module homomorphisms. I read the Mathlib signatures named
   by `def-weil-linear-functor` and `def-weil-triangulated-category`; no hidden
   preservation hypothesis occurs.
4. Existence, agreement on objects/integral morphisms, and E-linearity:
   `pbcRationalExtension` is the actual `ScalarLocalization.transport`.
   `transport.obj K := ⟨F.obj K.obj⟩` gives object agreement; `transportHom` is
   `(F.mapLinearMap R).baseChange (Localization.Away p)`. The first three
   conjuncts of `pbcRationalTransport` give additivity, E-linearity, and
   `map (a • Q.map f) = a ⊗ F.map f` as HEq. Verdict: exact. I read the source
   `ScalarLocalization.localization`: its map is literally `1 ⊗ f`, so the
   displayed input is precisely `a ⊗ f`; a = 1 gives integral agreement.
   TensorProduct.comm converts the scalar-first order to the node's order.
5. Uniqueness: the H conjunct quantifies over every additive E-linear H,
   assumes equality on integral objects and HEq on integral arrows, and gives
   `H = pbcRationalExtension ... F`. Verdict: exact. The endpoints are fixed
   by object equalities; HEq handles dependent Hom types without permitting
   arbitrary endpoint isomorphisms. Pure tensors generate every Hom module.
6. Exactness with localized shift comparison: `HasExactPbcRationalTransport`
   existentially supplies a coherent `CommShift ℤ`, its `IsTriangulated`
   property, and the HEq equating the degree-one comparison to
   `1 ⊗ (F.commShiftIso 1).hom.app K`. Verdict: exact. I opened Mathlib's
   `Functor.CommShift`: it includes zero and addition coherence for all
   integers. Degree one is the comparison used in the definition of an exact
   functor and determines the remaining integer comparisons coherently.
   The chosen rational structure comes from the named scalar-localization
   theorem with its tensor-induced shift and identity Q-comparison; it is not
   an unspecified triangulation selected from a bare existence assertion.
7. Every natural transformation between two supplied exact integral-linear
   functors: the final G/eta conjunct has the same four class binders for G
   and quantifies over every `η : F ⟶ G`; `∃! e` prescribes every component as
   `1 ⊗ η.app K`. Verdict: exact. No shift-compatibility restriction is added
   to eta. `transportNat` has these actual components and a separately named
   naturality theorem. All rational objects are integral objects, so the
   uniqueness condition ranges over every component.
8. Four schemes and four supplied exact integral operations: the additional
   X', Y', dimension, invertibility and Noetherian binders and the functors
   `Rf`, `Rf'`, `Lg`, `Lg'` in `pbcRationalExchange` have exactly the node's
   sources and targets. Each has the same exactness and linearity hypotheses.
   Verdict: exact. In particular `(Ex : Rf ⋙ Lg ⟶ Lg' ⋙ Rf')` is the specified
   integral exchange in the correct composition order. There is no implicit
   claim of constructibility preservation for arbitrary scheme maps.
9. The four extensions are exact and the specified exchange extends between
   their composites: the four `HasExactPbcRationalTransport` conjuncts and
   the final `∃! e` with `HEq (e.app ⟨K⟩) (1 ⊗ Ex.app K)` render this clause.
   Verdict: exact. Linearity of each extension is already the main theorem's
   second conjunct. The component condition retains the particular Ex,
   without substituting an arbitrary isomorphism of endpoints.

Dependency reading and repairs:

- `lem-weil-pbc-uniform-complete-triangulated` already exists as a DAG node;
  no new definition node is introduced. I read its complete statement and
  eight proof steps, its source corollary, the module, and Mathlib's
  `ObjectProperty.IsTriangulated` and full-subcategory instances. The first
  conjunct explicitly supplies ambient isomorphism closure (which Mathlib's
  triangulation predicate alone does not assume). The second supplies zero,
  every integer shift, and triangle closure; Mathlib gives inherited
  triangulation and exact inclusion. Thus every clause of the dependency
  is present, including arbitrary morphisms and all vertex positions.
  Its docstring carries all eight steps. The already available
  `pbcIntegralProperty_isTriangulated` in `IntegralTStructure` supplies only
  the triangulation conjunct, not ambient isomorphism closure, so it is not
  an exact existing declaration of this node. The structure helpers in this
  item specialize existing Mathlib full-subcategory structures and the one
  scalar-localization theorem; they introduce no second category, scalar
  action on the integral category, or definition of constructibility.
- The shared dependency records advanced during this reading. In particular
  `lem-weil-pbc-comparison-pullback` now records Q24's
  `Sheaf.Paper.CompactSupportComparisonPullbackCoherence` and
  `cbcComparison_pullback_coherent`. I opened its full current source via
  `scompile.py --source`: the comparison is still the actual restriction
  comparison's adjunction mate, with identity, arbitrary-composite, and
  specified-Cartesian-square equations for sets, abelian groups and finite
  fixed-ring modules. I replaced the prerequisite's stale proof import with
  that recorded module and removed our obsolete comparison module and node
  copy. This also removes a stale `reviewed_lean` overwrite. No new copy of
  the comparison and no dependency metadata reversal is delivered.
- The uniform-triangulation module omitted the now-recorded local-effectivity
  proof import and used earlier completion/constructibility presentations.
  I changed those proof imports to the currently recorded
  `IntrinsicCompletion`, `ProEtaleConstructibleCoefficientSheaf`, and
  `NormalizedConstructibleTowerLocalEffectivity`, and explicitly imported
  `AdicCoefficientDatum`. I opened the definitions/signatures: completion
  re-exports the actual completed Koszul construction through normalized
  coefficient transport; constructibility applies to the ringed modules of
  the tower; local effectivity gives the common local-model data from a
  normalized intrinsically constructible tower and one interval. This
  retains the node's actual notions and its complete stage-3 proof plan.
- The remaining finite-level comparison dependency's mathematical source is
  unchanged (only its module docstring explains recompilation). I read its
  exactness, canonical unit, and positive-degree injective-acyclicity
  signature against its node and all four proof steps: no clause or
  hypothesis changes. Its overlay remains to compile the owning interface
  against the finite-coefficient import closure; its lean.note now records
  that the comparison-pullback interface is reused rather than redelivered.
- I added the direct Mathlib `Triangulated.Pretriangulated` proof import to
  the item, matching the recorded proof dependency. The main signatures
  and actual tensor-map definitions did not need rewriting.

Edge cases: zero objects, zero maps and eta, identity functors, identity
and composite exchanges, a = 0 and a = 1, and shifts -1, 0, 1 and arbitrary
integers remain in the quantifiers. The empty scheme is permitted; invertibility
is vacuous there and a natural dimension bound is allowed. In the inherited
category zero has its zero local models, including the empty-stratification
case. There is no indexing set in this item, nor an excluded tower level:
positive quotients are indexed by n+1 in the published category. Ell is any
prime, including 2, and precisely the source's invertibility assumption is
retained. The generic tensor helpers have independent object/Hom universes
for C and D. The scheme specialization uses the published common size
convention and ULift for coefficients, retaining the small pro-etale site's
distinct object and morphism universes. No universe is unbound.

Independent searches (made with different wording from the first reader):
`msearch.py leanfinder` for “Tensor extension of a linear functor between two
categories extends natural transformations uniquely” returned module scalar
extension Hom-ext lemmas and Day-convolution extensionality, not this theorem.
`msearch.py loogle CategoryTheory.Localization.functor_linear_iff` found that
exact generic localization-linearity lemma; I read it and
`Localization.liftNatTrans` in Predicate.lean. Both require an already
identified categorical localization and do not state this raw tensor
construction, its normalized exactness, or specified exchange.
`msearch.py grep rationali[sz].*(transport|functor)|tensor.*(extension|functor)`
returned tensor functor material, no exact match. Independent rg searches
on Mathlib, upstream WeilConjectures and shared lean/Sheaf included
`baseChange.*Functor|Functor.*baseChange|mapLinearMap|liftNatTrans` and the
new declaration names. I opened upstream
`DerivedCategory/Complete/RationalizationMap.lean`: its `Rationalization.map`
is a categorical localization at torsion-cone maps, with a comparison
isomorphism, rather than the specified raw category and strict object/Hom
formulas. I also read `ScalarLocalization.map`, which covers endofunctors
only, and the existing localized-t-structure structure specializations;
none states this cross-category transport/exchange proposition. No existing
exact match and no missing independent definition was found.

H5/H6/H8/H9 check: tensor data and natural-transformation components are
explicit; proof fields refer to separately named theorems. The coefficient
equivalence is fixed on fractions. The localization structure is
characterized by the existing theorem, rather than a bare Nonempty choice.
Every postponed theorem is a named helper of its owning node or the named
main statement, has a source/blueprint docstring and natural-language proof,
and retains `sorry`. All delivered lines fit 100 characters and the node's
lean.statement matches its theorem signature verbatim. No mathematical
statement correction, new node, or target edit was needed.


Compilation validation: the local pass found no olean for the newly published
coefficient constructibility interface. An import-closure check also found local
normalized-tower local-effectivity compilation absent. The prescribed wrapper
then confirmed on the server: it compiled these current published sources and
the then-current three delivery files cleanly, with no warning. Thus their interfaces are
usable and neither dependency needs redelivery. I removed the two temporarily
prepared source copies and cancelled the redundant five-file validation. That earlier packet contained the finite-level comparison, uniform triangulation,
and rational transport modules. The final immutable delivery also contains the
bounded-below derived comparison module, for four modules in total. I kept the independent reading below because
both declarations are in the prerequisite's proof plan.

I read both dependency nodes and their complete Lean modules. For
`def-weil-proetale-constructible-sheaf`, `(Y : Scheme.{u})`, finite commutative
`A : Type (u+1)`, and `F : pbcModules Y (adicLisseConstantRing Y A)` are the
node's scheme, finite coefficients, constant ring sheaf, and module sheaf.
The existential `LocallyClosedStratification`, `0 < S.n`, constructible
strata, and `IsRelativelyFiniteLisseModule` on every actual inverse-image
restriction say exactly its finite partition and locally finite constant
modules. Local finite constants are equivalent to local constancy with
finite stalks, after refining a trivializing covering. A single empty
stratum handles the empty scheme. No etale-origin assumption is added.
The existing predicate and its current coefficient-universe repair are reused,
not replaced with the older fixed-module presentation.

For `lem-weil-pbc-normalized-constructible-local-effectivity`, I checked
`[IsNoetherian X]`, `AdicCoefficientDatum A`, the actual `AdicTower X d`,
constructible cohomology of every level via the canonical constant-to-functions
comparison, `(a b : ℤ) (hab : a ≤ b)`, and the uniform out-of-interval
`IsZero` condition. The two conclusions are bounded constructible etale
origin at every level and `IsUniformlyBoundedConstructibleAdicTower d M`.
The origin helper uses actual cochain representatives and restriction along
the existing coefficient-ring isomorphism; it is not an arbitrary map.
These are exactly the node's normalized-tower, common-bound hypotheses
and both conclusions. Quotients are indexed by n+1, so n = 0 is the first
positive quotient. The zero tower and empty scheme remain covered, and
there is no finite Tor or projectivity hypothesis. Its eight-step proof
docstring matches the node, including boundedness before full faithfulness,
normalization cocycles, compatible trivializations, the nonprojective
first term, and the actual restricted completed coefficient ring.
Both dependency records are reused from the shared base; no statement_change is needed.

The earlier three-file scompile.py server confirmation passed its files under the prescribed
nice 19, two-thread, 60-second-per-file limits. No errors or warnings remain.

## Earlier second reading (a previous round; superseded)

I reread the node statement, its source blueprint paragraph, the complete Lean
module, and every dependency record. The matching is as follows.

1. The finite extension data are `l : ℕ` with `[Fact l.Prime]`, `E : Type u`
   with `[Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`; the canonical
   integral ring and uniformizer are `PbcIntegralRing l E` and
   `pbcUniformizer l E`. Verdict: exact, with no field or coefficient-category
   substitution.
2. The integral and raw rational categories are rendered by
   `PbcIntegralCategory l E T hT hInv` and
   `PbcRationalDerivedCategory l E T hT hInv`, with `T : Scheme.{u}`,
   `[IsNoetherian T]`, `∃ d, topologicalKrullDim T ≤ d`, and stalkwise
   `IsUnit (l : T.presheaf.stalk t)`. Verdict: exact for every `T`, including
   the empty scheme; no properness, nonemptiness, or projectivity is added.
3. The generic functor clause is `ScalarLocalization.transport` and
   `pbcRationalExtension`; `transportHom` is the actual
   `LinearMap.baseChange` map. `[F.Additive]`, `[F.Linear (PbcIntegralRing l E)]`,
   `[F.CommShift ℤ]`, and `[F.IsTriangulated]` render the exact integral-linear
   hypotheses. Verdict: exact.
4. The first conclusion conjuncts of `pbcRationalTransport` state additivity,
   `Linear E`, and the explicit `HEq` formula for every integral `f` and
   localized scalar `a`; `transport_unique` supplies object and scalar-one-map
   uniqueness. Verdict: exact, including `a = 0`, `a = 1`, zero maps, and all
   objects.
5. `HasExactPbcRationalTransport` existentially supplies the localized
   `CommShift ℤ`, `IsTriangulated`, and the degree-one comparison
   `1 ⊗ (F.commShiftIso 1).hom.app K`. Verdict: exact; the comparison is tied to
   the given integral shift and is not an arbitrary isomorphism.
6. The natural-transformation clause quantifies over every second exact
   integral-linear `G` and every `η : F ⟶ G`, and gives the unique rational
   transformation with components `1 ⊗ η.app K`. Verdict: exact, including
   identity and zero transformations.
7. `pbcRationalExchange` introduces the four schemes and the four supplied
   exact integral functors with the stated composition order
   `Rf ⋙ Lg ⟶ Lg' ⋙ Rf'`; its four exactness conjuncts and final `∃!` component
   equation render the specified exchange. Verdict: exact and conditional on
   supplied operations, as the source requires; no arbitrary scheme-map
   preservation assertion is introduced.

The dependency `lem-weil-pbc-uniform-complete-triangulated` is rendered by
`pbcIntegralUniformComplete_isTriangulated`; it has the node's closure and triangulation
conjuncts for the published completed integral category. During compilation I
found that its `ObjectProperty` result needed explicit category and universe
arguments: without `ObjectProperty.IsClosedUnderIsomorphisms.{u + 2, u + 2}
(C := PbcCompletedDerived T (pbcIntegralDatum l E))` Lean misparsed the property
as a function field and rejected the module. I added those explicit arguments
and updated that dependency's recorded signature verbatim. This is the only
mismatch found. The item theorem's recorded signature was already verbatim.

Edge cases checked are the empty scheme and vacuous stalk condition, zero
objects/maps/transformations, identity functors and exchanges, scalar zero and
one, arbitrary integer shifts including zero and negative shifts, and prime
`l = 2`; all remain covered. There is no index set, no excluded `n = 0` case,
and no universe equality between the generic scalar-localization categories or
between the scheme and small-site encodings.

Independent searches used `msearch.py` LeanFinder and Loogle queries for scalar
localized functor extension, `rg` over Mathlib, `WeilConjectures`, and
`lean/Sheaf` for `rational transport`, `mapLinearMap`, `liftNatTrans`, and
`ScalarLocalization`. They found only generic localization infrastructure and
the existing endofunctor `ScalarLocalization.map`; none states this raw
cross-category tensor extension, exactness, uniqueness, or specified exchange.
The dependency declarations were also searched by full name and opened; no
second definition or existing exact statement was found.


## Maintainer immutable-delivery validation

The immutable delivery at 0eb26e4cd22a04d8411aa9c443fd2513baeb6d03 contains
four Lean modules: ProEtaleSiteComparisonFiniteLevel,
ProEtaleSiteComparisonDerived, PbcUniformCompleteTriangulated, and
PbcRationalTransport. The earlier three-file validation narrative above is
historical, not the inventory of this final delivery. Both required report
sections are retained.

The maintainer independently compiled all four immutable sources together
through scompile.py using the local side overlay. Every sandbox and library
compile passed without diagnostics, including the two comparison modules.
The uniform-triangulation replacement only aligns the indentation of its
second conjunct with its recorded signature; its mathematics is unchanged.
The derived-comparison record is the merge tool's whitespace-normalized
signature, with exactly the same binders and conclusion as its displayed
multiline signature. No declaration or hypothesis is changed.

The final corrected four-file packet was then compiled together through
scompile.py as well: exit 0, no errors or warnings. The replacement uniform
signature matches its immutable node record literally. No server fallback,
global build, or project-clone edit was needed.


## Repair of return L (immutable head 0eb26e4cd22a)

The return reported an unsupported reviewer-fix path for the already delivered
`PbcUniformCompleteTriangulated.lean`. I read the independent review and both
complete replacement files. Its substantive fixes are now incorporated in the
normal sandbox delivery: the second conjunction's indentation agrees literally
with the dependency's `lean.statement`, and the report accurately inventories
all four modules and reuses the published pullback-coherence interface. No
mathematical signature, hypothesis, conclusion, definition or proof is changed.
The dependency record was regenerated from the corrected source signature.
The derived-comparison record now also preserves its full multiline signature
verbatim, rather than the previously accepted whitespace normalization.

This removes the need to apply either reviewer replacement during landing. If
a second reader needs a further replacement of an already delivered module,
the return's supported reviewer layout is `DIR/<basename>.lean`; a full
`DIR/lean/Sheaf/...` path must not be submitted as a new module. The ordinary
worker delivery retains the required `lean/Sheaf/...` layout for deliver2.py.
Compilation and the required dry run are repeated below for this repaired packet.


## Current prerequisite interface repair

During this repair the shared node's recorded interface advanced to Q01's
`Sheaf.Paper.UniformCompleteTriangulated`. I read its current server source
with `scompile.py --source` and the complete `IntegralUniformCoefficient`
source. That theorem uses `E : Type (u+1)`, the unlifted
`pbcPadicCoefficientDatum`, and `IsPbcBoundedConstructibleComplete`. The
published rational category used by this item instead takes `E : Type u`
and uses the lifted valuation ring and `pbcIntegralDatum`. Those coefficient
sheaves and their derived categories are not definitionally identical.

Under §1(B), this delivery therefore supplies the same closure assertion for
its dependency's published lifted-coefficient realization. I renamed its
theorem to `AlgebraicGeometry.Scheme.pbcIntegralUniformComplete_isTriangulated`
and updated the consumer and its `lean` record, avoiding a duplicate of Q01's
declaration. The source statements and all hypotheses/conclusions are unchanged.
No completion, category, tensor or tower definition is introduced. Searches
with `rg` in the upstream source and shared `lean/Sheaf` found no existing
declaration with the new name. The dependency `lean.note` records the exact
interface mismatch; all maintainer-owned node fields were refreshed unchanged.


Repair validation: the final four-file `scompile.py` invocation exited 0.
The local mirror lacked `AdicCoefficientDatum.olean`, so the wrapper confirmed
against current server sources. All four delivery modules and their side-only
dependency closure compiled without errors or warnings, with nice 19, two
threads and the unchanged 60-second limit per file. The repaired triangulation
module took 2.3 seconds and its rational-transport consumer 13.4 seconds.
Every delivery node's `lean.statement` occurs verbatim in its owning source.

## Earlier second reading (a previous round; superseded)

This is a fresh independent reading of the repaired packet. I read the complete
node, all five proof steps, all four original packet modules, and the recorded dependency
signatures. I also read the actual blueprint paragraph and proof, the constructible
restriction corollary, Stacks `derived.tex` proposition-construct-localization
(05R6), and `proetale.tex` lemma-compare-derived and lemma-relative-comparison
from the server literature copy. The local shared clone omits fetched literature.
The blueprint transport assertion concerns supplied integral operations. Stacks 05R6
assumes a compatible multiplicative system and defines distinguished localized
triangles as isomorphic images; these conditions are supplied by the recorded
scalar-localization theorem, not extra hypotheses on F.

The objects, hypotheses and conclusions, matched item by item:

1. A prime ell and finite extension E/Q_ell: `(l : ℕ) [Fact l.Prime]`,
   `(E : Type u) [Field E] [Algebra ℚ_[l] E]`, and
   `[FiniteDimensional ℚ_[l] E]`. Verdict: exact. The valuation ring and specified
   uniformizer are the imported `PbcIntegralRing l E` and `pbcUniformizer l E`.
   I opened `BoundedConstructibleComplete`: these are the actual valuation ring
   and uniformizer with ULift, and `pbcIntegralDatum` has the actual principal
   ideal and positive quotients. No arbitrary coefficient ring is substituted.
2. Integral constructible categories C and D: the source/target of `F` are
   `PbcIntegralCategory l E X hX iX` and its Y counterpart. I read their full
   definition, including intrinsic completion, common uniformly bounded adic
   local models, the actual normalized reduction transitions, and compatible
   bounded-below etale origins. Verdict: exactly the dependency's full categories;
   their Hom sets contain every ambient derived morphism between their objects.
3. Schemes for which those categories are defined: `X Y : Scheme.{u}` with
   `[IsNoetherian X] [IsNoetherian Y]`, `hX`/`hY` the natural finite dimension
   bounds, and `iX`/`iY` stalkwise invertibility of ell. Verdict: exactly the
   imported category's hypotheses. No finite Tor, projectivity, nonemptiness,
   properness, or scheme morphism is assumed.
4. Raw rationalizations: `PbcRationalDerivedCategory` is the imported
   `ScalarLocalization` specialization. I opened `PbcRationalCategory` and
   `ScalarLocalization`: objects are the wrapped integral objects, Hom is
   `Localization.Away p ⊗[R] Hom`, identity is `1 ⊗ id`, and composition is the
   uniquely specified bilinear extension. Verdict: exact, without a Karoubi
   envelope. `pbcRationalCoefficientEquiv` uses ULift.ringEquiv and the recorded
   fraction-normalized localization equivalence. I read its fraction formula;
   thus `pbcRationalLinear` gives the intended E-action, not an arbitrary action.
5. An exact integral-linear F: `[F.Additive] [F.Linear (PbcIntegralRing l E)]`
   and `[F.CommShift ℤ] [F.IsTriangulated]`. I read Mathlib's definitions of
   `Functor.Linear`, `Functor.Additive`, and `Functor.IsTriangulated` against
   the two dependency nodes. Verdict: exactly linearity and exactness, with the
   supplied coherent shift comparison. No extra condition on transformations
   commuting with shifts is introduced.
6. Existence and agreement on objects and integral morphisms: the actual
   `pbcRationalExtension` has object map `K ↦ ⟨F.obj K.obj⟩` and Hom map
   `(F.mapLinearMap R).baseChange (Localization.Away p)`. The main theorem's
   first three conjuncts assert additivity, E-linearity, and the formula
   `a • Q.map f ↦ a ⊗ F.map f`. Verdict: exact; `a = 1` gives the required
   integral agreement. Scalar-first tensors are the source's Hom-first tensors
   under TensorProduct.comm. The helper uses the existing tensor base-change
   map, whose `baseChange_tmul` formula I opened.
7. Uniqueness: the H conjunct quantifies over every additive E-linear functor
   with the same object values and integral maps and concludes equality to
   `pbcRationalExtension`. Verdict: exact E-linear uniqueness. The HEq compares
   the same prescribed arrows after the stipulated object equalities, rather
   than allowing a chosen isomorphism or changing the agreement condition.
8. Exactness with localized shift comparison: `HasExactPbcRationalTransport`
   existentially supplies a coherent CommShift structure, asserts triangulated
   exactness for that structure, and fixes its degree-one component to
   `1 ⊗ (F.commShiftIso 1).hom.app K`. Verdict: exact. I read the complete
   scalar-localization structure theorem: it fixes the tensor-induced shift
   functor, identity comparison of Q, and precisely the isomorphic image
   triangles. Consequently the structure choices here retain those
   characterizations; they are not choices of an unspecified triangulation.
9. A second such functor and every natural transformation: the G conjunct has
   the same four class hypotheses and quantifies over every `η : F ⟶ G`.
   Its `∃! e` fixes every component to `1 ⊗ η.app K`. Verdict: exact. I checked
   `transportNat`: its data are those actual components and its proof field
   refers to the separately named naturality theorem. All rational objects
   are integral objects, so the uniqueness condition covers all components.
10. Four schemes, four supplied operations and a specified exchange: the
    additional `X' Y'` have the same geometric hypotheses; the four `Rf`,
    `Rf'`, `Lg`, `Lg'` have exactly the node's sources, targets and exact
    integral-linear hypotheses. `Ex : Rf ⋙ Lg ⟶ Lg' ⋙ Rf'` has the specified
    direction. Verdict: exact. The Lean takes supplied operations, as the
    node does, and imposes no unmentioned preservation assertion.
11. Their rational exactness and extension of that exchange: the first four
    conjuncts of `pbcRationalExchange` give localized exactness; E-linearity
    follows for each from `pbcRationalTransport`. Its `∃! e` is between the
    composites of the four actual extensions and fixes the component to
    `1 ⊗ Ex.app K`. Verdict: exact. It retains the specified Ex, including
    its endpoints and all components.

Dependency review: the uniform-triangulation node already exists; no new node
is needed. I read its eight proof steps against the complete delivered module.
The two conclusion predicates assert ambient isomorphism closure and zero,
integer-shift and middle-vertex closure. I read Mathlib Subcategory.lean:
rotation gives the other vertex cases, and the full subcategory inherits exactly
ambient distinguished triangles, triangulation, and an exact inclusion. This
therefore includes every clause of the node. Its proof docstring preserves all
eight steps, including completeness of arbitrary cones, a single bound,
boundedness before lifting quotient tensors, compatible witnesses and cocycles.
The published `UniformCompleteTriangulated` instead uses the unlifted
`pbcPadicCoefficientDatum` with E in Type (u+1). I opened it and
`IntegralUniformCoefficient`; it cannot directly instantiate the lifted
`pbcIntegralDatum` realization used by the published rational category.
The delivered §1(B) interface repairs this difference without redefining a
category or a coefficient construction. `IntegralTStructure` supplies only
IsTriangulated, not the node's ambient isomorphism closure, so it is not an
exact existing statement of this dependency.

I also read both finite-level and bounded-below comparison modules against
their nodes. Finite level quantifies over all finite rings and all module
sheaves, and asserts exactness, the actual unit isomorphism, and positive-degree
injective acyclicity. Bounded below retains all finite discrete rings and all
bounded-below complexes, the canonical inverse image, its transported derived
adjunction, full faithfulness and invertibility of the derived unit. No
constructibility, individual-module finiteness, upper bound, or commutativity
is assumed. Their actual current server sources now agree with the sandbox
sources apart from explanatory comments; their reusable status is checked below.

Edge cases: zero objects/maps/transformations, identity F/G, scalar 0 and 1,
identity/composite exchanges, and arbitrary positive, zero and negative shifts
are all quantified. The empty scheme is permitted: its stalk hypothesis is
vacuous and its dimension has a natural bound. There is no index-set restriction.
The positive adic quotient indexed by n = 0 is the first quotient, not omitted.
Every prime, including 2, is covered subject to the stated invertibility.
The generic helpers have independent source/target object and Hom universes.
The scheme specialization uses the dependency's published common size
convention and coefficient ULift; the small site's object and morphism
universes are not identified. All variables/universes are explicitly bound.

Independent searches, with queries different from the worker's:

- LeanSearch: “Tensor base change of morphism modules extends a linear functor
  to a scalar localized category” returned LinearMap.baseChange/baseChangeHom,
  LinearEquiv.baseChange and module extension-of-scalars maps. I opened the
  base-change definition and pure-tensor formula; the module uses this result.
  None states the category-level exact extension, uniqueness and exchange.
- LeanFinder: “Extension of scalars on Hom modules defines a functor between
  linear categories and lifts every natural transformation” returned
  Functor.mapLinearMap and module (co)extension-of-scalars. These supply Hom
  maps, not the proposition on the actual raw rational categories.
- Loogle: `CategoryTheory.Localization.liftNatTrans` found that construction,
  its component formula, and coherence lemmas. I opened Predicate.lean and
  upstream RationalizationMap.lean. They require an identified categorical
  localization and give comparison-isomorphism formulas; the upstream
  rationalization is a localization at torsion-cone arrows. They do not give
  this raw tensor category's strict object and Hom formulas as stated here.
- msearch grep `change.*scalar.*functor|scalar.*extension.*functor|transportNat`
  returned no hits. Independent rg on Mathlib, upstream WeilConjectures and
  shared lean/Sheaf checked `ScalarLocalization`, `transportNat`,
  `pbcRationalTransport`, `pbcRationalExtension`, and Rationalization functoriality.
  The existing ScalarLocalization.map handles endofunctors only. No existing
  exact match for this item or missing independent notion was found.

H5/H6/H8/H9: all tensor/functor data are actual constructions; required proofs
are named theorems. The coefficient equivalence is determined on fractions;
the localized structures are characterized by shift and image triangles.
All seven remaining named theorem proofs are `sorry`, and their source and
blueprint docstrings give the relevant node proof steps. No theorem was proved.
Lines are at most 100 characters. All four initial node signatures occurred
verbatim in their sources. No statement_change or target edit is needed.
The missing prescribed second-reading heading was a report defect; this
section supplies the fresh clause-by-clause reading without relabelling an
older reading.


Final repair and inventory: I removed the two redundant comparison-module and
node copies after confirming their current published source interfaces; their
old records would only overwrite metadata and comments of already repaired
nodes. I also corrected the item lean.note to describe the actual lifted
triangulation interface repair. The only delivered Lean files are now
`lean/Sheaf/Paper/PbcUniformCompleteTriangulated.lean` and
`lean/Sheaf/Paper/PbcRationalTransport.lean`. Their mathematical statements and
all constructions are unchanged by this second reading. No new nodes, statement
correction, private notions, or target edits are delivered.

Final compilation: the prescribed scompile.py invocation with just those two
modules exited 0 locally, without errors or warnings. It used the published
comparison interfaces, confirming that neither comparison module needs
redelivery. Both files were checked separately in sandbox and library form,
under the wrapper's unchanged nice 19, two-thread and 60-second compiler limits.
Their final lean.statement records still match the source signatures verbatim.

## Repair of return L (immutable head 9440017017c5)

The reported collision is removed entirely. The delivery no longer declares
`AlgebraicGeometry.Scheme.pbcRationalShiftAdditive`, nor an alias or a renamed
version of it. That name remains owned solely by
`Sheaf.Paper.CommonStageCalculus`. I opened the full current server source
with `scompile.py --source`, its shift existence/normalization and additivity
declarations, and the definitions of `pbcStageDatum`, `pbcStageUniformizer`,
and `pbcFiniteField` in `PbcFiniteCompletedCoefficientMap`.

The existing theorem has parameters `Ω`, an algebraic-closure structure, and
`E : Padic.FiniteCoefficientFields l Ω`; its category uses
`pbcIntegralDatum l (Shrink E.val)` and its shift is `pbcRationalHasShift`,
chosen from `pbcRationalShift_exists`. The transport statement quantifies over
an arbitrary finite extension `E : Type u`, and its shift is the witness of
`ScalarLocalization.exists_triangulated_scalarLocalization`. Consequently
importing the common-stage theorem does not supply the required instance for
this general category and this chosen shift. Restricting the transport theorem
to its small subfield model would lose the stated arbitrary-extension case.

Instead of renaming the duplicate, I removed it and the two dependent global
rational pretriangulation/triangulation instances. The definition
`HasExactPbcRationalTransport` now directly reuses the additive-shift and
pretriangulation witnesses of the already imported
`ScalarLocalization.exists_triangulated_scalarLocalization`, specialized by
`pbcRationalTriangulationData`. Its body installs those exact same witnesses
for its two categories before forming the same proposition. No new additivity
fact is stated, proved or postulated. The zero objects, shifts, distinguished
triangles, localized shift comparison, and functor/exchange tensor maps are
unchanged. Both main theorem signatures are unchanged, with no additional
hypothesis. The removed three names are also removed from `lean.declarations`.

The original clause-by-clause worker report and independent second reading
remain applicable to the mathematical statement. In particular the exactness
clause still uses the isomorphic-image distinguished triangles and prescribes
`1 ⊗ (F.commShiftIso 1).hom.app K`, including zero objects, identity functors,
and arbitrary integer shifts. This repair changes where existing structure
witnesses are supplied to the exactness predicate, not their values.

Repair compilation: the prescribed two-file `scompile.py` invocation exited 0
with no errors or warnings. Each module compiled separately, in both sandbox
and library form, using the unchanged 60-second per-file limit. Both recorded
main signatures still occur verbatim in their owning sources. The remaining
published occurrence of the returned declaration name is the common-stage
module and its owning DAG record; this delivery declares no such name.

## Earlier second reading (a previous round; superseded)

I reread the node statement, its blueprint source place (the sole proposition paragraph and
five proof steps), the dependency records, and both delivered modules. The item-by-item
matching is:

1. The coefficient data are a prime `l`, a finite extension `E` of `ℚ_[l]`, its lifted
   integral ring and specified uniformizer: `(l : ℕ) [Fact l.Prime]`,
   `(E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]`,
   `PbcIntegralRing l E`, and `pbcUniformizer l E`. Verdict: exact; the ring and
   uniformizer are the recorded ULift constructions, not arbitrary choices.
2. The integral and raw rational categories are the imported
   `PbcIntegralCategory l E T ...` and `PbcRationalDerivedCategory l E T ...`, with
   Noetherian schemes, finite natural dimension bounds, and stalkwise invertibility of
   `l`. Verdict: exact for every category used by the node; no properness, nonemptiness,
   projectivity, or finite Tor hypothesis was added.
3. The extension is constructed by `ScalarLocalization.transport`; its object map is
   `K ↦ ⟨F.obj K.obj⟩` and its Hom map is
   `(F.mapLinearMap R).baseChange (Localization.Away p)`. Verdict: exact raw
   localization, with actual tensor data and no Karoubi envelope.
4. The integral functor hypotheses are `[Additive]`, `[Linear (PbcIntegralRing l E)]`,
   `[CommShift ℤ]`, and `[IsTriangulated]`. Verdict: these are exactly Mathlib's
   realizations of additive linear exact functors and their coherent shift comparison.
5. The first three conjuncts of `pbcRationalTransport` assert additivity, `E`-linearity,
   and the formula on every scalar multiple of an integral morphism. Verdict: exact;
   scalar one gives integral agreement, and the tensor order is identified by the actual
   base-change map.
6. The uniqueness conjunct quantifies over every additive `E`-linear `H` with the same
   object values and integral maps and concludes `H = pbcRationalExtension`. Verdict:
   exact and in the same quantifier order; it does not add exactness to the uniqueness
   class.
7. `HasExactPbcRationalTransport` supplies a coherent localized shift comparison, fixes
   its degree-one component to `1 ⊗ (F.commShiftIso 1).hom.app K`, and asserts preservation
   of the distinguished localized triangles. Verdict: exact; the supplied
   scalar-localization structure fixes the image-triangle convention.
8. The natural-transformation clause quantifies over every second exact integral `G` and
   every `η : F ⟶ G`, and gives a unique transformation whose components are
   `1 ⊗ η.app K`. Verdict: exact, including zero and identity transformations.
9. The exchange clause supplies `X, Y, X', Y'`, four exact additive integral-linear
   operations with the stated source and target categories, and
   `Ex : Rf ⋙ Lg ⟶ Lg' ⋙ Rf'`. Verdict: exact; the operations are supplied data and no
   scheme-morphism preservation assertion is introduced.
10. Its conclusion gives localized exactness for all four operations and a unique natural
    transformation between the two localized composites with component
    `1 ⊗ Ex.app K`. Verdict: exact and retains the specified exchange direction and
    components.

The dependency `lem-weil-pbc-uniform-complete-triangulated` was reread against its source.
The delivered `pbcIntegralUniformComplete_isTriangulated` uses the lifted
`pbcIntegralDatum`, gives ambient isomorphism closure and the full triangulated closure,
and carries all eight proof steps in its docstring. The recorded published interface uses
an unlifted coefficient realization and therefore was unusable for this category; under
§1(B) I supplied this exact lifted interface and added it to `stmt_deps`. No other
notion was duplicated.

Edge cases checked: empty schemes (vacuous stalk condition and the zero object), zero
objects/maps/transformations, identity functors and exchanges, scalar zero and one, and
positive, zero, and negative integer shifts. Natural upper dimension bounds permit the
empty case. The finite coefficient prime includes `2`; no nonempty index set occurs and
no `n = 0` adic stage is silently removed. All variables and universes are explicitly
bound, with the published common size convention retained.

Independent searches used `msearch.py` LeanFinder/Loogle/grep queries for scalar
localization, tensor extension, `transportNat`, and triangulated functor transport, plus
`rg` over Mathlib, `WeilConjectures`, and `lean/Sheaf`. They found only generic
localization/base-change infrastructure and no exact category-level transport or exchange
statement. The Mathlib leaves `Functor.Linear`, `Functor.Additive`, `CommShift`, and
`Functor.IsTriangulated` match their dependency definitions exactly.

The repairs found in this reading are the already recorded §1(B) lifted-triangulation
module and dependency record; the obsolete rational shift helper and redundant comparison
copies remain removed. I added this required heading only; no target statement was changed.
Both modules compile through the prescribed `scompile.py` wrapper, with only named theorem
`sorry` declarations and no other diagnostics. The node copy's `lean.statement` remains
verbatim equal to `pbcRationalTransport`'s signature.

## Review by Q33

I independently reread the corrected node, the blueprint statement, and the complete Lean module. The generic declaration `transport_exact` now precedes and matches the arbitrary-category clause: its binders expose the coefficient ring, both pretriangulated triangulated linear categories, the exact additive linear functor, and the raw scalar-localization structures. Its conclusions include the tensor transport formulas, a localized shift comparison witnessing triangulated exactness, functor uniqueness from integral objects and scalar-one maps, and unique tensor extension of every natural transformation. The scheme theorem and exchange remain explicit supplied-data specializations, so they do not replace the generic assertion or add an arbitrary scheme-preservation claim. All postponed proofs are named `sorry` theorems with source docstrings, and the dependency repair is separately recorded.

## Second reading by Q33

This is the independent reading of the current delivery, including the newly added
arbitrary-category theorem. The earlier readings above predate that theorem. I read
the node, its blueprint order-1306 paragraph and proof, and derived.tex Tag 05R6
(proposition-construct-localization), including the induced shift and image-triangle
convention in its proof. The blueprint supplies the integral constructible categories;
it does not restrict the supplied functor to one of the geometric operations.

My object/hypothesis/conclusion list and its Lean correspondence are as follows.

1. A finite extension E of Q_l, its valuation ring and uniformizer: the scheme
   specialization binds `l`, `Fact l.Prime`, `E : Type u`, `Field E`, `Algebra ℚ_[l] E`
   and `FiniteDimensional ℚ_[l] E`. `PbcIntegralRing` and `pbcUniformizer` are the
   dependency's actual ULift constructions. Verdict: exact.
2. The integral categories and raw rationalizations: the generic theorem uses
   arbitrary independent-universe R-linear triangulated `C` and `D`, with shift-one
   R-linearity. The specialization uses the recorded `PbcIntegralCategory` and
   `PbcRationalDerivedCategory`, not another model. Each scheme is Noetherian with a
   finite natural dimension bound and stalkwise invertibility of l, precisely the
   hypotheses of the category dependency. Verdict: generic assertion and stipulated
   integral-category application are both present; no geometric preservation premise
   is substituted for a supplied exact functor.
3. The raw Hom tensor construction: `ScalarLocalization` retains integral objects,
   tensors Hom with `Localization.Away p`, and uses bilinear tensor composition.
   `transportHom` is `LinearMap.baseChange` of `F.mapLinearMap R`; `transport` has
   actual object map `K ↦ ⟨F.obj K.obj⟩`. The specialization transports the scalar
   action to E by `pbcRationalCoefficientEquiv`, which uses ULift.ringEquiv followed
   by the fraction-normalized published localization equivalence. Verdict: exact,
   with scalar-first tensors identified by TensorProduct.comm and no Karoubi envelope.
4. Every exact integral-linear functor: `F.Additive`, `F.Linear R`, `F.CommShift ℤ`,
   `F.IsTriangulated` match the two definition nodes. I opened Mathlib's LinearFunctor
   and Triangulated/Functor definitions. Verdict: no extra condition on F; the scheme
   case specializes R to the actual lifted valuation ring.
5. Existence, integral agreement and scalar linearity: `transport_exact` asserts
   additivity, localized-ring linearity, and now explicitly the formula
   `transport.map (a ⊗ f) = a ⊗ F.map f`. Scalar one gives integral agreement;
   the object agreement is the definition of transport. `pbcRationalTransport` gives
   the corresponding E-linearity and formula using `pbcRationalization`. Verdict: exact.
6. Uniqueness: both theorems quantify over every additive scalar-linear H, require
   the same integral objects and integral maps, and conclude equality to the actual
   extension. HEq handles the specified object equalities, not arbitrary endpoint
   isomorphisms. No exactness hypothesis is added to the uniqueness class. Verdict: exact.
7. Exactness with the localized shift comparison: the generic theorem now asserts
   `HasExactTransport R p F`. This installs exactly the zero, shift, additive-shift
   and pretriangulation witnesses of the existing characterized localization theorem,
   then requires a coherent CommShift structure, triangulated exactness, and the
   degree-one component `1 ⊗ (F.commShiftIso 1).hom.app K`. Its scheme counterpart
   `HasExactPbcRationalTransport` uses the same characterized structures specialized
   to the integral categories. Verdict: exact induced localization, not arbitrary
   triangulations. The characterization fixes the induced shift, identity Q
   comparison and precisely the triangles isomorphic to integral image triangles.
8. Every second exact linear G and every natural transformation η: the last conjunct
   of each transport theorem quantifies over G and η in that order and gives `∃! e`
   with every component `1 ⊗ η.app K`. `transportNat` constructs those actual
   components, using a separately named naturality theorem. Verdict: exact; η is
   arbitrary and need not itself commute with shifts.
9. Four schemes and supplied integral operations: `pbcRationalExchange` binds the
   four functors with sources and targets exactly as in the node, each with additive,
   integral-linear and exact structure. `Ex : Rf ⋙ Lg ⟶ Lg' ⋙ Rf'` is exactly the
   specified direction. Verdict: no hypothesis on an unmentioned scheme morphism.
10. Their rational exactness and specified exchange: the four exactness conjuncts
    and `∃! e` between the two composites prescribe `1 ⊗ Ex.app K` at every object.
    The main transport theorem supplies E-linearity for each operation. Verdict:
    exact and retains the given exchange, including identity and zero cases.

Mismatch and repair: the worker's new generic `transport_exact` took arbitrary
HasShift/Pretriangulated/IsTriangulated structures on both scalar localizations,
without relating them to the integral categories. Its exactness assertion therefore
had no justification from the source. It also only asserted the existence of some
shift comparison, without the source's localized component formula. I removed those
unconstrained structure hypotheses and added `HasExactTransport`, which uses the
existing localization theorem's characterized witnesses and explicitly normalizes
that comparison. I also made the generic pure-tensor formula an explicit conjunct.
The scheme theorem and its supplied-exchange application were already correct and
were left unchanged. No node mathematical statement or target changed; the primary
lean.statement was refreshed verbatim and the helper recorded in lean.declarations.

Dependency-module reading (H13): I opened the uniform-triangulation node, its eight
proof steps, its blueprint constructible-complete restriction, and the contextual
Stacks 09C3 local-model lemma. That Stacks lemma concerns constant coefficients and
is not silently used as a replacement for the compatible tower-category closure
statement. The delivered `pbcIntegralUniformComplete_isTriangulated` asserts ambient
isomorphism closure and ObjectProperty.IsTriangulated of precisely
`PbcIsBoundedConstructibleComplete T (pbcIntegralDatum l E)`. I opened the three-clause
predicate and Mathlib Triangulated/Subcategory: ContainsZero, all integer shifts and
middle-vertex closure give all cone/vertex cases by rotation, and the full subcategory
inherits the ambient triangles and exact inclusion. Thus every dependency conclusion
is present. I also opened the currently recorded UniformCompleteTriangulated and
IntegralUniformCoefficient sources: they use the unlifted ring and E in Type (u+1),
so they cannot directly supply this lifted realization. The delivery's §1(B) repair
has the same geometric assumptions and uses the existing predicate; no new notion
or definition node is required. Its docstring preserves all eight proof steps.

Edge cases: zero objects/maps, identity functors and transformations, zero and one
scalars, positive/zero/negative integer shifts, and identity/composite exchanges are
included. Empty schemes are permitted (stalk invertibility is vacuous and a natural
dimension bound exists); no nonempty index set is imposed. The adic index zero
represents the first positive quotient, so no quotient is silently removed. Every
prime including 2 is covered subject to the stated invertibility. Generic source and
target object and Hom universes are independent; the scheme specialization follows
the published lifted-coefficient size convention. Site object and morphism universes
are not equated. I checked every variable and universe is explicitly bound.

Independent reuse searches performed in this reading:

- LeanSearch: `tensoring Hom modules extends exact linear functors with localized
  shift comparison` returned tensor right-exactness and Ext/derived localization
  functoriality, not this exact statement.
- LeanFinder: `An exact linear functor induces an exact functor on categories with
  localized Hom modules and canonical localized shift comparison` returned module
  localization, Ext maps, and generic localization linearity/shift lemmas. None
  specifies the raw tensor category's functor, uniqueness and transformation extension.
- Loogle `LinearMap.baseChange` returned the actual construction, pure-tensor formula,
  and identity/composition laws; these are reused by the delivery, not redeclared.
- msearch grep `HasExactTransport|exact.*scalar.*localization|transport_exact`
  returned only unrelated local algebra occurrences. Independent rg searched Mathlib,
  upstream WeilConjectures, and shared lean/Sheaf for scalar transport and exact
  localization names. The existing ScalarLocalization.map handles endofunctors, not
  independently sized C and D; the characterized triangulation theorem is reused.
  No existing complete statement of this item was found.

H5/H6/H8/H9: all functor and tensor data are real constructions. The localization
structure choices are constrained by the imported characterization, not choices of
an unspecified category or triangulation. All postponed theorems have only `sorry`
proofs and their source/blueprint proof docstrings; no new result is proved. No private
or local definition/notation/instance is introduced. Lines are within 100 characters.
The required current second-reading heading was absent and is supplied here, with
the Worker report retained. The historical arbitrary-triangulation descriptions
above are superseded by this repair and this reading.

Verification: scompile.py compiled both delivered modules individually, in sandbox
and library form, with exit code 0 and no errors or warnings. The unchanged 60-second,
two-thread, nice-19 limits were used. Both node lean.statement fields are verbatim
source signatures. The final delivery dry run and push are recorded below.

Delivery dry run: deliver2.py --no-push printed OK for commit 244be6f73e,
including preflight and compilation of both files. The five-file staged inventory
contained only the report, the two node records, and their two owning Lean modules.
