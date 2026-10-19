## Worker report

The module `Sheaf.AlgebraicGeometry.FlatConstructibleTensor` states
`AlgebraicGeometry.Etale.flatConstructibleTensor_cohomology_and_bounds` with `sorry` as
its entire proof. Its three auxiliary definitions have fully specified data: a full
subcategory property bundling the two hypotheses on the sheaf, and the two actual
bifunctors compared by the theorem. Their maps are the maps of the existing inclusion,
single, derived tensor, homology, ordinary tensor and whiskering functors. There are no
new mathematical hypotheses, axioms, arbitrary comparison maps, or choice definitions.

Hypothesis and clause correspondence:

- A scheme X: `(X : Scheme.{u})`, with no Noetherian, quasi-compactness or separation
  assumption.
- A finite commutative ring Λ: `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
  This is the recorded coefficient universe for the ordinary small-etale construction.
- A sheaf of Λ_X-modules on the small etale site:
  `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, the encoding explicitly recorded
  by def-weil-pbc-etale-sheaves and def-weil-pbc-derived-categories. The tensor on it is
  `Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`, supplied as an
  explicit term wherever the ordinary tensor is used. No file-local instance or notation
  is needed to read any statement outside the file.
- L constructible: the first component of `flatConstructibleEtaleSheafProperty Λ X L`
  is exactly `Scheme.IsConstructibleEtaleModuleSheaf L`, with its finite locally closed
  scheme stratification, constructible parts and finite module values. No replacement
  by a geometric-stalk or Noetherian-scheme predicate is made.
- L flat, meaning - tensor L exact: the second component is the existing
  `CategoryTheory.exactFunctor _ _ (@tensorRight _ _ (Sheaf.monoidalCategory ...) L)`.
  Exactness is preservation of finite limits and finite colimits, exactly the definition
  used by the recorded `SheafOfModules.IsFlatOnSite`. See the dependency-record repair
  below for the difference between the two encodings.
- L[0] in the unbounded derived category:
  `(_root_.DerivedCategory.singleFunctor _ 0).obj L.obj`. The ordinary tensor's derived
  version is the recorded `AlgebraicGeometry.Etale.derivedTensor`, with no bounded or
  completed replacement.
- K in D^b_c: `(K : BoundedConstructibleDerivedCategory Λ X)` bundles precisely the
  recorded `DerivedCategory.isBoundedConstructible Λ X K.obj`. Its full subcategory
  retains every derived-category morphism, including maps not represented by a chosen
  strict model. No finite Tor-amplitude hypothesis occurs.
- Natural isomorphisms H^i(K tensor^L L[0]) ≅ H^i(K) tensor L, for every integer i:
  the first conjunct is `∀ i : ℤ, Nonempty (flatConstructibleTensorCohomologyLeft Λ X i ≅
  flatConstructibleTensorCohomologyRight Λ X i)`. These are natural isomorphisms of
  bifunctors, not merely separate objectwise isomorphisms. The outer variable is the
  full category of flat constructible sheaves and the inner variable is D^b_c.
  The left bifunctor composes inclusion, `singleFunctor`, `derivedTensor.flip`,
  precomposition with the D^b_c inclusion, and postcomposition with `homologyFunctor`.
  Its value is exactly H^i(K tensor^L L[0]). The right bifunctor is ordinary
  `curriedTensor.flip` precomposed with the D^b_c inclusion and `homologyFunctor`;
  its value is exactly H^i(K) tensor L. The tensor factors have the stated order.
  Full subcategories retain arbitrary maps between flat constructible sheaves, so the
  comparison includes naturality in L as well as K.
- These cohomology sheaves are constructible: the second conjunct quantifies over L
  and K and first asserts `∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf` of the
  left bifunctor's value.
- Consequently the tensor is in D^b_c: its next conjunct is
  `DerivedCategory.isBoundedConstructible Λ X` of the displayed derived tensor object.
- Every cohomological interval [a,b] for K is also an interval for the tensor:
  the final conjunct quantifies over arbitrary integers a,b with `a ≤ b`; from
  `∀ i, (i < a ∨ b < i) → IsZero ((homologyFunctor _ i).obj K.obj)` it concludes the
  same vanishing for the left bifunctor's value. No interval is selected or enlarged.

Dependency declarations used, read in their source modules:

- def-weil-pbc-etale-sheaves: `WeilConjectures.AlgebraicGeometry.EtaleSheaves`;
  its record explicitly prescribes the `Sheaf`/`ModuleCat` encoding for this chapter,
  with `CategoryTheory.Sheaf` and `CategoryTheory.constantSheaf` already available.
- def-weil-pbc-etale-constructible-sheaf:
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`,
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`.
- def-pc-flat-sheaf-modules:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`,
  `SheafOfModules.IsFlatOnSite` and its publicly imported underlying
  `CategoryTheory.exactFunctor` (`Mathlib.CategoryTheory.Limits.ExactFunctor`).
- def-weil-pbc-derived-categories: `WeilConjectures.AlgebraicGeometry.DerivedCategories`;
  `AlgebraicGeometry.Etale.DerivedCategoryModule`, `DerivedCategory.singleFunctor`,
  `DerivedCategory.homologyFunctor`, and the existing unbounded `DerivedCategory`.
- def-weil-pbc-constructible-complexes:
  `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`,
  `AlgebraicGeometry.Etale.DerivedCategory.isBoundedConstructible` and
  `AlgebraicGeometry.Etale.BoundedConstructibleDerivedCategory`.
- def-kun-derived-tensor: `WeilConjectures.SixFunctors.Etale.Derived.Tensor`,
  `AlgebraicGeometry.Etale.derivedTensor`.

The stated proof dependencies are imported non-publicly. The docstring reproduces all
five node proof steps: exact tensor and K-flatness of L[0]; K-flat resolution and natural
localization; actual fibre-product refinements; finite locally constant tensor on those
strata; and vanishing with unchanged bounds. The Stacks source was read at
`etale-cohomology.tex`, lemma-tensor-product-constructible (095I) and lemma-tensor-c
(0961). Finite rings are Noetherian. The unbounded exact-functor computation explains
why this flat-factor specialization requires no finite Tor amplitude of K.

Edge cases checked before writing: the empty scheme, zero ring, L = 0, and K = 0 all
produce zero tensor and zero cohomology. For a singleton interval a = b, the conclusion
preserves that same interval; larger intervals are arbitrary and include all zero
complex intervals. The comparison ranges over every i in Z, including zero and negative
indices. On a geometric point with Λ = Z/4, the flat factor Λ and K = Z/2[0] preserve
[0,0] despite K having infinite Tor amplitude. Taking the non-flat factor Z/2 instead
creates negative Tor cohomology, confirming that the exactness condition is essential.
The scheme and coefficient universes follow the recorded small-etale declarations;
there is no extra equality between site-object and site-morphism universes.

Searches made for an existing statement and its auxiliary vocabulary:

- msearch.py LeanFinder: "Tensoring a bounded constructible complex of etale module
  sheaves with a flat constructible sheaf commutes with cohomology and preserves bounded
  constructibility" returned eight hits about LightCondensed monoidal structures and
  internal projectivity; none gives this theorem on the ordinary small-etale site.
- msearch.py Loogle: `"constructible", "tensor"` returned zero hits.
- msearch.py grep: `constructib.*tensor|tensor.*constructib|flat.*homology` returned
  zero Mathlib hits.
- msearch.py LeanSearch: "Cohomology of derived tensor with a flat sheaf equals the
  tensor of cohomology sheaves" returned eight results, including
  `Module.Flat.lTensor_exact`, `Module.Flat.rTensor_exact` and their short-complex
  versions. These are algebraic-module exactness, not the etale derived statement.
- rg in WeilConjectures and lean/Sheaf for flat/constructible tensor and tensor/homology
  combinations found bounded-flat-model and Tor-amplitude results, plus the
  locally-constant finite-type theorem. Those have different assumptions or conclusions.
  `torAmplitudeIn_singleFunctor_obj_of_flat` only gives the factor's Tor amplitude;
  it does not give this natural cohomology comparison or this global finite-value
  constructibility conclusion for arbitrary schemes.
- The exact node id occurs in neither WeilConjectures nor the upstream-name index.
  All four proposed full declaration names were searched in Mathlib, WeilConjectures
  and lean/Sheaf with no collision.
- The recorded upstream EtaleSheaves and DerivedCategories modules are absent in the
  old local source checkout; their current complete source was read using
  `scompile.py --source`. Current bounded-constructible and flatness module sources
  were also read through that command to confirm the side-project bindings.

There is no statement correction, no new independent notion, and no disputed mathematical
statement. Only the item's `lean` and the flatness dependency's `lean` records change.
The previous worker's stage-1 stale-assignment message does not indicate a landed stage-2
statement: the current item has no `lean` record or `reviewed_lean` before this delivery.

## Dependency modules

`def-pc-flat-sheaf-modules`: exact existing-interface repair under §1(B), with no new
module. The old primary declaration accepts `SheafOfModules` over a ring sheaf; this
item's recorded derived and constructibility categories require `Sheaf (ModuleCat Λ)`.
Its body is exactly `CategoryTheory.exactFunctor _ _ (siteSheafTensorRight F)`. Its
public import already exposes `CategoryTheory.exactFunctor`, so the repaired record
retains `SheafOfModules.IsFlatOnSite` as primary and lists that underlying exactness
predicate as an additional existing declaration. The new consumer specializes it to the
canonical `tensorRight L` on `Sheaf (ModuleCat Λ)`, i.e. the same sheafified sectionwise
tensor used by the recorded `derivedTensor`. This states exactly the dependency node's
flatness condition for this encoding, without duplicating flatness, replacing the
independent-universe interface, or assuming any unproved equivalence. Existing users
of `IsFlatOnSite` remain supported. Its `lean.note` explains this domain mismatch and
the added existing interface; all other dependency fields remain unchanged.

## Second reading by Q48

Independent maintainer second reading, 2026-10-18, of immutable delivery
`e56736d77ea06414b08bbe876826fc63a3b6d5e4`. This section replaces the delivered
placeholder; the maintainer did not author the module.

I read the packet, item, all six statement dependencies, source places, complete delivered
module and report, and the definitions actually used. The Lean states the item correctly:

- `(X : Scheme.{u})` is arbitrary. `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`
  is the finite commutative coefficient ring in the recorded small-etale convention.
  There is no Noetherian, quasi-compactness, separation or nonzero assumption.
- `Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` is the accepted module-sheaf
  encoding of def-weil-pbc-etale-sheaves. `flatConstructibleEtaleSheafProperty` combines
  precisely `Scheme.IsConstructibleEtaleModuleSheaf` with exactness of the canonical
  sheaf tensorRight. I read IsFlatOnSite and Mathlib exactFunctor: the latter means
  preservation of finite limits and colimits. The dependency's existing-interface
  repair retains IsFlatOnSite and exposes its underlying exactness predicate; it does
  not assert an unconstructed equivalence of the two module-sheaf encodings.
- `BoundedConstructibleDerivedCategory Λ X` is exactly the full subcategory defined
  by constructible cohomology and vanishing outside some integer interval. K has no
  finite Tor-amplitude hypothesis. `singleFunctor _ 0` places L in degree zero.
- Unfolding the left bifunctor gives H^i(K tensor^L L[0]); unfolding the right gives
  H^i(K) tensor L, with that factor order. I checked flip and both whiskering
  definitions. `Nonempty` here encloses a genuine natural isomorphism of functors
  into a functor category, so it asserts naturality in both variables, including all
  morphisms in the full subcategories; it is not merely objectwise isomorphism.
- The remaining conjuncts explicitly assert constructibility of every output
  cohomology sheaf, membership of the displayed tensor in the same D^b_c, and
  preservation of every a <= b interval using IsZero in every integer degree.

Sources read: Stacks etale-cohomology.tex, lemma-tensor-product-constructible (095I,
line 11991), lemma-tensor-c (0961, line 13688), and
lemma-tensor-product-locally-constant (095D, line 10071); homology.tex,
lemma-exact-functor (010N, line 1545); sites-modules.tex, definition-flat (03ER(3),
line 4243); sites-cohomology.tex, definition-K-flat (line 2999),
lemma-K-flat-resolution (06YS, line 3207), and definition-derived-tor (06YU,
line 3300) with its preceding construction. The finite ring is Noetherian. The
unchanged lower bound is justified by exact tensor with a flat degree-zero factor,
not by pretending 0961 alone supplies boundedness below. Global finite constructible
stratifications are the project's recorded notion, retained throughout.

The five proof steps in the declaration docstring match the node: exact tensor commutes
with cohomology and makes L[0] K-flat; flat-term K-flat resolutions compute the ordinary
derived tensor and the comparison descends naturally; actual fibre-product strata refine
both finite partitions; module pullback commutes with tensor and finite locally constant
factors stay finite locally constant; zero tensor gives precisely the unchanged interval.
I read the cited proof-dependency statements, including the refinement's scheme
fibre-product assertion, inverse-image constant-ring comparison, tensor comparison,
and the separate local-constancy and finiteness assertions. No proof is imported from
inside another node's argument. For finite Λ, finite generation in the finite-sheaf
API gives finite module values on the trivializations.

Edge cases: empty X (including empty stratifications), the zero ring, L=0, K=0,
a=b, negative and zero cohomological degrees, and arbitrary larger intervals are covered.
On a point, Λ=Z/4, L=Λ, K=Z/2[0] checks that infinite Tor amplitude of K is allowed.
The non-flat factor Z/2 instead produces negative Tor, confirming why flatness is needed.
All universes are bound; u+1 is the dependency convention, not an extra identification
of the site's object and morphism universes.

Independent searches used rg on upstream WeilConjectures, Mathlib homology modules and
the group's Sheaf algebraic-geometry tree for tensor/homology/constructibility and the
new names. Nearby constructibleFiniteTor and generic constructible-homology results
have different assumptions or predicates. Loogle query `"homology", "tensor"` returned
three group-homology declarations, none matching. The worker report also records
LeanSearch, LeanFinder, Loogle and grep searches. No duplicate notion was found: the
three auxiliaries are actual compositions or conjunctions of existing definitions.

I checked all four declared names, source/blueprint docstrings, all five proof steps,
100-character line widths, explicit variables and the exact theorem signature.
`lean.statement` equals the signature verbatim. All three definitions have actual data;
the only new theorem has exactly `by sorry`. The item and dependency deltas are confined
to lean records. No new DAG node or statement_change is required. The shared route-pivot
dropped list contains none of the item's statement or proof dependencies; there is no
item repair note at the specified ref and no enhanced/infinity/model or pro-etale route.

Compiler reproduction: ran
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q48 lem-fd-flat-constructible-tensor`
with the immutable snapshot's FlatConstructibleTensor.lean absolute path. Exit code 0:
sandbox Sheaf/Stage2/Sandbox0.lean passed in 7.3 s and library
Sheaf/AlgebraicGeometry/FlatConstructibleTensor.lean passed in 6.7 s, with no Lean
diagnostics. The installed wrapper currently dispatches its private side overlay and
library confirmation on the server; no direct ssh or global build was run. Current
bounded-constructible, constructible-module, derived-category and MonoidalParts sources
were also checked through scompile.py --source where local sources were absent or stale.

Finding and repair: H11 (and the substantive report requirement of H1): the original
second-reading section said no reading had occurred. This complete independent reading
replaces it. The report also lacked explicit per-file compiler results; reproduction
is now recorded above. No Lean, node or mathematical correction was needed.
