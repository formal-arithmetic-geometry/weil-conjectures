## Worker report

The complete statement already exists upstream as a bundle of declarations. This delivery
records `existing: true`; it introduces no module, definition, theorem, or sorry. The primary
entry is `AlgebraicGeometry.Etale.isBaseChangeIso_of_isFinite` in
`WeilConjectures.SixFunctors.Finite.BaseChange` (line 359). Its public imports expose every
other declaration listed in `lean.declarations`. The node is unchanged outside `lean`.
No repair note exists at `coord/repair-notes/sk-lem-pbc-finite.json`.

Clause-by-clause correspondence:

- Schemes V, W and finite u: the existing declarations bind `{X Y : Scheme.{u}}`,
  `(f : X ⟶ Y)`, and `[IsFinite f]`. This is the finite convention of `sk-def-conv`,
  using Mathlib's affine morphism with finite ring maps on affine opens.
- Abelian F: specialize the coefficient category A to `AddCommGrpCat.{u + 1}` and take
  `F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}`. This is precisely the recorded
  abelian-sheaf encoding, with no condition on F.
- Geometric point: `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]` and
  `(y : Spec (.of Ω) ⟶ Y)`. Algebraic closedness is retained, including in positive
  characteristic; there is no replacement by separable closedness.
- Displayed stalk isomorphism: `Etale.stalkIsoPi AddCommGrpCat.{u + 1} f y F`, from
  `WeilConjectures.SixFunctors.Finite.Stalk`, has source
  `(Scheme.pointSmallEtale y).sheafFiber.obj ((Etale.lowerStar _ f).obj F)` and target
  `∏ᶜ fun t : f.GeometricFiber y => (Scheme.pointSmallEtale t.1).sheafFiber.obj F`.
  The source and each target stalk are definitionally the recorded `pointedEtaleStalk`;
  the consumer check explicitly type-ascribes that form. `stalkIsoPi.hom` is the product
  lift of `Etale.stalkRestrict`, so this is the actual restriction-of-germs map.
  `Etale.lowerStarSheafFiberIsoPi` packages its naturality in F.
- Exactly the indexing set: `Scheme.Hom.GeometricFiber f y`, in
  `WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber`, abbreviates
  `{x : Spec (.of Ω) ⟶ X // x ≫ f = y}`. This fixes Ω, with no quotient by automorphisms
  and no substitution of topological points. Its `GeometricFiber.finite` instance
  proves the finite-product clause.
- Exact direct image: `Etale.preservesFiniteLimits_lowerStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` gives left exactness;
  `Etale.preservesFiniteColimits_lowerStar_of_isFinite` and
  `Etale.preservesHomology_lowerStar_of_isFinite` in
  `WeilConjectures.SixFunctors.Finite.Exact` give exactness for the same abelian category.
- Arbitrary base change: `Etale.isIso_baseChangeMap_of_isFinite` in
  `WeilConjectures.SixFunctors.Finite.BaseChange` takes an arbitrary
  `sq : IsPullback g' f' f g` and proves
  `IsIso (Etale.baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq)`.
  `Etale.isBaseChangeIsoSheaf_of_isFinite` packages all such squares. This uses the
  canonical underived mate of `WeilConjectures.SixFunctors.BaseChange.Square`, not an
  unspecified isomorphism of its endpoints. A chosen cartesian square supplies such a
  pullback square through its chosen isomorphism; conversely every pullback square has
  the canonical pullback identification. No preferred presentation restricts g.
- Every constant commutative coefficient ring: take `Λ : Type (u + 1) [CommRing Λ]`
  and specialize A to `ModuleCat.{u + 1} Λ`. This is the module encoding recorded by
  `def-weil-pbc-derived-categories`, whose definition is in
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients` and documented in
  `WeilConjectures.AlgebraicGeometry.DerivedCategories` (read with `scompile.py --source`).
  There is no finite, torsion, characteristic, or invertibility assumption on Λ.
- Every bounded below K and the specified derived exchange: the primary existing
  instance gives `Etale.IsBaseChangeIso (ModuleCat.{u + 1} Λ) f`. Its `isIso` field,
  applied to `g' f' g sq`, is exactly
  `IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq)`.
  Taking its component at an arbitrary
  `K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))`
  gives the requested isomorphism in the bounded below category on Y'. The endpoints
  are `Rf_* ⋙ Dg^*` and `Dg'^* ⋙ Rf'_*`. The map is exactly the recorded declaration
  of `sk-def-exchange` in `WeilConjectures.SixFunctors.BaseChange.Derived`, whose
  resolution normalization is `derivedBaseChangeMapPlus_fac_app`.

Dependency declarations read: `IsFinite` (the finite clause of `sk-def-conv`),
`CategoryTheory.Sheaf`, `IsAlgClosed`, `pointedEtaleStalk` and its diagram,
`Etale.lowerStar` and `rightDerivedLowerStarPlus`, `Scheme.Hom.GeometricFiber`,
`Etale.derivedBaseChangeMapPlus`, `Etale.baseChangeMap`, `Etale.squareUpperStarIso`,
and `Etale.DerivedCategoryModule` / `DerivedCategory.Plus`. Their modules and their
uses are identified above. The new standalone stalk interface is used by definitional
equality, verified in the consumer, rather than duplicated. No dependency repair is needed.

Sources checked: the current blueprint unit
`literature/blueprint/main-20261015/blueprint/sec-proper-base-change/`
`sk-lem-pbc-finite/_section.md`; Stacks `etale-cohomology.tex`, Tag 03QP,
`proposition-finite-higher-direct-image-zero` (lines 8244 onward), and Tag 0959,
`lemma-finite-pushforward-commutes-with-base-change` (lines 8291 onward). The upstream
stalk, exactness, and exchange docstrings and full signatures implement those clauses.
The blueprint uses products; the finite abelian direct sum in 03QP is canonically the
same finite product, including the empty case.

Edge cases checked: an empty geometric fibre gives the empty product, the zero abelian
object; an empty source gives zero direct image; an empty target has no geometric points.
The identity finite map gives a singleton fibre and identity base change. Nonreduced and
inseparable finite fibres remain included because Ω is algebraically closed and the index
is the set of Ω-valued lifts. Zero sheaves, zero coefficient rings, arbitrary characteristic,
arbitrary base changes (including identities and geometric points), and unbounded-above
bounded-below complexes are included. Neither surjectivity nor etaleness of f is required.
Scheme objects live in the conventional universe u+1 with morphisms in u; coefficients
and their module carriers use u+1. No universe equality or new size restriction is imposed.

Searches made (all through the prescribed search wrapper or read-only source searches):

- LeanFinder: “For a finite morphism of schemes etale pushforward has finite product
  stalks is exact and commutes with arbitrary base change including bounded below derived
  module exchange”: eight Mathlib hits, headed by stability of `IsFinite` under base
  change; no complete sheaf theorem.
- Loogle: `"lowerStar", "isFinite"`: zero hits.
- LeanSearch: “Finite morphism etale sheaf pushforward exact stalk product arbitrary
  base change”: eight hits, including topological stalk pushforward and module-sheaf
  pushforward data; no complete theorem.
- Mathlib grep: `isIso.*[Ff]inite|[Ff]inite.*lowerStar|[Ff]inite.*baseChangeMap`, restricted
  to AlgebraicGeometry: four scheme-geometry hits; no complete theorem.
- Upstream grep: `sk-lem-pbc-finite`, `isIso_piLift_stalkRestrict`,
  `preservesFiniteColimits_lowerStar`, `isIso_baseChangeMap_of_isFinite`, and inspection
  of `SixFunctors/Finite/*.lean`: found every required declaration in Finite.Stalk,
  Finite.Exact, and Finite.BaseChange. The blueprint id itself has no exact upstream hit.
- Project grep with the same named declarations found consumers of the upstream finite
  results, but no reason to duplicate them. `dag/lean_names_upstream.json` also lists
  the stalk, exactness, and exchange declarations against the corresponding older nodes.

Validation: `scompile.py Q02 sk-lem-pbc-finite checks/FiniteConsumer.lean` passed both
sandbox and library checks (3.3 s / 3.0 s), with no errors or warnings. The scratch consumer
has `autoImplicit false`, explicitly binds its universes and variables, type-checks the
pointedEtaleStalk product isomorphism, synthesizes finite limits, finite colimits and
homology preservation for the abelian direct image, checks the underived mate, synthesizes
module exactness, and applies `IsBaseChangeIso.isIso` to the arbitrary square before
checking its component at arbitrary bounded-below K. The first attempted direct instance
search for that component did not unfold the class field; explicitly applying its `isIso`
projection fixes the consumer, with no interface or mathematical change. The scratch
consumer is validation only and is not a delivered Lean module.

No statement is disputed; no statement correction, new node, or dependency module is needed.

## Second reading by Q02

A separate final pass reopened the node and the existing source declarations. It checked
all six parts: abelian finite stalk isomorphism with exactly the Ω-valued lifts, finiteness,
exactness, arbitrary underived base change, arbitrary commutative coefficients, and the
specified bounded below derived exchange on every K. Each is recorded above; merely
recording the primary derived-exchange instance would omit the other clauses, so the
record explicitly lists their existing declarations as a bundle. The restrictions of the
general coefficient-category API are infrastructure instances for both AddCommGrpCat and
ModuleCat, rather than additional geometric or ring hypotheses. The standalone
`pointedEtaleStalk` agrees definitionally with the upstream `sheafFiber` in the consumer.
No mathematical mismatch was found. This is the worker's second pass; no second agent was
started, as instructed. The maintainer supplies the independent delivery review.
