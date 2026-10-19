## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleHorizontalSupportMate` states
`AlgebraicGeometry.Etale.etaleHorizontalSupportMate` with proof `sorry`, together with the
three canonical interfaces used by that statement:
`etaleCanonicalCompactSupportComparison`, `etaleHorizontalSupportMateDelta`, and
`etaleHorizontalSupportBaseChangeIso`.  The implementation uses the published
six-functor encoding of the node's ordinary constant-
`A` small-etale derived categories.  Thus `DerivedCategoryModule A T` is
`D(T_et,A)`, `rightDerivedLowerShriek ... f` is `F_f = Rf_!`,
`etaleLowerShriek ... v` is the etale sum-extension `S_v`,
`derivedEtaleLowerShriekUpperStarAdjunction ... v` supplies the counit
`epsilon_v`, and `etaleHorizontalSupportBaseChangeIso` is the specified
compact-support exchange `C_{f,u}` as an isomorphism (the statement uses its `inv`).  The comparison
`etaleCanonicalCompactSupportComparison` is the normalized `d_a`; `Delta` is the
composition in the node, expanded through the specified compact-support
composition and exchange isomorphisms.

### Statement rendering

* `A` is rendered by `(A : Type (u + 1)) [CommRing A] [Finite A]`.
* The four schemes in the Cartesian square are `{X X' Y Y' : Scheme.{u}}`, and
  `sq : IsPullback v' f' f v` renders the Cartesian-square hypothesis.
* `[IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']`
  renders the common Noetherian hypothesis.
* The four arrows are `{f : X ⟶ Y} {f' : X' ⟶ Y'}
  {v : Y' ⟶ Y} {v' : X' ⟶ X}`.  Separatedness is rendered by
  `[IsSeparated f] [IsSeparated f'] [IsSeparated v] [IsSeparated v']`.
* Etaleness of the horizontal maps is `[Etale v] [Etale v']`; finite type is
  represented by `[LocallyOfFiniteType f] [LocallyOfFiniteType f']` and the
  corresponding hypotheses on `v,v'`, with quasi-compactness supplied for all
  four arrows.  Together these are the finite-type assumptions in the node's
  scheme-theoretic encoding.
* The compactification requirement for `f,f',v,v'` and for both equal composites
  is rendered by the six `HasCompactification` binders.  The composite
  quasi-compactness binders are supplied as required by the existing unbounded
  compact-support API.
* `N : EtaleCompactSupportNormalization A` records the node's specified
  proper-support comparison normalization; no arbitrary isomorphism is chosen.
* `∀ (M : DerivedCategoryModule A X), ...` quantifies every unbounded derived
  input.  The left side is
  `Delta.inv.app (v'^* M) ≫ F_f.map (epsilon_{v',M})`.  The right side is
  `S_v.map (C_{f,v}^{-1}.app M) ≫ epsilon_{v,F_f M}`.  Equality is equality of
  morphisms in `D(Y_et,A)`, exactly the node's mate equation.

### Dependency declarations used

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme
  morphisms.
* `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` (the project uses the
  existing `IsNoetherian` scheme classes).
* `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` and derived-category notation.
* `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
* `WeilConjectures.Compactification.Refinement`:
  `AlgebraicGeometry.Compactification.Refinement` and compactification API.
* `WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap`:
  `AlgebraicGeometry.Etale.etaleLowerShriek`.
* `Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact`:
  `AlgebraicGeometry.Etale.quasifiniteCompactSupportExact` (normalization source).
* `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`:
  `derivedEtaleLowerShriekUpperStarAdjunction` and the ambient adjunction
  locality interface.
* `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`:
  `unboundedEtaleLowerShriekCompIso`, `unboundedEtaleLowerShriekCongr`,
  `unboundedEtaleCompactSupportBaseChange`, and their specified composition,
  unit, associativity, and exchange normalizations.
* `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `IsPullback`/pullback square interface.

### Edge cases checked

The statement quantifies arbitrary unbounded `M`, including `0`, shifts, and
objects with no boundedness or constructibility restriction.  The square permits
identity arrows (then the composition and base-change isomorphisms reduce to the
identity normalizations), open etale arrows (the mate specializes to the open
extension-by-zero calculation), split finite-etale covers, and empty schemes.
No nonemptiness, connectedness, characteristic, or degree hypothesis is added.
The coefficient universe is tied to the scheme universe as `A : Type (u+1)` and
`ModuleCat.{u+1} A`, so the statement does not exclude the finite zero ring.

### Searches

The node's recorded searches were rechecked before retaining the module:

* `msearch.py ... leanfinder "compact support base change along etale horizontal maps equals partial adjunction mate ..."`: only generic sheaf adjunction and pullback hits; no matching geometric statement.
* `msearch.py ... loogle "CategoryTheory.mateEquiv"`: generic mate lemmas only.
* `msearch.py ... grep "etale.*(comp|mate)|shriek.*(exchange)|compactSupport" CategoryTheory`: no matching declaration.
* `msearch.py ... grep "shriek|properSupport|compactlySupported|compactSupport" AlgebraicGeometry`: no matching geometric declaration.
* `rg` over `WeilConjectures/` and project `lean/Sheaf/` found no declaration with the
  item id or the full horizontal-support mate statement; the only relevant APIs
  are the dependency declarations listed above.

The file compiles cleanly with the required `scompile.py` wrapper; the only
postponed proof is the theorem's expected `sorry`.

## Second reading by Q56

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
