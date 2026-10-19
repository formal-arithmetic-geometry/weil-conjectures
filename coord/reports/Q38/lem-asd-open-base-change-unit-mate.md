## Worker report

Existing upstream declarations cover the node. No Lean module is added and only the
item's `lean` field changes. The existing attachment was incomplete (no module,
primary declaration, signature, author, date or existing flag); this delivery supplies
the complete stage-2 record without changing the mathematical statement or dependencies.
No repair-note file for this item was present.

The source is
`WeilConjectures/SixFunctors/Etale/Derived/OpenImmersionLowerShriekProjectionBaseChange.lean`.
Read its setup and declarations at lines 78–155, and the definitions in
`OpenImmersionLowerShriekBaseChange.lean` and `LowerShriek/OpenImmersion/BaseChangeSquare.lean`.
The primary declaration is
`AlgebraicGeometry.Etale.unit_map_derivedOpenImmersionLowerShriekBaseChangeIso`.
The recorded supporting declarations are
`AlgebraicGeometry.Etale.derivedOpenImmersionSquareMap_app` and
`AlgebraicGeometry.Etale.mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso_mate`.
All three are in the same recorded upstream module. The signature in `lean.statement`
is extracted verbatim from the source, from `lemma` through the expression preceding `:=`.
The inherited section parameters are explained below; the source uses scoped notation.

Hypothesis and clause correspondence:

- The commutative ring C is supplied by specialization of the coefficient category
  `A` to `ModuleCat.{u + 1} C`, with `C : Type (u + 1)` and `[CommRing C]`.
  The general theorem's Abelian, Grothendieck, sheafification, closed symmetric
  monoidal and functorial flat-resolution structures are the standard structures
  of this module category; they impose no condition on C beyond commutativity.
- The schemes are `{U' U Z' Z : Scheme.{u}}`; the source's `g'`, `g''` are the
  node's `u`, `a`, respectively. Its `j` and `j'` have the same meanings.
  The source assumes `[IsOpenImmersion j] [IsOpenImmersion j']` and
  `(hsq : IsPullback g' j' j g'')`. For the node's chosen square take
  `U' = pullback j a`, `g' = pullback.fst j a`, `j' = pullback.snd j a`,
  and `hsq = IsPullback.of_hasPullback j a`. The second open-immersion instance
  follows by base change; it is not a new geometric hypothesis. Conversely the
  general Cartesian-square statement applies to any representative of this square.
- `DerivedCategory (Sheaf T.smallEtaleTopology A)`, after this specialization,
  is exactly `DerivedCategoryModule C T`, the ordinary unbounded constant-module
  derived category of the recorded dependency. Its objects have no extra property.
  The coefficient and site universes are the published convention of that dependency.
- The node's termwise exact inverse image is `D((h)^*[A])`, i.e.
  `(upperStar A h).mapDerivedCategory`. The primary theorem uses `L((h)^*[A])`
  for g' and g'', identified canonically with D by
  `leftDerivedUpperStarIsoMapDerivedCategory A h`. The source expressly makes
  this identification. The third recorded declaration states the same equation
  directly with D at all four inverse images, so termwise descent is available
  without choosing any substitute functor.
- `j_!` and `j'_!` on derived categories are `D((j)_!open[A])` and
  `D((j')_!open[A])`. The functor `openImmersionLowerShriek` is the existing
  extension by zero, not a replacement defined here.
- The units are `(derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit`
  and its j' analogue. These are the adjunctions descended from the sheaf
  extension-by-zero adjunction, as required.
- B is `(derivedOpenImmersionLowerShriekBaseChangeIso A hsq).hom`. In
  `OpenImmersionLowerShriekBaseChange.lean` it is defined by conjugating the
  termwise map with `leftDerivedUpperStarIsoMapDerivedCategory`; its termwise
  version is `mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso`.
  That definition applies `mapDerivedCategoryNatIso` to the isomorphism of
  `openImmersionLowerShriekBaseChangeMap`. The sheaf map is explicitly the
  inverse conjugate of the exchange for the two composite adjunctions, exactly
  the mate specified by `def-weil-pbc-etale-shriek-base-change-map`.
  For open immersions the etale and open-extension presentations are the
  canonical left adjoint to the same inverse image; the comparison uses their
  adjunctions, rather than an arbitrary isomorphism. Its invertibility is built
  from `isIso_openImmersionLowerShriekBaseChangeMap A hsq`.
- c is `(derivedOpenImmersionSquareMap A hsq.toCommSq).app X`. The second
  recorded theorem identifies this with `(derivedSquareUpperStarIso A sq).inv`,
  with the exactness comparisons for j and j'. The composition comparison
  `leftDerivedUpperStarComp A g₁ g₂` has direction
  `L((g₁ ≫ g₂)^*) ≅ L(g₂^*) ⋙ L(g₁^*)`, the node's gamma direction.
  The square inverse therefore goes from `u^* j^*` to `j'^* a^*`, namely
  gamma(a,j') after gamma(j,u) inverse. Equivalently the termwise declaration
  uses `mapDerivedCategorySquareIso (openImmersionSquareIso A sq)`, where
  `openImmersionSquareIso` is defined as `(upperStarComp A g' j).symm`
  followed by `upperStarComp A j' g'' (g' ≫ j) sq.w`.
- With E represented by the unrestricted binder
  `(K : DerivedCategory (Sheaf U.smallEtaleTopology A))`, the left side is
  `unit'.app (u^*.obj K) ≫ j'^*.map (B.app K)` and the right side is
  `u^*.map (unit.app K) ≫ c.app (j_!.obj K)`. Lean's composition order is
  left-to-right, so these are precisely the two composites displayed in the node.
  Their common source is u^* E and common target is j'^* a^* j_! E.
- Units and comparisons are natural transformations and the maps are functor
  maps; both composites are consequently natural in K. The component identity
  for every K is equality of those natural transformations by extensionality.
- There is no boundedness, constructibility, coefficient finiteness, or flatness
  assumption on the scheme morphism a. The coefficient is ModuleCat C, never a
  variable structure sheaf. No assertion about monoidal compatibility is added.

Dependency declarations read and used to interpret the existing statement:

- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` and its imported
  `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`:
  `AlgebraicGeometry.Etale.DerivedCategoryModule` (the ordinary `DerivedCategory`).
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`:
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`.
- `Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal`:
  `AlgebraicGeometry.Etale.canonicalDerivedPullbackCompositionMonoidal`, whose
  gamma is `leftDerivedUpperStarComp` as used above.
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`:
  `AlgebraicGeometry.Etale.etaleLowerShriekBaseChangeMap`.
- `Sheaf.AlgebraicGeometry.OpenImmersionExtensionZeroBaseChange`:
  `AlgebraicGeometry.Etale.openImmersionExtensionZero_exact_baseChange`.
  This record states the abelian-sheaf specialization; the imported upstream
  `isIso_openImmersionLowerShriekBaseChangeMap` already supplies the module-valued
  instance needed here, so no dependency-interface repair is required.

The three missing local upstream source files in this list were read through
`scompile.py --source`, as authorized, rather than treating stale local paths as blockers.

Edge cases checked by reading the unrestricted signatures and the actual constructions:
empty U or Z', zero E, zero coefficient ring, identity open immersion, identity a,
and nonflat a. None is excluded; all maps remain defined and the mate identity is
unchanged. No nonemptiness, nonzero, boundedness, or finite-dimensional condition occurs.
The source permits arbitrary unbounded K, including complexes unbounded in both directions.

Searches (2026-10-17 UTC; raw service results are in sandbox searches.jsonl):

- msearch LeanFinder: "Derived open immersion base change unit is the mate of the
  pullback composition square map" returned eight general pullback/adjunction hits,
  including `Scheme.Modules.restrictAdjunction_unit_app_app`; none is this theorem.
- msearch Loogle: `CategoryTheory.unit_mateEquiv, CategoryTheory.Adjunction.unit`
  returned `CategoryTheory.unit_mateEquiv`; it is the abstract mate identity and
  does not identify the concrete derived square comparison.
- msearch LeanSearch: "extension by zero derived base change adjunction unit mate"
  returned eight generic adjunction results, including `Adjunction.derived_unit`
  and `unit_mateEquiv`; no concrete etale-open theorem.
- msearch Mathlib grep in CategoryTheory:
  `mateEquiv.*unit|unit.*mateEquiv|unit.*baseChange|baseChange.*unit` returned ten
  mate/monoidal/bicategorical hits; none states the concrete comparison.
- Source `rg` for `unit_map_derivedOpenImmersionLowerShriekBaseChangeIso` and
  `mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso_mate` found the exact
  upstream declarations in the source module recorded above. Source search for
  the node id had no hits. The inspected source is the exact source place of the node.
- `rg` of `lean/Sheaf` for `derivedOpenImmersionSquareMap` and the primary
  declaration had no hits. A broader base-change/mate search found other
  projection and exchange statements, not a second statement of this identity.
- The upstream names index search had no hit for these names; direct source reading
  resolves them. The node's existing audit already records the first two as closed.

No new proofs, definitions, nodes, statement corrections or disputed statements.
An existing-only delivery has no new file to compile under brief-stage2 §1;
the required delivery dry run validates this binding through the server preflight.

## Second reading by Q38

Author self-check, not an independent review: the dispatcher expressly prohibits
starting other agents; the maintainer supplies the independent delivery review.
Reopened the node, source declarations and the saved record. Checked the ring
specialization, all four arrows and their orientation, the Cartesian-square argument,
both units, the sheaf mate underlying B, and the gamma square identification above.
In particular the primary theorem mixes L and D, while the node says termwise;
this is covered by its stipulated exactness identifications and by the separately
recorded all-D theorem. The second recorded declaration supplies the gamma
identification, so merely citing the abstract mate lemma is avoided. Naturality
is contained in the actual natural transformations. No clause is missing and no
extra geometric or coefficient condition is introduced. The sole change is completing
`lean`; the existing attachment, status, source, statement and dependency lists are preserved.
