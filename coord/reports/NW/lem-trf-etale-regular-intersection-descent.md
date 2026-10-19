## Worker report

The module `Sheaf.TraceFormula.EtaleRegularIntersectionDescent` defines `SchemeOver`, the
finite pullback construction `intersectionData`, its carrier and ambient map
`intersectionScheme`/`intersectionMap`, and the stalk-spectrum base change
`localIntersection`/`localIntersectionProjection`.  The theorem
`AlgebraicGeometry.etale_regular_intersection_descent` states the four-step étale descent
argument and has a `sorry` proof as required at stage 2.

The theorem binds a locally Noetherian scheme `X`, a natural number `n`, a `Fin n` family
of schemes `D`, maps `i j : D j ⟶ X`, and the closed-immersion hypothesis
`hclosed : ∀ j, IsClosedImmersion (i j)`.  Its local hypothesis quantifies every point
`x : X` and every `J : Finset (Fin n)`, and supplies `W`, `v : W ⟶ X`, and `w : W` with
`Etale v` and `v w = x`.  The local object is exactly the pullback of
`intersectionMap D i J` along `W.fromSpecStalk w ≫ v`; it is locally Noetherian, all its
stalks are `IsRegularLocalRing`, and each irreducible component has `Order.coheight` of
its projection point equal to `J.card`.  The conclusion quantifies every finite `J`,
asserting local Noetherianity, regularity of every stalk, and the same coheight equality
for each irreducible component of the intersection in `X`.  `Order.coheight` is the
Mathlib chain supremum for the specialization order, so it renders the stated
codimension definition.

The finite intersection handles `J = ∅` by returning `X`; the recursive branch removes
`J.min' h`, and termination is discharged by `Finset.card_erase_lt_of_mem`.  The case
`n = 0` therefore has only the empty intersection.  Empty local intersections have no
irreducible-component witnesses, so the component clause is vacuous.

The declarations used are Mathlib's `AlgebraicGeometry.Etale`,
`AlgebraicGeometry.IsClosedImmersion`, `AlgebraicGeometry.IsLocallyNoetherian`,
`CategoryTheory.Limits.pullback`, `AlgebraicGeometry.IsGenericPoint`/the scheme
specialization order, `IsRegularLocalRing`, `irreducibleComponents`, and
`Order.coheight`.  The module imports only Mathlib modules supplying these declarations.

Searches performed before writing: `msearch.py ... leanfinder` for étale descent of
regular intersections (no match); `msearch.py ... loogle` for `IsRegularLocalRing`,
`Etale`, and `KrullDimension` (no matching theorem); `msearch.py ... grep` for
`regular.*[Ee]tale|[Ee]tale.*regular|dimension.*[Ee]tale` in Mathlib algebraic geometry
(no descent theorem); `rg` over `WeilConjectures` and project `lean/Sheaf` for regular
scheme, codimension, and étale intersection declarations (no exact statement).  The
existing node records were read for `pqf-def-locnoeth`, `def-weil-etale-morphism`,
`def-pc-fibre-product`, `def-weil-closed-immersion`, `def-weil-irreducible-components`,
and `def-weil-regular-scheme`; their Mathlib declarations are used directly.

## Statement corrected

The returned split omitted the Lean module and had an unusable stale split report.  The
node statement is made explicit enough to type: `n`, the `Fin n` family, every `Finset`
(including the empty set), the iterated pullback construction, stalk-spectrum base
change, stalkwise regularity, and chain codimension are all introduced.  The source is
Stacks Étale Morphisms Tags 025N, 039S, and 02GO and the blueprint's local
strict-normal-crossings criterion.  The sole citer is
`lem-trf-permissible-boundary-preservation`; its use remains valid because it applies
the theorem to a finite family of boundary components and explicitly includes the empty
intersection.  No citer is edited.

## Second reading by NW

I reread the source tags and checked the statement clause by clause.  The empty family
has intersection `X`; repeated or coincident closed immersions do not satisfy the local
expected-codimension hypothesis unless the source conclusion is valid; and an empty
intersection contributes no irreducible components.  The pullback is formed over `X`
using the supplied ambient maps, and `v w = x` records that `w` lies over the chosen
point.  The theorem's four proof steps in its docstring match the source route: affine
ideal-sum description and base change, flat local regularity descent, generic-point
étale dimension comparison, and translation from local dimension to chain codimension.

## New nodes

None.  All notions needed by the typed statement have existing Mathlib or DAG
interfaces.

## Dependency modules

None.  The recorded dependency declarations are usable as Mathlib declarations or
existing DAG interfaces.
