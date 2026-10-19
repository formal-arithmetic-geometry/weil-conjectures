## Worker report

The node is already stated by the source-library declaration
`AlgebraicGeometry.ProEtale.isIso_openImmersionLowerShriekProjectionMap_app_app` in
`WeilConjectures.SixFunctors.ProEtale.LowerShriek.OpenImmersion.Projection`.
No new module is needed. The declaration is an `IsIso` instance for the component of
`openImmersionLowerShriekProjectionMap`, the adjunction projection map for
`openImmersionLowerShriek ⊣ upperStar` with the strong monoidal pullback comparison.
For `A = AddCommGrp` (abelian sheaves), take the source declaration's `K` to be the
node's `M` and its `M` to be the node's `L`; the symmetric tensor identifies
`M ⊗ j^*L` and `j^*L ⊗ M`, and `j_!M ⊗ L` and `L ⊗ j_!M`. Under these canonical
symmetries the source projection map is exactly the node's unit-adjoint canonical map.

The node's hypotheses and clauses are rendered as follows:

* `j : U → X` open immersion is the section variable `j` with `[IsOpenImmersion j]`.
* `j^{Ab}_! ⊣ j^*_{Ab}` is the source adjunction
  `ProEtale.openImmersionLowerShriekUpperStarAdjunction A j`.
* `L` and `M` are the two sheaf objects represented by the source components
  `(K : Sheaf (Scheme.ProEt.topology U) A)` and
  `(M : Sheaf (Scheme.ProEt.topology X) A)` after the variable swap above.
* The displayed canonical projection map is the component
  `((openImmersionLowerShriekProjectionMap A j).app K).app M`; its transpose is the
  unit map followed by the strong monoidal pullback comparison, by
  `CategoryTheory.Adjunction.projectionMapTranspose` and the definition of
  `openImmersionLowerShriekProjectionMap`.
* The conclusion that this map is an isomorphism is exactly the source instance
  `isIso_openImmersionLowerShriekProjectionMap_app_app`.
* The tensor is the recorded sheaf tensor structure from `sk-def-sfb-sheaf-tensor`.

Dependency declarations used are the source lower-shriek/upper-star adjunction and
projection-map declarations in the module above, together with the recorded sheaf
tensor declaration `CategoryTheory.sfbSheafTensor_properties` in
`Sheaf.CategoryTheory.SheafTensor`.

Edge cases checked: `L` and `M` are arbitrary sheaves (including zero objects), and
there is no finiteness, nonzero, or support hypothesis. The source theorem is for
arbitrary coefficient category satisfying its stated monoidal hypotheses, hence its
`AddCommGrp` specialization includes the zero sheaf and the identity open immersion.

Searches made:

* `msearch.py ... leanfinder "projection formula extension by zero open immersion pro-etale sheaves"` — no exact hit in Mathlib; only unrelated open-immersion declarations.
* `msearch.py ... loogle "isIso_openImmersionLowerShriekProjectionMap_app_app"` — zero hits because this is a project declaration.
* `msearch.py ... grep "openImmersionLowerShriekProjectionMap" CategoryTheory/` — zero Mathlib hits.
* `rg` in `WeilConjectures` found the exact source declaration and its definition in
  `WeilConjectures/SixFunctors/ProEtale/LowerShriek/OpenImmersion/Projection.lean`.

## Earlier second reading (a previous round; superseded)

The source file and node were opened independently. The open immersion, adjunction,
objects, canonical unit-adjoint map, tensor, and isomorphism conclusion all match.
The source uses the equivalent symmetric ordering `j_!(M ⊗ j^*L) → j_!M ⊗ L`; after
swapping the two variables and applying the symmetric tensor isomorphisms this is
exactly the node ordering. No mismatch was found and no change was needed.

## Second reading by Q21

I read the node statement in the source order and compared every item with the existing
source declaration `AlgebraicGeometry.ProEtale.isIso_openImmersionLowerShriekProjectionMap_app_app`
in `WeilConjectures/SixFunctors/ProEtale/LowerShriek/OpenImmersion/Projection.lean`.

* The object `j : U \to X` and the open-immersion hypothesis are the declaration's
  `{U X : Scheme.{u}}`, `(j : U \to X)`, and `[IsOpenImmersion j]`; there is no
  separatedness, finiteness, properness, or nonempty-scheme assumption.
* The adjunction `j^{\Ab}_! \dashv j^*_{\Ab}` is
  `ProEtale.openImmersionLowerShriekUpperStarAdjunction A j`, specialized to
  `A = Ab`; its left functor is the extension-by-zero functor from the lower-shriek
  dependency and its right functor is `upperStar` (the pullback).
* The node's `L : Sh(X_proet, Ab)` and `M : Sh(U_proet, Ab)` are rendered by the
  declaration's arbitrary sheaves `M : Sheaf (Scheme.ProEt.topology X) A` and
  `K : Sheaf (Scheme.ProEt.topology U) A`, respectively, after the explicit swap
  `K := M` and `M := L`. The coefficient category is therefore exactly abelian sheaves.
* The source component is
  `((openImmersionLowerShriekProjectionMap A j).app K).app M`, whose definition is
  `Adjunction.projectionMap` for this adjunction and the lax/strong monoidal structure
  `μNatTrans (upperStar)`. With `K := M` and `M := L`, its displayed order is
  `j_!(M \otimes j^*L) \to j_!M \otimes L`; the node writes the canonically symmetric
  order `j_!(j^*L \otimes M) \to L \otimes j_!M`. The two are identified by the
  symmetry isomorphisms of the recorded sheaf tensor, so the source component is the
  same canonical projection map up to the stated tensor symmetries, rather than a
  different arbitrary map.
* The unit-adjoint description in the node is exactly the definition of
  `Adjunction.projectionMap`: the unit of
  `openImmersionLowerShriekUpperStarAdjunction` followed by the monoidal comparison
  of `upperStar`. The tensor is the sheaf tensor from `sk-def-sfb-sheaf-tensor`, and
  the source's `MonoidalCategory`/`SymmetricCategory` instances supply its symmetry.
* The conclusion is the source instance
  `IsIso (((openImmersionLowerShriekProjectionMap A j).app K).app M)`, hence an
  isomorphism for all such `L` and `M`. No extra clause, quantifier, or hypothesis is
  present in the Lean declaration.

Edge cases were checked: the sheaves are arbitrary, so the zero sheaf is included; the
identity open immersion is included; no index set or integer parameter occurs; empty
schemes and arbitrary characteristics are not excluded by the statement; and the
source's universe parameters are polymorphic (`u'` for coefficients and `u` for the
scheme), with no equality imposed between them.

For the one-definition-per-notion check, I searched the project and Mathlib with
`msearch.py` LeanFinder/Loogle/grep queries for the projection formula, and used `rg`
through both `WeilConjectures` trees and `lean/Sheaf`. Mathlib has no declaration of
this pro-étale open-immersion projection map. The only exact declaration is the source
one above; the module is present at the recorded path, so no new module or duplicate
was written. The dependency nodes `sk-def-sfb-finite-lower-shriek` and
`sk-def-sfb-sheaf-tensor` were opened: they provide the extension-by-zero adjunction
and the sheafified symmetric tensor used here. The blueprint also names
`sk-def-sfb-finite-pushforward-pullback`; its pullback content is supplied by the
recorded upper-star declaration used by the adjunction, and no additional assumption
is introduced in this item.

No mismatch requiring a statement or node change was found. The only presentational
point is the source's opposite tensor ordering, which is exactly accounted for by the
symmetric tensor isomorphisms already described in the worker report. Since the item
uses an existing declaration, there is no Lean module to compile; the existing source
was read with `scompile.py --source` and its declaration and imports were verified.
