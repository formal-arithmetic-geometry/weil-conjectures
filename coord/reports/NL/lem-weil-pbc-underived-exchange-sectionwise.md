## Worker report

The module `Sheaf.AlgebraicGeometry.UnderivedExchangeSectionwise` states
`AlgebraicGeometry.underivedExchangeSectionwise`, with `sorry` as its only
postponed proof. It constructs the supporting canonical map
`AlgebraicGeometry.sectionwiseBaseChangeHom` using two actual pullback lifts.
There are no new nodes, dependency repairs, or changes to the natural-language
statement. The helper belongs to the map explicitly introduced by this node
and is listed in `lean.declarations`; it is not an alternative inverse image,
sheafification, or exchange construction.

The statement follows the reviewed DAG text, including its explicit distinction
between a presheaf representative and a general section after sheafification.
I read the current blueprint node and the underived-exchange paragraph of
`literature/blueprint/main-20261015/blueprint/sec-proper-base-change/sk-def-exchange/_section.md`.
The node's revised formulation of “restrict and sheafify” is important: the
original section need not live on an object étale over X after the arbitrary
base change. The inverse-image unit and restriction along an X'-site arrow
supply exactly the well-typed formulation already in the DAG.

Hypotheses and clauses:

| DAG text | Lean rendering |
| --- | --- |
| A cartesian square of schemes with f, g, g', f' | Explicit scheme and arrow binders; `sq : ChosenCartesianSquare g' f' f g`. This retains the chosen pullback identification, both projection equations, and commutativity. |
| F is an abelian sheaf on X's small étale site | `F : Sheaf X.smallEtaleTopology (AddCommGrpCat.{u + 1})`. |
| Any étale V over Y' and W over Y | `∀ (V : Y'.Etale) (W : Y.Etale)` in the first conjunct. |
| a : V → Y' ×_Y W over Y' | `a : V ⟶ g.Etale.obj W`. Mathlib writes the fibre product in the symmetric order W ×_Y Y'. This is the same over-Y' object via the canonical symmetry. |
| s in F(K), K = X ×_Y W | The binder `s : ((Etale.lowerStar ... f).obj F).obj.obj (op W)` is definitionally F's sections at `f.Etale.obj W`, namely W ×_Y X over X. The symmetric ordering introduces no restriction. |
| P_g(f_*F) and its representative (W,a,s) | `(MorphismProperty.Over.pullback @Etale ⊤ g).op.leftKanExtension H`, with H the existing lowerStar sheaf's underlying presheaf. `leftKanExtensionUnit H` at W, followed by `.map a.op`, is precisely the corresponding colimit coprojection. |
| Its class in the sheaf inverse image | `toSheafify Y'.smallEtaleTopology P` evaluated at V and applied to that generator. Existing `Etale.upperStar` is definitionally the sheafification of this left Kan extension; no comparison choice or extra assumption is introduced. |
| A = X' ×_Y' V and ℓ_a : A → X' ×_X K over X' | `f'.Etale.obj V` and `sectionwiseBaseChangeHom sq.toCommSq W V a : f'.Etale.obj V ⟶ g'.Etale.obj (f.Etale.obj W)`. The first lift maps A to K using a and g'; the second lift pairs that map with the projection to X'. The over-morphism equation is checked by the pullback projection equation. |
| Apply η_g',F at K to s | `((Etale.upperStarLowerStarAdjunction ... g').unit.app F).hom.app (op (f.Etale.obj W)) s`. |
| Restrict along ℓ_a in g' inverse image F | `((Etale.upperStar ... g').obj F).obj.map (sectionwiseBaseChangeHom ...).op` applied to that unit image. |
| The result is a section of f'_*g' inverse image F at V | The RHS has precisely that type, definitionally by `Etale.lowerStar`. |
| The rule extends to a morphism and this morphism is Ex⁰ | The LHS evaluates the existing morphism `(Etale.baseChangeMap ... sq.toCommSq).app F` on the sheafified representative. Thus the first conjunct says the specified morphism realizes the rule on every generator. Since these are the colimit coprojections, this also specifies the composite on the whole presheaf, hence the claimed extension. No arbitrary map is assumed. |
| Equal sheafified classes have equal values | The first conjunct expresses each rule value as the value of the same sheaf morphism on its sheafified class. Consequently equality of the classes gives equality of the rule values, including equality arising only after sheafification. There is no assertion that every sheaf section has a global representative. |
| Its f' adjunct is g' inverse image ε_f after θ | The second conjunct is `(Etale.upperStar ... f').map Ex ≫ counit_f' = squareUpperStarIso.hom.app (f_*F) ≫ (Etale.upperStar ... g').map counit_f`. The direction is diagrammatic composition, exactly as in the node. |

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`:
  `AlgebraicGeometry.ChosenCartesianSquare`, including `isoPullback`, `hom_fst`,
  `hom_snd`, and the inherited `toCommSq`. The existing square comparison is
  `Etale.squareUpperStarIso` on that `toCommSq`, as its docstring prescribes.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, `upperStar`, and
  `upperStarLowerStarAdjunction`. Their source confirms that lowerStar is
  precomposition with base change, and upperStar is the constructed left Kan
  extension followed by sheafification. The same module provides the
  unit-compatible `lowerStarComp`/`upperStarComp` for the proof plan.
- `WeilConjectures.SixFunctors.BaseChange.Square`:
  `AlgebraicGeometry.Etale.baseChangeMap` and `squareUpperStarIso`.
  `upperStar_map_baseChangeMap_app_counit` is exactly the already-available
  adjunct clause, but does not contain the representative formula, so it is
  not an exact existing match for the whole item.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`:
  `AlgebraicGeometry.etaleInverseImageAlgebraicStructures`. I read the current
  source with `scompile.py --source`. Its forgetful comparisons preserve the
  underlying hom bijections and units, so the abelian representatives agree
  with the set description. This is a proof import; no private lift is defined.
- `Mathlib.CategoryTheory.Sites.Sheafification`:
  `CategoryTheory.presheafToSheaf`, `toSheafify`, and
  `sheafificationAdjunction`; the definitions show that `toSheafify` is the unit.
- The stated proof dependencies are also available via imports:
  `Mathlib.CategoryTheory.Limits.HasLimits` for colimits,
  `Mathlib.CategoryTheory.Limits.MorphismProperty` for finite-limit-preserving
  étale base change, `Mathlib.CategoryTheory.Functor.Flat` for the filtered
  presheaf pullback, and `Mathlib.CategoryTheory.Adjunction.Basic` for
  `Adjunction.comp`. The size-convention node is metatheoretic; explicit
  `universe u`, schemes at u, and coefficient groups at u+1 implement it.

Edge cases checked before finalizing:

- The identity square is admitted; a and s remain arbitrary and both sides
  have the same restriction/unit meaning. No nonidentity condition is added.
- F = 0 and the zero section are admitted; every map in the formula is an
  abelian-group homomorphism.
- The empty V, W, or scheme is allowed. There is no Nonempty binder or choice
  of a geometric point; when there is no arrow a, the representative quantifier
  makes no assertion about a nonexistent representative.
- Arbitrary, possibly nonétale g and g' are admitted. For example the square
  with X = Y = Spec k and X' = Y' = A¹ has a well-typed unit at K and an
  X'-étale restriction, without assuming A is étale over X.
- Equality only after sheafification is included. In particular the formulation
  never identifies the sheaf's sections with the presheaf colimit and never
  assumes a representative of an arbitrary global sheaf section.
- Every universe and variable is explicit (`set_option autoImplicit false`).
  There are no extra coefficient-size equalities or scheme hypotheses.

Searches (all remote semantic searches used the prescribed `msearch.py` wrapper):

- LeanFinder: `sectionwise exchange map for etale sheaves on a cartesian square`.
  Eight results, including `Scheme.Etale.forget` and Mayer-Vietoris gluing
  identities. None states the section formula for the exchange map.
- Loogle: `Etale.baseChangeMap, sheafPullbackConstruction.sheafPullbackIso, leftKanExtensionUnit`.
  No hits; the Mathlib index does not know the project's `Etale.baseChangeMap`.
- Mathlib grep through msearch: `baseChangeMap|sectionwise|leftKanExtensionUnit`
  in `CategoryTheory/Sites`: no hits.
- LeanSearch: `The etale base change map sends a left Kan extension representative to pullback unit followed by restriction`.
  Eight results including `Functor.lan`, `lanUnit`,
  `isPointwiseLeftKanExtensionLeftKanExtensionUnit`, `leftKanExtensionUnit`,
  and `TwoSquare.lanBaseChange`. These supply generic infrastructure, not
  the scheme-site comparison with the fixed `Etale.baseChangeMap`.
- `rg` in the upstream `WeilConjectures` sources found the mate construction,
  its pushforward-unit and counit identities, and generic left Kan extension
  generators in `Mathlib/CategoryTheory/Sites/Pullback`. Reading their types
  confirmed that none gives the requested representative formula. Searching
  the exact node id there found no existing statement.
- `rg` in the project's `lean/Sheaf` found existing uses of the exchange map
  and `ChosenCartesianSquare`, but no sectionwise formula. Searches for the
  proposed declaration names in Mathlib, the upstream names table, upstream
  sources, and `lean/Sheaf` found no collision.

The theorem docstring supplies the node's full five-step proof plan, including
cocone relations, naturality in V, sheafification, the composite adjunct, and the
triangle-identity comparison. The helper has real data and no sorry. No
STATEMENT-DISPUTED issue remains.

## Second reading by NL

No second reading by a worker: the current direct-delivery brief requires the
maintainer's independent review. I checked the completed statement against the
node once more, including the two symmetric fibre-product orderings, the unit's
object K, the direction of ℓ_a and its opposite restriction, the three stages of
the sheafified representative, and the adjunct's orientation. The first draft
only displayed the generator formula; I added the explicit adjunct conjunct to
match the final equivalent clause of the node. No natural-language correction
or dependency-interface replacement was needed.
