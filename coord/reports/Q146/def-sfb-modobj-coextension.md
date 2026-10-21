## Worker report

Recorded the existing declaration `CategoryTheory.Mod.coextendScalars` from
`WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars` (source lines 733–740).
No new Lean module, theorem, axiom, or definition is delivered. Only the item's
`lean` field changes. There is no repair note for this item in `coord/repair-notes/`.

Source read: the current blueprint
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/`
`sk-def-sfb-change-of-scalars/def-sfb-modobj-coextension.md`, complete text, and the
DAG node's four elementary construction/well-definedness steps. The upstream
module's full coextension construction at lines 484–740 was read, including each
helper's signature, docstring and implementation. The example CompactObject
module is now withdrawn; its node records the upstream existing declaration.

Hypothesis and clause correspondence:

- The arbitrary monoidal category is `{C : Type u} [Category.{v} C]
  [MonoidalCategory C]` (line 81), with independent object/morphism universes.
  `[MonoidalClosed C]` (line 488) means precisely that each `tensorLeft X` has a
  specified right adjoint: `Closed.rightAdj`, `Closed.adj`, `ihom`, and `ihom.ev`
  in `Mathlib.CategoryTheory.Monoidal.Closed.Basic` (lines 39–94). Its Hom
  bijection is `MonoidalClosed.curry` / `uncurry` (lines 146–152).
- Existence of equalizers is exactly `[HasEqualizers C]` (line 549).
  No braiding, commutativity, coequalizers or preservation of equalizers is used.
  The previous extension section closes its `Mod` namespace at line 482;
  its stronger variables do not enter the new coextension namespace.
- The monoid objects are `{R S : C} [MonObj R] [MonObj S]`; the arrow is
  `(φ : R ⟶ S)` (line 488). The node's morphism-of-monoids requirement is
  `[IsMonHom φ]`, from its recorded monoid dependency. The existing construction
  in fact makes sense for any underlying arrow φ; specialization to a monoid
  morphism is exactly this node's construction. This additional generality
  does not replace or alter the input monoid morphism.
- An R-module object N is `(N : Mod C R)` (line 492), with action `γ[R,N.X]`.
  The categories in the conclusion are exactly `Mod C R` and `Mod C S`.
- The equalizer's first parallel map is `coextendFst φ N` (lines 493–497):
  `(MonoidalClosed.pre (φ ▷ S ≫ μ[S])).app N.X`. It precomposes with
  `R ⊗ S ⟶ S ⊗ S ⟶ S`, the required R-action on S.
- The second is `coextendSnd S N` (lines 500–503):
  `MonoidalClosed.curry ((α_ R S _).hom ≫ R ◁ (ihom.ev S).app N.X ≫ γ[R,N.X])`.
  Its source and target are `[S,N]` and `[R ⊗ S,N]`, and its uncurried formula
  is exactly the ordered tensor product R,S,[S,N] specified in the node.
- `coextendScalarsObj φ N` has underlying object
  `equalizer (coextendFst φ N) (coextendSnd S N)` (lines 589–614).
  `coextendι φ N` is `equalizer.ι` (620–621) and `coextendEv φ N` is
  `S ◁ coextendι φ N ≫ (ihom.ev S).app N.X` (633–634).
- The equalizer universal property in the final paragraph is Mathlib's
  `equalizerIsEqualizer`, `equalizer.lift`, `equalizer.lift_ι` and
  `equalizer.existsUnique` in `Mathlib.CategoryTheory.Limits.Shapes.Equalizers`,
  lines 837–893. Thus the object is a genuine equalizer, with unique
  factorization for every test object, not an arbitrary object or map.
- The S-action is `coextendSMul φ N` (567–576). It is the equalizer lift of
  `MonoidalClosed.curry ((α_ S S _).inv ≫ μ[S] ▷ _ ≫
    S ◁ equalizer.ι _ _ ≫ (ihom.ev S).app N.X)`.
  Currying in the first S factor leaves `S ⊗ E` as domain, so ordered inputs
  t,s,e evaluate to `v(t*s,e)`. This is `(s • f)(t) = f(t*s)`, without a swap
  or a commutativity assumption. `coextendScalarsObj` equips this map with
  the unit and associativity laws. The proofs use respectively the right
  unit law and associativity, as in node steps 2 and 3.
- On an R-linear morphism f, `coextendScalarsMap φ f` (723–726) is
  `coextendHomMk φ (coextendEv φ N ≫ f.hom) ... ...`: precisely postcomposition.
  It factors the transpose through the equalizer; the two supplied equations
  give equalization and S-linearity. The evaluation identity at lines 729–731
  identifies this map intrinsically as postcomposition. The functor at
  lines 736–740 takes exactly these objects/maps and supplies identity and
  composition laws by equalizer uniqueness, matching node step 4.

Recorded dependencies read and used (no private copies):

- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`, declaration
  `CategoryTheory.Mod`, with `ModObj` (59–65), `IsModHom` (213–214), `Mod.Hom`
  (281–285), category instance (313–316), `Mod.regular` (336–338) and
  `Mod.forget` (347–349). Here D = C with the self tensor action; this is the
  generic part of the dependency required by this item. Its sheaf
  specialization is not an assumption on this general coextension node.
- `det-def-sfb-ring-object-monoid`: the recorded Mathlib match in
  `Mathlib.CategoryTheory.Monoidal.Mon`: `MonObj` (73–85), `IsMonHom`
  (213–215), `Mon` (256–259), `Mon.Hom` (521–524), `Mon.id` (542), `Mon.comp`
  (551–552), `Mon.instCategory` (555–558), `Mon.forget` (595–597),
  `Mon.forget_faithful` (602), `IsCommMonObj` (1222–1223). Their full
  signatures and nearby docstrings were read. Only the noncommutative
  monoid and monoid-hom clauses enter this item.

Edge cases checked by reading the actual construction: R and S need not be
commutative; C need not be braided, concrete, additive, small, or have a zero
object. The action never interchanges tensor factors. There is no injectivity,
surjectivity or invertibility assumption on φ. Identity maps and the unit monoid
are included; coincident equalizer arrows use the same ordinary universal
property. Empty or zero objects are not excluded by any extra hypothesis.
There is no elementwise detection assumption: curry/uncurry and equalizer
uniqueness compare morphisms. No hollow data or new postponed proof is added.
No statement correction or STATEMENT-DISPUTED issue was found.

Searches actually run through `/home/ubuntu/weil-launcher-all/batch2/msearch.py`
with group Q146 and this item:

- leanfinder: "Coextension of scalars for internal modules over a monoid morphism
  in a closed monoidal category as an equalizer of internal homs". Eight hits,
  including ModuleCat restriction/coextension formulas and closed structure on
  ModuleCat/Rep; none gives the general internal-module construction.
- loogle: `"coextendScalars"`. Twelve hits, all concrete `ModuleCat` change-of-rings
  declarations, not the required arbitrary monoidal category.
- grep: `coextendScalars|coextendFst|coextendSnd` in `CategoryTheory`. Zero Mathlib
  hits; the direct source read confirms these helpers are upstream additions.
- leansearch: "Coextension of scalars for module objects over monoids in a closed
  monoidal category with equalizers". Eight hits, all concrete ModuleCat
  extension/coextension data; no general internal construction.

Direct source searches: `rg -n 'coextendScalars|coextension|Coext'` in the
project's `lean/WeilConjectures/CategoryTheory` and `lean/Sheaf/CategoryTheory`
located `ModuleObjects/ExtendScalars.lean`; broader searches in both source roots
also found concrete étale/sheaf ModuleCat uses. The exact item-id grep in
`lean/WeilConjectures` returned no hit. `rg -n 'coextendScalars'` in
`dag/lean_names_upstream.json` returned no hit. The upstream source construction
is nevertheless present and was checked clause by clause as above. A focused
`rg -n 'coextendFst|coextendSnd|coextendSMul|def coextendScalars' lean/Sheaf`
returned no duplicate construction.

Validation: `deliver2.py --no-push` checks all recorded existing declarations
through scompile.py against the server's published live build, then runs server
preflight. The first dry run compiled the existing declarations successfully but required
 the upstream branch label `slopmaster2`; that metadata was corrected. Its
 signature comparison starts at `def`, so the optional `noncomputable` modifier
 was removed from `lean.statement` as well. The construction is unchanged.

## Second reading by Q146

A separate rereading by the same worker (no other agents were started, as the
brief requires), with the node and upstream module open, checked all clauses
again. The key possible mismatches were the tensor order and inherited stronger
hypotheses from extension of scalars. Source lines 482/486 close and reopen the
namespace, and the action at 569–576 curries the first S input without braiding.
The general construction does not require IsMonHom, but its value at the node's
monoid morphism is exactly the required equalizer/action/functor. No new module
or statement correction is needed. Independent mathematical review is left to
the maintainer, as specified in the dispatch brief.

Dry-run result: `OK (dry run): commit 338b84619d2 passes the preflight and compiles; nothing pushed`.
