## Worker report

This delivery records an exact existing aggregate match for
`sk-def-sfb-module-lower-shriek`. No Lean module is added and no theorem is proved.
The primary declaration is
`AlgebraicGeometry.ProEtale.CondensedRing.lowerShriek`, in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`.
The companion declarations in `lean.declarations` cover every earlier clause of
this umbrella definition. The published source was read using
`scompile.py --source WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`;
its statements and constructions agree with the shared framework copy. The live
source has a proof of the projection-formula instance where the older local copy
still has `sorry`; this record makes no claim about proof closure or changes to
`lean_audit`.

The source is the current blueprint main-20261015,
`sec-six-functors-basics/sk-def-sfb-module-lower-shriek/_section.md`, read in full,
and its DAG statement and expanded six-step proof. The source's own Lean table
lists the same constructions. The `slopmaster2` branch label identifies the
published `WeilConjectures` source root, including the side overlay documented in
`coord/pefw-upstream-framework.md`.

Hypotheses and clauses, matched individually (names without a namespace in this
paragraph are in `AlgebraicGeometry.ProEtale.CondensedRing`):

1. An arbitrary commutative condensed ring is represented by
   `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` with `MonObj Λ` and
   `IsCommMonObj Λ`. This is an internal commutative ring, with no discreteness,
   finite generation, torsion or field hypothesis. The underlying sheaf category
   uses the small pro-etale topology `Scheme.ProEt.topology X`; schemes are
   `Scheme.{u}`. The site object and arrow universes are not identified.
2. The pulled-back coefficients are the dependency's `condensedRingObj Λ X`,
   definitionally `(upperStarFromPoint X).obj Λ`, with its transported monoid
   structure. Its bundled counterpart is `coefficientRing X`. Module objects are
   exactly `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)`.
3. An open immersion is `{U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]`.
   No quasi-compactness assumption is placed on this open-immersion section.
   `ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j` is the
   specified abelian extension-by-zero/pullback adjunction.
4. The projection-formula clause is `hasProjectionFormula_openImmersion`.
   `Adjunction.HasProjectionFormula` asserts
   `∀ L M, IsIso (adj.projectionFormulaMap L M)` for all abelian sheaves L and M.
   The map is defined in `ModuleObjects.ProjectionFormula` by
   `(adj.homEquiv _ _).symm
     (S.obj L ◁ adj.unit.app M ≫ Functor.LaxMonoidal.μ S L (P.obj M))`.
   Thus this is precisely the canonical map in the node, not a chosen arbitrary
   isomorphism. There is no restriction on L or M. The tensor is the sheafified
   pointwise tensor over the integers, not the cartesian product.
5. `linearOpenImmersionLowerShriek Λ j` has source
   `Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
     ((j)^*[Ab.{u + 1}].obj (condensedRingObj Λ X))`
   and target `Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
     (condensedRingObj Λ X)`. Its body is the adjunction's `mapModLeft`.
   The generic construction's action `Functor.ProjectionFormula.smul` is
   `(pf.iso B M).inv ≫ P.map γ[S.obj B,M]`, exactly the inverse projection
   comparison followed by extension by zero of the module action. Its morphism
   map is `P.map f.hom`. `linearOpenImmersionLowerShriek_comp_forget` verifies
   the underlying functor. `linearOpenImmersionLowerShriekAdjunction` has right
   adjoint `(j)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)`, as required.
6. `openImmersionLowerShriek Λ j` is definitionally
   `Mod.comap (condensedPullbackHom Λ j) ⋙ linearOpenImmersionLowerShriek Λ j`.
   This is restriction along the forward alpha_j followed by the linear
   extension, in Lean's left-to-right composition order. `Mod.comap` leaves
   underlying objects and morphisms unchanged. The lemma
   `openImmersionLowerShriek_comp_forget` gives exactly the asserted underlying
   abelian-sheaf extension by zero.
7. Exactness of j_! is given by
   `preservesFiniteLimits_openImmersionLowerShriek`,
   `preservesFiniteColimits_openImmersionLowerShriek`, and
   `preservesHomology_openImmersionLowerShriek`, with additivity supplied by
   `openImmersionLowerShriek_additive`. The specified adjunction is
   `openImmersionLowerShriekUpperStarAdjunction Λ j`. Its construction composes
   `Mod.restrictCoextendAdjunction` with the linear adjunction, then uses the
   inverse of `Mod.extendScalarsIsoCoextendScalars` on the right adjoint. Thus its
   right adjoint is the dependency's actual `upperStar Λ j`, defined by forward
   extension of scalars along alpha_j, with the correct scalar-change direction.
8. A specified compactification gives
   `compactificationLowerShriek Λ c := (c.i)_!open⟦Λ⟧ ⋙ (c.g)_*⟦Λ⟧`.
   The dependency `BoundaryCompactification f` retains quasi-compactness of c.i;
   its underlying upstream compactification is `c.obj.obj`, so the displayed
   construction is applied to that exact factorization. It uses the dependency's
   module `lowerStar`, including restriction along eta_g, not a bare abelian
   pushforward or an unrelated module structure. The upstream `Compactification`
   has `comm : f = i ≫ g`, `IsOpenImmersion i`, and `IsProper g`.
9. For f admitting a compactification, `lowerShriek Λ f` is definitionally
   `compactificationLowerShriek Λ (HasCompactification.compactification f)`;
   `lowerShriek_eq` states the chosen composite explicitly. An input with the
   node's quasi-compact compactification makes f quasi-compact; the upstream
   theorem `Compactification.quasiCompact_openImmersion_iff` then makes the open
   part of every compactification of f, including this chosen one, quasi-compact.
   No independence of different compactifications is assumed or asserted.
10. `lowerShriek_comp_forget` identifies the underlying functor with the abelian
    `ProEtale.lowerShriek Ab.{u + 1} f`, which uses the very same
    `HasCompactification.compactification f`. `lowerShriek_additive` and
    `preservesFiniteLimits_lowerShriek` give additivity and left exactness of
    the composite for all such f.

Dependency declarations read and used by this existing construction:

- `sk-def-sfb-pulled-back-coefficients` and `sk-def-sfb-coefficient-morphisms`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`,
  `isCommMonObj_condensedRingObj`, `coefficientPullbackIso`,
  `condensedPullbackHom`, and `condensedPushforwardHom`, with their monoid-map
  and isomorphism instances. The coefficient maps are canonical, not parameters.
- `sk-def-sfb-module-objects`: the closed upstream audit names Mathlib
  `CategoryTheory.ModObj`, `Mod`, `Mod.forget`, `Mod.regular` in
  `Mathlib.CategoryTheory.Monoidal.Mod`. Its absence of a separate lean record
  is expressly permitted by the 2026-10-18 brief; the definitions are available.
- `sk-def-sfb-finite-lower-shriek`: the recorded
  `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Proper`
  imports the canonical definitions in `.LowerShriek.Open.Defs` and
  `.LowerShriek.Defs`: `ProEtale.openImmersionLowerShriek`, its adjunction and
  exactness, `ProEtale.Compactification.lowerShriek`, and `ProEtale.lowerShriek`.
- `def-sfb-finite-upper-star`: `ProEtale.upperStar` from
  `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs`, the sheafified Kan
  extension; the finite-coefficient reorganization preserves this declaration.
- `sk-def-sfb-sheaf-tensor`: `CategoryTheory.sfbSheafTensor_properties` and the
  canonical `sfbSheafTensorStructure` from `Sheaf.CategoryTheory.SheafTensor`
  and `.SheafTensorStructure`. These use Mathlib's `Sheaf.monoidalCategory`.
  The upstream `ProEtale.sheafMonoidalCategory` uses that same construction;
  `monoidalCategory_sheaf_of_essentiallySmall_eq` records independence of the
  proof of tensor-localization compatibility. No second tensor is introduced.
- `sk-def-sfb-transport`: the closed upstream audit names `Functor.mapMod`
  from `WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod`,
  `Adjunction.mapModAdjunction` from `.CategoryTheory.ModuleObjects.MapMod`,
  and `Functor.ProjectionFormula`, `Adjunction.projectionFormulaMap`,
  `Adjunction.HasProjectionFormula`, `Functor.ProjectionFormula.mapModLeft`,
  `Adjunction.mapModLeftAdjunction` from `.ModuleObjects.ProjectionFormula`.
- `sk-def-sfb-change-of-scalars`: the closed upstream audit names `Mod.comap`
  in Mathlib and `Mod.extendScalars`, `Mod.extendRestrictAdjunction`,
  `Mod.coextendScalars`, `Mod.restrictCoextendAdjunction` in
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`, with
  `Mod.extendScalarsIsoCoextendScalars` in `.ModuleObjects.MapMod`.
- `sk-def-sfb-module-pushforward-pullback`:
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`,
  `AlgebraicGeometry.ProEtale.CondensedRing.lowerStar`, `upperStar`,
  `lowerStar_comp_forget`, `lowerStar_obj_smul`, and
  `preservesFiniteLimits_lowerStar`. These are the exact module operations used.
- `sk-def-nagata-sketch-data`:
  `Sheaf.Compactification.BoundaryRefinement`,
  `AlgebraicGeometry.Compactification.BoundaryCompactification`; the forgetful
  underlying object is the existing `Compactification f`, as explained above.
- `sk-def-sfb-condensed-ring`:
  `Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing` exports
  `Profinite.continuousCoefficientRingObj` and its commutativity instance.
  Such concrete examples fit the arbitrary `Λ, MonObj Λ, IsCommMonObj Λ`
  parameters; the module lower shriek does not restrict to those examples.

Edge cases checked in the signatures and constructions: arbitrary open immersions
(including non-quasi-compact ones), the empty open and identity open; zero modules
(the additive exact functor preserves zero), unrestricted L and M including zero,
and arbitrary commutative condensed rings including the zero ring. No
nonemptiness, nontriviality, finite coefficients, characteristic, Noetherian or
finite-dimensional hypothesis is added. The compactification formula works for
any supplied factorization, including a proper morphism's identity-open
compactification; it introduces no false claim that arbitrary f has a
compactification. There is no independent small diagram universe forced onto
the pro-etale site. These are statement/definition checks, not new Lean proofs.

Searches performed, 2026-10-18:

- msearch leanfinder: "Extension by zero for module objects over pulled back
  condensed coefficient rings on pro-etale sites, projection formula, and lower
  shriek by compactification". Eight hits concern condensed free/solid modules
  and locally constant constructions; none is this geometric construction.
- msearch loogle: `"lowerShriek"`. Zero Mathlib hits.
- msearch grep: `lowerShriek|extensionByZero|ProjectionFormula` in
  `Mathlib/CategoryTheory`. Zero hits.
- msearch leansearch: "Extension by zero for sheaves of modules is exact and left
  adjoint to restriction along an open immersion". Eight hits include
  `Scheme.Modules.restrictAdjunction` and `SheafOfModules.PullbackConstruction.adjunction`;
  these concern different categories or the opposite operation and are not matches.
- rg in the slopmaster2 source: the item id and the exact names
  `linearOpenImmersionLowerShriek|compactificationLowerShriek|hasProjectionFormula_openImmersion`
  have no hits in that older checkout. The broader
  `lowerShriek|extensionByZero|ProjectionFormula` finds finite-coefficient and
  etale operations, not this module-object implementation.
- rg in shared `lean/Sheaf`: the exact names occur as uses in
  `Compactification/NagataDensityNormalization.lean`, not duplicate definitions.
  The broader search also finds general ringed-sheaf slice extension-by-zero
  interfaces, not this condensed-coefficient compactification construction.
- Reading the audit's exact module in shared `lean/WeilConjectures` finds the
  full implementation, and `scompile.py --source` confirms the current published
  source. This is the exact match used in the record; the old-checkout absence
  is not used to justify a duplicate.

No new nodes, dependency repairs, statement corrections or disputed clauses.
Only the item's lean field is changed. The delivery wrapper checks every listed
existing declaration through a compiled probe and runs server preflight.

## Second reading by Q27

Independent maintainer reading, 2026-10-18, for immutable delivery
32ad74a810ba1efd666f7893e95f0bf70dc36602. This reading was performed by a reader
who did not write or previously second-read this delivery; the heading is the
required delivery-report heading, not a claim of another Q27 worker session.

Read the immutable item and all eleven statement dependencies, the full review
brief and stage-2 criteria, the blueprint source _section.md (order 1684), all
its detail/proof files, the group clone's exact 51-module framework interfaces,
and the published module via scompile.py --source. The existing binding is
correct in substance. The only mismatch found in the delivery was this section's
former placeholder; this replacement supplies the actual reading. No statement,
Lean declaration, dependency or node record was changed.

### Hypotheses and conclusion clauses

The exact implementation read is the group clone's
`lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/LowerShriek/Defs.lean`.
Its module docstring describes the projection formula, action, scalar-change direction,
adjunction, and chosen compactification. Also read the current published source through
`scompile.py --source` for this module. The published projection-formula proof is now
filled; the older group copy has sorry in that Prop-valued instance. The signatures and
data constructions used here agree. This delivery does not change either source or
claim proof closure.

| Node clause | Exact Lean rendering and assessment |
| --- | --- |
| Arbitrary commutative condensed ring | `Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u+1}`, `[MonObj Λ] [IsCommMonObj Λ]`. No finite, discrete, field, nontriviality or completeness assumption. |
| Schemes, coefficient rings, modules | `Scheme.{u}`, `condensedRingObj Λ X = (upperStarFromPoint X).obj Λ`, and Mathlib `Mod` over this internal ring in `Sheaf (Scheme.ProEt.topology X) Ab.{u+1}`. Correct small pro-etale site and tensor, not an etale or cartesian substitute. |
| Arbitrary open immersion | `{U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]`; no quasi-compactness assumption on j. |
| Projection map is invertible for every L,M | `hasProjectionFormula_openImmersion` for the specified abelian adjunction. `Adjunction.HasProjectionFormula.isIso` quantifies over both sheaves. `projectionFormulaMap` is the adjoint of `S.obj L ◁ adj.unit.app M ≫ LaxMonoidal.μ S L (P.obj M)`, exactly the canonical map. |
| Linear extension and action | `linearOpenImmersionLowerShriek` is the adjunction's `mapModLeft (condensedRingObj Λ X)`. `ProjectionFormula.smul` is the inverse canonical projection isomorphism followed by `P.map` of the action. Morphisms map by abelian extension by zero. |
| Lifted adjunction | `linearOpenImmersionLowerShriekAdjunction` has right adjoint the actual `(j)^*[Ab].mapMod`, not an arbitrary functor. |
| Extension by zero | `openImmersionLowerShriek = Mod.comap (condensedPullbackHom Λ j) ⋙ linearOpenImmersionLowerShriek Λ j`. Forward alpha_j has the required direction for restriction. |
| Underlying sheaf and exactness | `openImmersionLowerShriek_comp_forget`, its additive instance, both finite-limit/finite-colimit instances and `preservesHomology_openImmersionLowerShriek` cover all assertions. |
| j_! left adjoint to the dependency's j^* | `openImmersionLowerShriekUpperStarAdjunction` composes restriction/coextension and the linear adjunction, then identifies Coext with Ext using invertible alpha_j. The right side is the recorded module pullback defined with extension of scalars. |
| Specified compactification | `compactificationLowerShriek Λ c = (c.i)_!open⟦Λ⟧ ⋙ (c.g)_*⟦Λ⟧`. For a recorded `BoundaryCompactification`, instantiate with `c.obj.obj`; its quasi-compact open property is retained, not assumed away. |
| Choice of compactification | `lowerShriek Λ f` uses `[HasCompactification f]` and `HasCompactification.compactification f`; `lowerShriek_eq` displays precisely the composite. A choice is expressly permitted by the node, not a hollow choice of an unspecified functor. |
| Underlying abelian lower shriek and left exactness | `lowerShriek_comp_forget` uses the identical chosen compactification on both sides. `lowerShriek_additive` and `preservesFiniteLimits_lowerShriek` give left exactness. No independence-of-compactification claim is added. |

The upstream Compactification interface is more general than the blueprint's: its open
part need not be quasi-compact. This does not exclude any source case. For a blueprint
compactification, f is quasi-compact; `Compactification.quasiCompact_openImmersion_iff`
then shows that the upstream chosen compactification has quasi-compact open part too.
Read that theorem, Compactification's fields, HasCompactification and its choice definition
in `WeilConjectures/Compactification/Defs.lean`, and the actual BoundaryRefinement module.
There is no additional density or qcqs-base assumption in this underived definition.

### Dependency and uniqueness checks

Read the declarations, binders and surrounding docstrings in these exact interfaces:

- Pulled-back coefficients and coefficient morphisms: ModuleObject/Basic.lean,
  `coefficientRing`, `condensedRingObj`, transported commutativity,
  `upperStarFromPointComp`, `coefficientPullbackIso`, `condensedPullbackHom`,
  its IsMonHom/IsIso instances, and `condensedPushforwardHom` as the unit mate.
- Module objects: Mathlib/CategoryTheory/Monoidal/Mod.lean,
  `ModObj`, `Mod`, its action-compatible morphisms, `regular`, `forget`, `comap`.
- Finite lower shriek and upper star: FiniteCoefficient/LowerShriek/Open/Defs.lean,
  FiniteCoefficient/LowerShriek/Defs.lean and UpperLowerStar/Defs.lean:
  localization opposite Kan extension and sheafification, open adjunction and
  exactness, compactification composite and ordinary pullback.
- Tensor: Sheaf/CategoryTheory/SheafTensor.lean and SheafTensorStructure.lean;
  upstream GrothendieckAbelian/Monoidal/Defs.lean and
  ModuleObject/UpperLowerStar/Monoidal.lean. They use Sheaf.monoidalCategory, the
  sheafified objectwise integer tensor. The equality interface confirms the same
  tensor across the two presentations.
- Transport and scalars: ModuleObjects/ProjectionFormula.lean, MapMod.lean,
  ExtendScalars.lean, and Mathlib/CategoryTheory/Monoidal/Mod.lean in the
  WeilConjectures extension tree. Read the actual action and functor bodies,
  canonical projection map, lifted adjunction, extension/coextension functors,
  restrictCoextendAdjunction and extendScalarsIsoCoextendScalars.
- Module pushforward/pullback: ModuleObject/UpperLowerStar/Defs.lean; lowerStar
  is mapMod followed by restriction along eta_f; upperStar uses forward Ext_alpha;
  the underlying-sheaf, action and finite-limit declarations match the dependency.
- Nagata data: Sheaf/Compactification/BoundaryRefinement.lean, including the
  quasi-compact full subcategory and boundary-preserving wide subcategory.
- Condensed ring: Sheaf/AlgebraicGeometry/ContinuousCoefficientCommRing.lean
  and ContinuousCoefficientUniverse.lean. Its continuous-ring examples are genuine
  sheaves with pointwise operations; this item takes an arbitrary internal ring,
  not only the concrete examples or Type-0 coefficients.

Independently searched Mathlib CategoryTheory and the group's Sheaf tree for
`extensionByZero`, `lowerShriek`, and extension-by-zero wording; also searched the
old WeilConjectures tree and the Sheaf tree for the exact linearization and
compactification names. Generic ringed-slice and etale constructions have different
categories. The exact condensed-module implementation is the published framework,
already used by this binding. There is no duplicate construction. The worker records
LeanSearch, Loogle/LeanFinder and text searches, with queries and outcomes.

### Gates, universes and edge cases

All binders are bound in the module's universe/section variables. The scheme/site
universe u is retained with abelian coefficients at u+1; the small site is the
WeaklyEtale over-category, not a replacement site. No equality between independently
specified site universes is imposed. No arbitrary comparison map or hollow data
construction was found. Existing projection-formula invertibility determines its
inverse; adjunctions are constructed from Hom equivalences. The explicit permitted
choice of compactification is separate from any choice of an undetermined functor.

Checked empty and identity opens, non-quasi-compact opens, zero modules and zero
coefficients, arbitrary L and M including zero, empty schemes, and proper morphisms
with their identity-open compactification. No index, degree, prime or characteristic
restriction occurs. General lower shriek is only left exact as asserted; no false
exactness of proper pushforward is claimed.

No delivered Lean file exists, so the source/blueprint docstring and sorry-only
new-proof gates have no newly authored declaration to check. The existing upstream
module has explanatory docstrings but not this project's blueprint markers; reusing
it does not require duplicating or rewriting upstream. The delivery introduces no
proof, no live Lean write, no global build, and no pro-etale substitute.

Compared all direct stmt_deps/proof_deps with the current
`origin/newtargets-dag:coord/route-pivot-dropped.txt`: intersection is empty.
No item repair note exists at the named current-ref path. This is an underived
module-object construction; no infinity/dg/model, coherent-section, operad or
Quillen machinery is reintroduced. No pre-pivot repair-note comparison is applicable.
The missing-helper and universe-repair rules therefore require no additional module
or prerequisite in this delivery. No statement_change or citer audit is needed.

### Compiler evidence

This is an existing-only delivery: there are zero delivered Lean files to compile.
The worker report records source retrieval and the delivery wrapper's existing-name
probe, rather than a new-file compilation log. Independently reproduced that check:

`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q27 sk-def-sfb-module-lower-shriek fixes/ReviewProbe.lean`

The temporary probe imported
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`, opened
`AlgebraicGeometry.ProEtale.CondensedRing`, and issued `#check @<short-name>`
for each of the twenty names in the immutable lean.declarations list, in order.
The final input had maximum line length 73 and no proofs or definitions. The wrapper
compiled sandbox `Sheaf/Stage2/Sandbox0.lean` and library `Sheaf/Stage2/Check.lean`
against its private overlay, exited 0, and resolved all twenty declarations; the
library check reported 3.8 seconds. No Lean error or source warning remained in
this shortened probe. The first probe also exited 0 but had two long-line warnings
in reviewer-generated #check lines; these were repaired before the final run.
The temporary probe was removed and is not a proposed library file.

Also retrieved the current exact source through
`scompile.py --source WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs`.
The immutable lean.statement is verbatim the three-line `noncomputable def lowerShriek`
signature before `:=`, in both the group source and the retrieved published source.
Read the surrounding section variables too: Λ, MonObj, X, Y, f and HasCompactification
are genuine binders; no extra commutativity assumption is silently needed for the
lower-shriek definition itself. The module adjunction is specialized to the commutative
case as the node requires. Compiling a name probe does not establish proof closure;
existing open inputs in the audit remain open. No lake build, global build, direct
ssh invocation, delivery/merge command, or repository mutation was performed.


