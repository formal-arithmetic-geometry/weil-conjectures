## Worker report

Delivery: `Sheaf.AlgebraicGeometry.FundamentalGroup.FiberEquivalence`, with two
required dependency modules. All new theorem proofs are `sorry`; the FLC fibre
functor is defined in full from the recorded category and stalk functor. The item's
statement and dependencies are unchanged. No new definition nodes are needed.

The node is rendered by three declarations in the main module:

- Connected scheme and geometric point: `{Y : Scheme}` `[ConnectedSpace Y]`,
  `{Ω : Type w}` `[Field Ω]` `[IsAlgClosed Ω]`, `s : Spec (.of Ω) ⟶ Y`.
  The source uses algebraically closed geometric points; no characteristic,
  Noetherian, quasi-compactness or separation condition is imposed.
- Fundamental group: the binders `G`, its compact topological group structure,
  the fibre actions and `[IsFundamentalGroup (fiber s) G]` follow the project's
  FUNDAMENTAL GROUP convention. Such models exist in the scheme universe by
  `FiniteEtale.exists_isFundamentalGroup`; these binders specify the object π₁,
  rather than impose an additional geometric hypothesis. The witness
  `γ : G ≃ₜ* Aut (FLC.fiber s)` explicitly identifies it with the automorphism
  group in the node, with the evaluation topology. The finite-etale identification
  is the existing `toAutContinuousMulEquiv (fiber s) G`.
- FEt equivalence: the existing `FiniteEtale.equivalenceContAction s G`.
  Its objects are the geometric fibres, its morphisms the fibre maps, and its
  action the given fundamental-group action, as checked in all three source
  lemmas following that definition in FundamentalGroup/Basic.lean.
- FLC equivalence: `E : Y.FLC ≌ ContAction FintypeCat G`. The witness `Φ` and
  its natural Yoneda comparison identify FEt with the *recorded* FLC category.
  `Φ.functor ⋙ E.functor ≅ (equivalenceContAction s G).functor` ties the
  equivalences together. The natural isomorphism `τ` identifies the underlying
  sets of E with `FLC.fiber s`. The displayed equality for every F, g and z
  states that the action is evaluation of `γ g` on that stalk. Hence E is the
  claimed fibre equivalence, rather than an unrelated equivalence of categories.
- Finite limits and colimits: the four `PreservesFiniteLimits` and
  `PreservesFiniteColimits` clauses cover both the FEt and FLC equivalences.
- General connected base change: `fiber_equivalence_baseChange` binds arbitrary
  connected X and Y, `f : X ⟶ Y` and `s : Spec Ω ⟶ X`, so the target point is
  literally `s ≫ f`. GX and GY specify their respective fundamental groups.
  `h : GX →ₜ* GY` is continuous and has underlying homomorphism the recorded
  `fundamentalGroupMap (pullbackFiberIso f s) GX GY`. The natural isomorphism η
  identifies pullback followed by the fibre equivalence with restriction along h.
  The component equation specifies that its underlying bijection is precisely
  `pullbackFiberIso`, whose source definition sends a lift to its composite with
  the first pullback projection. Because η is an isomorphism in ContAction, its
  components are equivariant. This renders both naturality and the asserted
  action through f_* without introducing independent arbitrary fibre bijections.
- Finite étale case: `fiber_equivalence_finiteEtale_baseChange` adds exactly
  `[IsFinite f] [Etale f]`; it states injectivity, equality of the range with the
  stabilizer of `fiberMk (s ≫ f) ⟨Etale.mk f, ...⟩ s rfl`, openness of that
  stabilizer and its `FiniteIndex`. This element is exactly the marked point s
  of the cover's fibre. Combined with the preceding η, base change is restriction
  to that subgroup. The node only asserts finite index, so the stronger formula
  for its numerical index in the proof input is not added to this statement.

Dependency declarations used/read:

- `def-galois-categories`: `Sheaf.AlgebraicGeometry.GaloisCategories`,
  `AlgebraicGeometry.Scheme.FLC`, the full subcategory of the predicate in
  `Sheaf.AlgebraicGeometry.EtaleSheaves`. The existing FEt category and its fibre
  are `Scheme.FiniteEtale` and `FiniteEtale.fiber` in
  `WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale`.
- `def-galois-fibre-functor`: its old record is that finite-etale fibre only.
  The dependency module supplies `Scheme.FLC.fiber` from
  `(pointSmallEtale s).sheafFiber`, using `F.property.2 Ω s` for finiteness.
  Mathlib.CategoryTheory.Galois.Topology supplies `autEmbedding` and the induced
  topology on Aut of any finite-set-valued functor; it does not require assuming
  the FLC Galois-category theorem. ContAction supplies continuous finite actions.
- `thm-galois-lc-etale`: read `EtaleTorsor.toSheafTorsor` in
  WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor and both
  `exists_toSheafTorsor_equiv` declarations in EtaleTorsorDescent. They concern
  torsors only. The dependency module now states the missing categorical
  equivalence, with canonical sheaf-of-sections comparison, all geometric-point
  fibre comparisons, and natural base change after the full-subcategory inclusions.
  Its `finiteEtale_flc_preserves_torsors` explicitly identifies the image of every
  finite abelian torsor with its existing sheaf torsor and intertwines the action
  morphisms on every section. The existing torsor's fields supply simple
  transitivity and local nonemptiness. No private torsor definition is used.
- Base-change source signatures/docstrings read in
  WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction:
  `pullbackFiberIso`, `fundamentalGroupMap`, `fundamentalGroupMap_smul`,
  `continuous_fundamentalGroupMap`, `fundamentalGroupMap_injective`; also
  `pullback` in FundamentalGroup.Functoriality and `fiberMk` from its imports.
  The source `equivalenceContAction` is imported transitively from that module.
- Stabilizer proof input read in the landed
  Sheaf.AlgebraicGeometry.FundamentalGroup.ImageStabilizer:
  `fundamentalGroupMap_range_eq_stabilizer`. It is not needed to elaborate a
  statement, so no unused import of this proof input is introduced.

Edge cases checked before writing:

- The empty finite étale cover and the empty finite locally constant sheaf are
  included; none of the equivalences or the definition of their fibre requires
  a nonempty fibre. Finite limits/colimits include terminal and initial objects.
- An empty base cannot admit s, so ConnectedSpace's nonemptiness removes no case.
- Identity base change, a one-sheet cover and a trivial fundamental group give
  full stabilizer and index one, and satisfy all clauses.
- General base change need not have injective or open image: e.g. an algebraically
  closed point over a scheme with infinite π₁. These claims appear only with the
  finite étale hypotheses, as in the already corrected node.
- Arbitrary characteristic is allowed. The scheme and geometric field use the
  same universe; sheaves take values one universe higher, as required by the
  recorded FLC category. ULift in the natural comparisons is a universe transport
  of sets and maps, not a finiteness or size restriction. All finite sets in either
  universe have representatives in the scheme universe, so E excludes no objects.

Searches for existing notions/statements (all performed before writing):

- msearch.py leanfinder, query `finite etale schemes fibre functor equivalence finite
  locally constant sheaves fundamental group base change`: eight abstract Galois
  theory hits, including FiberFunctor, IsFundamentalGroup and functorToContAction;
  none states the whole scheme theorem or the recorded FLC equivalence.
- msearch.py loogle, query `CategoryTheory.PreGaloisCategory.functorToContAction`:
  eight hits for the abstract action functor and its equivalence instances.
- msearch.py leansearch, query `finite etale covers equivalent finite locally
  constant sheaves`: service unavailable, Internal Server Error. No search verdict
  is claimed for the unavailable service.
- msearch.py grep, query `FiniteLocallyConstant|fundamentalGroup|functorToContAction`
  in CategoryTheory/Galois: ten hits for the abstract group/action constructions.
- rg on Mathlib/AlgebraicGeometry for finite locally constant/fundamentalGroup:
  no scheme equivalence; unrelated FlatRank hits.
- rg on WeilConjectures for FLC, finite locally constant and the item id:
  FundamentalGroup.Basic has the FEt equivalence and its object/action/map lemmas;
  FundamentalGroup.FiniteLocallyConstant has a different full-subcategory encoding
  using IsFiniteLocallyConstantSheafOfTypes, not the recorded Scheme.FLC predicate;
  HenselianFiniteEtale has object-level representability, explicitly documenting
  that the categorical equivalence and group-action correspondence are not stated
  there. EtaleTorsor/EtaleTorsorDescent have the existing torsor construction.
- rg on lean/Sheaf for FLC/flc/finiteLocallyConstant and the proposed declaration
  names: the recorded GaloisCategories and stalk-finiteness module are present;
  none supplies the new equivalence or a fibre functor on that recorded FLC.
  A simultaneous search of Mathlib, WeilConjectures and lean/Sheaf for the proposed
  new names found no collision.

Sources: opened https://stacks.math.columbia.edu/tag/0BND (Theorem 58.6.2,
parts 1 and 3) and https://stacks.math.columbia.edu/tag/0DV6 (Remark 59.65.3).
The untracked literature documents are absent in this clone; the source node's
complete proof and the existing source modules supply the SGA 1 V.6.13/§7 argument.
No statement correction or disputed statement was needed.

Validation: all three modules compiled together on the server with exit code zero
and no warnings, with explicitly declared (distinct) universe variables. Distinct
universe names avoid duplicate declarations in the compilation tool's combined file.

## Dependency modules

`def-galois-fibre-functor`: the recorded `FiniteEtale.fiber` is a functor on covers,
not on Scheme.FLC. FLCFiber.lean supplies the stalk functor on exactly the recorded
FLC category. Its data comes from Mathlib's point sheafFiber and the existing
predicate's finiteness clause; there is no sorry or new topology in the definition.
The finite-etale fibre remains the existing declaration, and the automorphism group
and topology remain Mathlib's Aut and evaluation topology.

`thm-galois-lc-etale`: the recorded `toSheafTorsor` only constructs a sheaf torsor;
it does not state the categorical equivalence. LocallyConstantEquivalence.lean
states that missing equivalence on the recorded categories and the natural
base-change/fibre comparisons. Its second theorem identifies the image of a torsor
with its existing sheaf torsor, and the action morphisms with composition on its
sections; thus it explicitly preserves the simply transitive torsor action. Existing
EtaleTorsor constructions and their converse remain imported and are not copied.

Dry run: deliver2.py --no-push printed OK. The sole pending second-reading
section is reserved for the independent second reader; nothing was pushed.


## Second reading by S1

Independent second reader: I opened the item node, all three delivered modules,
the three statement dependencies and their recorded source declarations. No Lean
signature, definition, or node statement needed repair. This section adds the
independent review and source checks; the Worker report remains above.

Object/hypothesis/conclusion checklist (each verdict is PASS):

1. Y is a scheme, connected, with a geometric point ybar. Lean:
   `{Y : Scheme.{w}} [ConnectedSpace Y]`, `{Ω : Type w} [Field Ω]
   [IsAlgClosed Ω]`, `s : Spec (.of Ω) ⟶ Y`. The source assumes no
   Noetherian, separated, quasi-compact, or characteristic hypothesis.
2. FEt(Y) is the finite étale category and FLC(Y) is the recorded category
   of finite locally constant set sheaves. Lean: `Y.FiniteEtale` from
   FundamentalGroup/FiniteEtale and `Y.FLC` from GaloisCategories. I read
   both definitions, not merely their names: the former is finite objects
   in Y.Etale; the latter is the full subcategory of the recorded
   `IsFiniteLocallyConstantEtaleSheafOfSets` predicate. Its arrows are
   sheaf morphisms. The predicate uses an étale covering with constant
   restrictions and finite geometric stalks, equivalent to finite local
   constant values: on each nonempty trivializing member a geometric
   stalk is its constant value; empty members may be discarded.
3. The group is Aut of the stalk functor with its profinite topology.
   Lean: the project-convention `G` and `[IsFundamentalGroup (fiber s) G]`,
   together with `γ : G ≃ₜ* Aut (FLC.fiber s)`. These describe a model of
   π₁, not a geometric restriction: I read `exists_isFundamentalGroup`
   and `toAutContinuousMulEquiv`. Mathlib's topology is induced by
   `autEmbedding` into finite discrete automorphism groups. Evaluation
   on all objects and on a skeleton give the same topology, since
   isomorphisms identify evaluation coordinates. No second topology.
4. The FEt fibre functor induces an equivalence with finite continuous
   π₁-sets. Lean: existing `equivalenceContAction s G`; I checked its
   definition and the object, action, and map lemmas immediately after it.
   They identify its underlying set with `fiber s`, its action with
   `g • x`, and its map with the geometric fibre map.
5. The corresponding FLC fibre functor is an equivalence, under the Yoneda
   identification. Lean: existential `Φ`, `E`, `γ`, the Yoneda natural
   comparison, and `Φ.functor ⋙ E.functor ≅ equivalenceContAction.functor`.
   The natural isomorphism `τ` identifies E's underlying finite sets with
   `FLC.fiber s`; the equation for every F, g, z identifies the action
   with evaluation of `γ g`. Thus E is the stalk equivalence up to natural
   isomorphism, not an arbitrary categorical equivalence.
6. Compatibility with finite limits and colimits. Lean: the four
   `PreservesFiniteLimits` / `PreservesFiniteColimits` clauses, for the
   existing FEt equivalence and E. Neither existence nor preservation
   excludes the empty diagram.
7. General base change f : Y' → Y, with connected Y' and ybar = f(ybar').
   Lean in `fiber_equivalence_baseChange`: connected X and Y, arbitrary
   `f : X ⟶ Y`, point `s` of X, and target point literally `s ≫ f`.
   GX/GY have the same fundamental-group convention as G above.
8. A continuous f_* and a natural equivariant fibre bijection, with action
   through f_*. Lean: `h : GX →ₜ* GY`, its equality with
   `fundamentalGroupMap (pullbackFiberIso f s) GX GY`, and the natural
   isomorphism η into `ContAction.res ... h`. Its component equation is
   exactly `pullbackFiberIso`, whose source definition composes a lift
   with the first pullback projection. η's morphisms are equivariant.
   There is no injectivity assertion for arbitrary f.
9. If f is finite étale: injectivity, stabilizer image, openness, finite
   index, and restriction to that subgroup. Lean in
   `fiber_equivalence_finiteEtale_baseChange`: exactly `[IsFinite f]
   [Etale f]`, `Function.Injective`, range equality, `IsOpen`, and
   `.FiniteIndex`. The marked fibre element `fiberMk ... s rfl` is ybar'
   in the fibre of X over s ≫ f. Together with clause 8 this gives
   restriction to the image subgroup; compactness and Hausdorffness
   identify GX topologically with that image. No numerical index formula
   beyond the node's conclusion is added.

Dependency-module reading (H12/H13): no new definition nodes are delivered.
`def-galois-fibre-functor` previously recorded only the FEt fibre functor.
FLCFiber defines the missing functor on the exact recorded FLC category:
`ObjectProperty.lift` of the inclusion followed by `pointSmallEtale.sheafFiber`.
The lift uses `F.property.2 Ω s`, so no data or auxiliary proof is sorry.
I read Mathlib Point/Basic.sheafFiber and EtalePoint.pointSmallEtale: they
compute the colimit over opposite pointed étale neighbourhoods, as the
geometric-stalk dependency requires. Its Aut/action category/topology are
existing Mathlib notions, not additional definitions.

`thm-galois-lc-etale` previously recorded a torsor construction, not a
categorical equivalence. LocallyConstantEquivalence supplies the equivalence
with a natural Yoneda comparison, stalk comparisons for every point, and
base-change comparisons for every f. Its second theorem identifies each
finite abelian torsor's image with the existing `toSheafTorsor`, including
its action maps on every section. The node's proof specifies finite abelian
M; these are the `AddCommGroup M` / `Finite M` binders, not an added
restriction. I read `EtaleTorsor.toSheafTorsor` and both converse existence
theorems in EtaleTorsorDescent. Their torsor fields give simple transitivity
and local nonemptiness. The module keeps that construction and its converse,
and its new action equation follows the Yoneda comparison. Both dependency
records explain precisely why their old declarations were insufficient.

Sources read independently: downloaded and read the relevant labelled
blocks of Stacks `pione.tex` (theorem-fundamental-group, 0BND) and
`etale-cohomology.tex` (definition-finite-locally-constant, 03RU;
lemma-characterize-finite-locally-constant, 03RV;
remark-functorial-locally-constant-on-connected, 0DV6) from the Stacks
source repository. Their hypotheses are arbitrary schemes, with connectedness
only for the group equivalence. Also read the node's five proof steps and
ImageStabilizer's declaration/docstring for the finite étale clause. The
main docstrings carry those five steps, split across the three theorems;
the dependency docstrings carry the representation, Yoneda, base-change,
stalk, and torsor steps. Source pages:
[0BND](https://stacks.math.columbia.edu/tag/0BND),
[0DV6](https://stacks.math.columbia.edu/tag/0DV6),
[03RU](https://stacks.math.columbia.edu/tag/03RU),
[03RV](https://stacks.math.columbia.edu/tag/03RV).
There is no `statement_change` in this delivery and no correction to audit.

Edge cases: empty covers/sheaves and empty finite fibres are allowed, as
are empty finite diagrams. The main theorem's point cannot exist over the
empty scheme, so ConnectedSpace's nonemptiness loses no pointed case;
the dependency equivalence itself permits an empty base. Identity f,
trivial fundamental groups and one-sheet connected covers yield the whole
stabilizer and index one. General non-finite-étale f has no subgroup claims.
Characteristic is unrestricted; n and index-set parameters are absent.
All universes are bound explicitly: schemes/fields/group models live in
w, sheaf values in w+1, and ULift transports finite sets between these
universes without restricting their cardinalities. The three module
universe names u/v/w are distinct for the combined compile.

Independent searches, with different wording from the worker:
- LeanFinder: `geometric stalk functor locally constant finite sheaves
  equivalence monodromy`, eight hits for condensed locally constant
  functors, none for the scheme theorem.
- Loogle: `ContAction.res`, eleven hits for continuous action restriction
  and its compatibilities. This is the reused abstract notion.
- LeanSearch: `finite etale covers equivalent finite continuous fundamental
  group actions`, Internal Server Error; unavailable, no search verdict.
- rg in Mathlib/AlgebraicGeometry, WeilConjectures and lean/Sheaf using
  monodromy, finite locally constant, FLC/flc, and all proposed names.
  The existing FEt equivalence is reused. The source's
  `FiniteLocallyConstant.fiber` has a different domain predicate
  (`IsFiniteLocallyConstantSheafOfTypes` with `IsFiniteSheaf`), so cannot
  serve as the functor on the recorded FLC domain. No existing declaration
  supplies the entire theorem or the missing categorical dependency.
  No proposed-name collisions found.

Validation: compiled all three delivered modules together via scompile.py
on the server, in dependency order, exit code 0, no warnings (2.7 seconds).
Read signatures and binders by eye; no auto-implicit variables, file-local
notation, private definitions, or hollow data. Every theorem remains sorry.
No mathematical mismatch found and no correct Lean was rewritten.

## Reviewer fix (R-gfu, stage 2)

- def-galois-fibre-functor reverted (`--revert-nodes`): its record is the closed source
  declaration `AlgebraicGeometry.Scheme.FiniteEtale.fiber`, which the STATE convention
  FUNDAMENTAL GROUP (`[IsFundamentalGroup (fiber s) G]`) and the landed
  lem-galois-pi1-finite-etale-image-stabilizer (E1 7d4a5b1c8) cite as this node's
  declaration; re-pointing it to a new `Scheme.FLC.fiber` would leave that landed statement
  off its stmt_dep's record. FLCFiber.lean is left out with the revert.
- The FLC stalk functor is written inline from the recorded declarations instead:
  `ObjectProperty.ι (IsFiniteLocallyConstantEtaleSheafOfSets (T := Y)) ⋙
  (pointSmallEtale s).sheafFiber (A := Type (w + 1))` (def-galois-categories' `Scheme.FLC`
  and def-weil-pbc-geometric-stalks' `pointSmallEtale`, the same spelling as the landed
  predicate). In `exists_fiber_flc_equivalence` the group identification is
  `γ : G ≃ₜ* Aut (that functor)`, whose topology is G1's
  `SetFunctorAut.functorTopologyInstance` (lem-galois-aut-profinite, the evaluation
  topology of def-galois-aut-topology); `τ` lands in the same functor. In
  LocallyConstantEquivalence.lean (thm-galois-lc-etale) the fibre clause uses the same
  inline functor and the import of FLCFiber is replaced by GaloisCategories.
- Nothing else changed; the thm-galois-lc-etale dependency module is kept.
