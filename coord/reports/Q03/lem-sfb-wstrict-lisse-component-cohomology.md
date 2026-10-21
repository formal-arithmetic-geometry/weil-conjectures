## Worker report

Delivered module: `Sheaf.Paper.WStrictLisseComponentCohomology`.
Main declaration:
`AlgebraicGeometry.ProEtale.CondensedRing.wstrict_lisse_component_cohomology`.
The main theorem and the composition theorem have `sorry` proofs, as required for
stage 2. All five auxiliary constructions have real bodies assembled from existing
functors, adjunctions, natural isomorphisms, and the existing K-injective-preservation
criterion. There is no choice of an arbitrary map or isomorphism.

Sources read: Hemo--Richarz--Scholbach, *Constructible sheaves*, local PDF,
Section 3, Lemma 4.1, Proposition 4.3, equation (4.2), and Corollary 4.7,
particularly the relative-component construction preceding Proposition 4.3 and
its proof that the component lift is w-contractible. The node explicitly records
that the w-strictly-local extension is agent-formulated; it is not attributed to
a verbatim assertion of Proposition 4.3. The docstring retains all nine steps of
the node's hypercover argument, including the degree-zero/K-flat duality step
and the normalization by the actual unit.

Hypothesis and conclusion correspondence:

- An arbitrary commutative condensed ring is
  `(Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]`. The abbreviation is
  exactly the bundled monoid of abelian sheaves on the coherent profinite site.
  It is not restricted to condensed rings represented by topological rings.
- The pulled-back coefficient on every scheme is the existing
  `condensedRingObj Λ.X X`, the underlying ring of `coefficientRing X Λ`.
  That definition uses `upperStarFromPoint` and its monoidal ring transport.
- The small pro-etale site is the existing `Scheme.ProEt.topology X`, and
  coefficients lie in `Ab.{u + 1}`, for schemes and profinite spaces in universe
  `u`. Thus the site has its original object universe `u+1` and morphism
  universe `u`; no equality of these universes is assumed.
- The schemes called `X'` and `X` in the node are called `X` and `Y` in Lean;
  their map is `(f : X ⟶ Y)`. The two `[IsAffine ...]` binders assert affineness.
- W-strict locality of their coordinate rings is exactly
  `[IsWStrictlyLocalRing Γ(X, ⊤)] [IsWStrictlyLocalRing Γ(Y, ⊤)]`, using the
  recorded upstream class. This includes w-locality and strictly henselian
  localizations at maximal ideals.
- The component hypothesis is
  `IsHomeomorph f.continuous.connectedComponentsMap`. Mathlib's
  `ConnectedComponents` has the quotient topology, and this map is the quotient
  map induced by the actual scheme morphism. The recorded spectral-space theorem
  supplies the profiniteness fact without changing the quotient space.
- The coefficient module is
  `M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ.X Y)`.
  This is the recorded internal module category, not a substitute category of
  section modules.
- Finite-rank lisseness is the recorded `IsLisseCoefficientModule Λ.X M`.
  Reading its body and `Mod.IsFree` confirms that it means a pro-etale cover
  and an isomorphism with `Mod.finiteFree R n` on each member, where `n : ℕ`
  may vary. No positive-rank, constant-rank, or connectedness condition is added.
- `condensedModuleSections Λ.X Y` is the existing forgetful functor to abelian
  sheaves followed by presheaf evaluation at `op (Scheme.ProEt.mk (𝟙 Y))`.
  Its `rightDerivedFunctor` is the ordinary unbounded K-injective total right
  derived functor, with values in `DerivedCategory Ab.{u + 1}`.
- `componentDerivedSectionsPullback` applies that sections functor to the actual
  `derivedUpperStarLowerStarAdjunction Λ.X f` unit and then the canonical Leray
  comparison. The Leray comparison is built by
  `Functor.rightDerivedFunctorCompIso'` from terminal-section comparison and
  the criterion that a right adjoint of an exact functor preserves K-injectives.
  Its underived terminal comparison uses
  `globalSectionsLowerStarIso` and both terminal-evaluation identifications.
- `componentLisseSectionsPullback` precomposes with
  `DerivedCategory.singleFunctor _ 0` and postcomposes with the canonical
  `singleFunctorCompLeftDerivedFunctorIso` for exact `upperStar`. Consequently
  its component at `M` has exactly the source `RΓ(Y,M[0])` and target
  `RΓ(X,((upperStar Λ.X f).obj M)[0])` in `D(Ab)`.
- The conclusion is `IsIso ((componentLisseSectionsPullback Λ f).app M)`,
  asserting invertibility of that specific map, rather than merely existence
  of some isomorphism between the two objects or per-degree identifications.
- Naturality in `M` is part of the natural transformation type of
  `componentLisseSectionsPullback`. Composition compatibility is stated in
  `componentLisseSectionsPullback_comp`, using exactly `upperStarComp` and
  the derived sections of its single-degree component. For a commutative
  diagram, apply this equality to its two factorizations; equality of the
  composites identifies their direct section maps. This gives precisely
  diagram naturality through the canonical pullback composition comparisons.
  The structural composition assertion holds for all modules and scheme maps;
  the main invertibility theorem alone needs w-strict locality and lisseness.
- There are no completeness, discreteness, Noetherianity, or extremal
  disconnectedness binders anywhere in the statement or section constructions.

Recorded dependency declarations used, after reading their source signatures and
docstrings:

- `Sheaf.Topology.ProfiniteCondensedRing`: `Profinite.CondensedRing`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing` and `condensedRingObj`, reexported
  by the module-derived-pushpull dependency.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `AlgebraicGeometry.Scheme.ProEt`
  and `Scheme.ProEt.topology`, reexported by the same dependency.
- `Mathlib.CategoryTheory.Monoidal.Mod`: `CategoryTheory.Mod`, its module
  actions, morphisms, and forgetful functor.
- `Sheaf.Paper.CondensedModuleDerivedPushpull`:
  `moduleObjectDerivedPushforward`, `moduleObjectDerivedPullback`; it reexports
  `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar`
  and its `derivedUpperStarLowerStarAdjunction`, exact-pullback comparison,
  and underlying `upperStar`, `lowerStar`, `upperStarComp`.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`:
  `AlgebraicGeometry.ProEtale.IsLisseCoefficientModule`; its finite free meaning
  is the existing `Mod.IsFree` from
  `WeilConjectures.CategoryTheory.ModuleObjects.Free`.
- `WeilConjectures.RingTheory.ProEtale.WContractible`: reexports
  `IsWStrictlyLocalRing` from `WeilConjectures.RingTheory.ProEtale.WLocal`.
- `Sheaf.Topology.SpectralSpace.ConnectedComponentsProfinite`:
  `spectralSpace_connectedComponents_profinite`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, with the existing framework instances.
- Definition dependency `def-sfb-condensed-module-sections` owns the existing
  `AlgebraicGeometry.ProEtale.condensedModuleSections` in
  `Sheaf.Paper.CondensedQcqsPushforwardContinuity`. The continuity theorem is
  not a statement dependency; its conclusion is not used to type the item.

All thirteen other recorded proof-dependency modules are imported with plain
`import` (the lisse-definition module is already a public statement import).
`lem-sfb-acyclic-hypercover-pullback-normalization` has no Lean record yet, so
its proof import is necessarily absent. Its mathematical use remains in the
main theorem's proof docstring. It is a proof dependency, not a missing notion
needed to type this stage-2 statement.

Edge cases checked before writing and again against the final signature:
empty schemes and empty component spaces (no `Nonempty` or nontrivial-ring
binder); rank-zero modules; the zero condensed ring; disconnected affines and
ranks varying over an infinite cover; profinite component spaces that are not
extremally disconnected; non-Noetherian rings; identity morphisms and arbitrary
commuting factorizations; ordinary unbounded derived categories while the
hypercover proof uses degree-zero bounded-below inputs. All remain covered.
The source and target of the map remain in the ordinary derived category, not
only their cohomology groups. The theorem does not assert vanishing of higher
sections on a general w-strictly-local affine.

Searches actually run:

- `msearch.py ... leanfinder` with query "Derived global sections of a lisse
  condensed module on w strictly local affine schemes are invariant under
  homeomorphism of connected components": eight hits, on condensed/discrete
  module functors; none states this geometric invariance theorem.
- `msearch.py ... loogle` with query `ConnectedComponents.map, IsIso`:
  zero hits, diagnostic unknown identifier `ConnectedComponents.map`.
  The correct existing API was found in the source as
  `Continuous.connectedComponentsMap` and used directly.
- `msearch.py ... grep` with query
  `(lisse|dualizable).*(connectedComponent|wStrict|w_strict)|(wStrict|w_strict).*(lisse|condensed)`:
  zero hits in Mathlib.
- `msearch.py ... leansearch` with query "Derived global sections internal
  condensed modules pullback along morphism of w strictly local affines
  identical connected components": eight hits on ordinary module-sheaf
  pullbacks and affine global sections; none is this theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  w-strict/lisse component keywords: no existing matching theorem. Searches
  for sections and derived-section APIs found `condensedModuleSections`,
  `globalSectionsLowerStarIso`, total derived composition, and the exact
  single-degree comparison, all reused. Searches for the seven proposed
  declaration names found no collisions.

Validation: all compiler probes used `module` headers and `scompile.py` only.
The final file, including all available proof imports, passed both sandbox and
library-module server compilation (13.2 s and 11.5 s respectively). Every
universe and variable is explicitly bound; both auto-implicit options are off.
No overlength line or compiler warning other than the expected sorry warnings.

No STATEMENT-DISPUTED finding, statement correction, or dependency-interface
repair was necessary. The new definition node below repairs the returned H2
ownership defect without changing any Lean declaration.

## Second reading by Q03

I reread the completed file against the node and the dependency source bodies.
This is the worker's second pass; the maintainer performs the independent review.
The domain/codomain names are reversed relative to the node's labels but the
map direction and both affine/w-strict-local hypotheses agree. The homeomorphism
is imposed on the actual quotient map, not an unrelated homeomorphism. The
lisse predicate permits zero and varying ranks. The chosen `Γ` abbreviation is
literally final-object evaluation, not Hom under an unproved comparison. The
map expands to the actual derived module adjunction unit, followed by the
unit-normalized composition comparison and the canonical exact degree-zero
comparison. Thus it has the specified normalization, not an arbitrary
isomorphism. The composition equation has its comparison on the composite
pullback target, in the direction `upperStarComp.hom`; both sides end at
sections of `f^*g^*M`. This and module naturality account for the diagram clause.
All seven declarations are listed in the node record. No mathematical mismatch
was found; no statement change was made. The only added statement dependency
records ownership of the existing sections helper; it adds no hypothesis.

## New nodes

`def-sfb-condensed-module-sections` records the existing, fully constructed
`AlgebraicGeometry.ProEtale.condensedModuleSections`, with `existing: true`;
it adds no module and duplicates no declaration. For any condensed ring
(the `[MonObj Λ]` binder, with no commutativity required) and any scheme
`(X : Scheme.{u})`, this functor starts from the internal module category
over the actual `condensedRingObj Λ X`. `Mod.forget` forgets the action,
`sheafToPresheaf` exposes the underlying abelian presheaf, and evaluation at
`op (Scheme.ProEt.mk (𝟙 X))` returns its global sections and the corresponding
component on maps in `AddCommGrpCat.{u + 1}`. These render every clause of
the new node. The item's existing `.rightDerivedFunctor` supplies total
derived sections of this exact functor.

Source reread: HRS Section 3, coefficient-module and global-section convention
(in particular the discussion around (3.1)–(3.2)); the existing declaration's
source is the proof of Lemma 5.3(1). The new definition merely names ordinary
sections with the action forgotten. No cohomological claim is attached to it.
Empty schemes, zero rings, rank zero, noncommutative coefficients and arbitrary
schemes cause no extra binder: the three actual functors are defined for all
these inputs. The scheme/site universes remain u+1 for objects and u for maps.

Searches run for this new node: LeanSearch, “Global sections of internal modules
over a pulled back condensed ring by forgetting scalars and evaluating at the
terminal pro etale object” (8 generic global/section functor hits); LeanFinder,
“Forget the internal module structure of a sheaf and evaluate its underlying
abelian sheaf at the terminal object of the small pro etale site” (8 generic
SheafOfModules hits); Mathlib grep for
`condensedModuleSections|Mod\.forget.*sheafToPresheaf` (0 hits). Project rg
finds the exact definition at CondensedQcqsPushforwardContinuity.lean:127–135
and only consumers elsewhere; no upstream WeilConjectures match. DAG search
finds no definition owning it. `def-sfb-finite-derived-global-sections` concerns
A-valued sheaves and does not supply internal-module sections with actions
forgotten. Blueprint search `condensed.*sections|derived.*sections` has no
matching blueprint node; ancestor is null, preserved in the new record.

## Repair of returned H2 and second-pass self-check

The return on immutable head e7da645c097d identified the extra theorem
`lem-weil-pbc-condensed-qcqs-pushforward-continuity` as an improper statement
dependency. Replaced it by `def-sfb-condensed-module-sections`, owning exactly
the helper used. Its `existing: true` record gives the full signature verbatim
and its original module, so the public import in the item stays correct. The
source body was checked both locally and through `scompile.py --source` on the
live server. The main statement, all seven Lean declarations, all hypotheses,
all conclusions and the nine-step proof docstring are unchanged from the
reviewed delivery. The original first-pass dry run passed; this repair is
substantive DAG ownership work despite that mechanical acceptance.

Second reading by Q03 of the new node and record: Λ with `[MonObj Λ]` is exactly
a ring object on the condensed site; X is arbitrary; the internal modules,
coefficient ring, forgetful functor, terminal object, abelian-group codomain
and map evaluation all agree with the statement and source. The four cited
definition nodes supply precisely the objects used; no theorem conclusion is
used to state this definition or the item. No new mathematical assertion or
statement correction was introduced. Independent review remains with the
maintainer.
