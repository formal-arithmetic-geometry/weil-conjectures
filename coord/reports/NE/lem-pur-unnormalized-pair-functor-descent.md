## Worker report

The module `Sheaf.CategoryTheory.UnnormalizedPairFunctorDescent` states
`CategoryTheory.StageSystem.unnormalizedPairFunctorDescent`, with one `sorry` and no
new definitions. The node's statement and all dependencies are unchanged.

Hypotheses and data:

- `I : Type w`, `[Preorder I]`, `[IsDirectedOrder I]`, `[Nonempty I]` are the
  arbitrary-universe nonempty directed preorder.
- `C : I → Type u`, `D : I → Type u'`, `E : I → Type u''`, with category
  instances of respective morphism universes `v`, `v'`, `v''`, keep every object,
  morphism and index universe independent. `S`, `T`, `R` are `StageSystem`s.
  `R` is the arbitrary third system needed for composite families and either
  whiskering; choosing its category family independently imposes no size equality.
- The node's first paragraph uses the plain stage-system portion of
  `def-sf-directed-common-stage-data`, not its optional exact-stage pair datum.
  We import its recorded module `Sheaf.CategoryTheory.ExactStagePairData`, read
  the complete `ExactStagePairData` declaration and its `system : StageSystem C`
  field, and reuse the underlying upstream `CategoryTheory.StageSystem`.
  No additive, shift, exactness or pretriangulation hypotheses are introduced.
- `F : S.Morphism T` stores the functors as `F.Φ`, comparisons as `F.β`, and
  exactly the tower equation as `F.coh`. Lean composes left to right: its
  `T.map β ≫ β ≫ Φ.map assoc = assoc ≫ β` is the node's displayed equation
  with sides interchanged. It imposes no constraint on `β le_rfl` beyond this
  equation. `G : S.Morphism T` is the second coherent family.
- `η : Morphism.Hom F G` stores the natural transformations as `η.τ` and the
  node's square as `η.comm`: `U.map η ≫ c = b ≫ η`. Again this is exactly
  the displayed equation with sides interchanged.

Conclusions in their Lean order:

1. `F.functor.obj X = ⟨X.stage, (F.Φ X.stage).obj X.obj⟩` is the literal object
   formula. The existing `F.functor` has type `S.PairCategory ⥤ T.PairCategory`,
   so functoriality, including well-definedness on the quotient, is retained.
2. `F.functor.map (mkHom m hX hY f) = mkHom ... (β.hom ≫ Φ.map f ≫ β.inv)`
   is precisely the representative formula, with both endpoint comparisons.
3. `T.tr h (F.mapAt f) = F.mapAt (S.tr h f)` states literal commutation with
   further transport for every upper bound, representative and endpoint.
   `mapAt` is the existing real conjugation construction, not a new map.
4. The next two conjuncts state equality on inclusion objects and inclusion arrows.
5. `(F.ιCompFunctorIso i).hom.app x = 𝟙 _` states the identity components of
   the corresponding natural inclusion comparison (an existing natural isomorphism).
6. For every compatible `η`, `descNatTrans η` is a natural transformation between
   the stated descents. Its components are explicitly `(T.ι X.stage).map ...`.
7. `(∀ i, IsIso (η.τ i)) → IsIso (descNatTrans η)` is descent of compatible
   families of natural isomorphisms; `asIso` supplies the corresponding isomorphism.
8. Post-whiskering: for every `K : T.Morphism R` there is a compatible family
   `ω : Hom (F.comp K) (G.comp K)` whose stages are exactly
   `Functor.whiskerRight (η.τ i) (K.Φ i)`. Its descended component is
   `K.functor.map ((descNatTrans η).app X)`.
9. Pre-whiskering: for every `H : R.Morphism S` there is a compatible family
   `ω : Hom (H.comp F) (H.comp G)` whose stages are exactly
   `Functor.whiskerLeft (H.Φ i) (η.τ i)`. Its descended component is
   `(descNatTrans η).app (H.functor.obj X)`.
   These existential families have fully specified stage transformations, hence
   unique data; no arbitrary comparison or hypothesis is substituted for them.
10. Equality of stage transformations gives equality of descents, explicitly for
    all `η`, `θ`. Equality at every object is equivalent by NatTrans.ext. Together
    with the composite, identity, vertical and whiskering laws this preserves
    equations of compatible transformations, including composite families.
11. The next two conjuncts say that the identity family descends to the identity
    on all objects and arrows.
12. The next two say that `F.comp K` descends to the successive descents on
    all objects and arrows. `Morphism.comp` is the existing coherent family,
    with comparison `K.β.hom ≫ K.Φ.map F.β.hom`, exactly the node's formula.
13. The last two state `descNatTrans (Hom.id F) = 𝟙 F.functor` and preservation
    of vertical composition for every composable pair of compatible families.

Dependency declarations and sources read:

- `Sheaf.CategoryTheory.ExactStagePairData`:
  `CategoryTheory.StageSystem.ExactStagePairData`, including all its fields and
  docstring; its underlying `system` reuses the plain stage-system construction.
- `WeilConjectures.CategoryTheory.StageSystem.Basic`:
  `CategoryTheory.StageSystem`, `StageSystem.PairCategory`, `PairCategory.toStage`,
  `PairCategory.Rep`, `Rep.Rel`, `PairCategory.mkHom`, `StageSystem.tr`, `StageSystem.ι`;
  read their full signatures and the construction of the quotient/category.
- `WeilConjectures.CategoryTheory.StageSystem.Functor`: full file read, in particular
  `StageSystem.Morphism`, `Morphism.mapAt`, `Morphism.functor`, `Morphism.ιCompFunctorIso`,
  `Morphism.Hom`, `Morphism.descNatTrans`, `Morphism.Hom.id`, `Morphism.Hom.comp`,
  `Morphism.id`, `Morphism.comp`, and their formula lemmas and docstrings.
- `lem-pur-associative-stage-family-descent` is a proof dependency with no recorded
  Lean declaration at inspection, so no invented module/import is supplied for it.
  Its entire statement and proof were read. Its conclusions are already represented
  by the upstream operations used here; the docstring follows the item's five proof
  steps, with transport and whiskering calculations written out.

Edge cases checked: repeated indices, including singleton `I` with nonidentity
idempotent `T_ii`, nontrivial associators and `β_ii`, remain admitted by the exact
upstream structures. In particular no identity normalization, unitors, faithfulness
or exactness is assumed. Zero transitions are permitted; empty stage categories
make the relevant universal claims vacuous as expected. Empty `I` is expressly
excluded by the node. Independent object/morphism/index universes appear explicitly,
including the auxiliary category used for both whiskerings. The arrow equalities
are homogeneous because the published constructions have the stipulated literal
object functions; the clean compile checked this without transport casts.

Searches actually run via `/home/ubuntu/weil-launcher-all/batch2/msearch.py`:

- leanfinder: `Coherent functors and compatible natural transformations on unnormalized
  directed stage categories descend to common-stage quotient pair categories with
  transport and whiskering formulas` — 8 hits, including `Quotient.natTransLift`,
  `Quotient.comp_natTransLift`, and `Functor.IsLocallyDirected.cond`; none is this
  directed common-stage quotient construction or its whiskering theorem.
- loogle: `CategoryTheory.Functor.whiskerLeft, CategoryTheory.Functor.whiskerRight` —
  12 hits, chiefly whisker exchange/associativity and adjunction triangles; none
  states stage-system descent. The existing Mathlib whiskering operations are reused.
- grep: `StageSystem|descNatTrans|tr_mapAt`, subdirectory `CategoryTheory` — 0 hits
  in Mathlib, correctly recording that this stage-system API is project-specific.
- leansearch: `Compatible stage functors and natural transformations descend to pair
  categories of directed diagrams without unit-normalized transitions` — 8 hits,
  including `Limits.mapPair`, `NatTrans.mk`, `Square.mapFunctor` and site-plus maps;
  none supplies the unnormalized directed quotient statement.
- `rg` of `lean/WeilConjectures` located the existing StageSystem/Functor API;
  `rg` of `lean/Sheaf` found `StageSystemFunctorDescent`, `SfPackageCommonStageTransport`
  and `RationalPurityIdentityDescent`. Those sources were read: they treat a
  functor-only interface or specialized exact coefficient descents/private identity
  lemmas, not this full generic statement with independent universes and both
  whiskerings. No duplicate construction was introduced.
- `rg` for the proposed declaration in Mathlib/upstream name inventory and project
  sources found no existing declaration; `rg` for this node ID in WeilConjectures
  found none.

No statement correction or disputed statement is needed. No new or dependency nodes
are delivered. The only declaration is the single theorem above, with proof `sorry`.
Server `scompile.py` passed: sandbox 3.8 seconds, library module 1.8 seconds, no errors
or unexpected warnings.

## Second reading by NE

Self-audit of the node and file, not a claim of an independent worker review (the
brief provides an independent maintainer review and forbids starting other agents).
Checked all thirteen conclusion groups above against the node's paragraphs, and
expanded `Morphism.coh`, `Hom.comm`, `mapAt`, `comp` and both whiskerings against
its equations. The direction reversal is only Lean's left-to-right composition.
`ExactStagePairData` is imported for the dependency but its stronger structures
are not assumed: the node explicitly uses only plain stage systems. Confirmed
that the existential whiskered Hom data are uniquely specified by their stage
transformations and include compatibility, rather than assuming it. No mismatch
or edit was required after the first clean compile.
