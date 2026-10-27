## Worker report

Item: `lem-sfb-finite-pushforward-dimension-flatness`.
Module: `Sheaf.AlgebraicGeometry.FinitePushforwardDimensionFlatness`.
Declaration: `AlgebraicGeometry.Scheme.Modules.finitePushforward_dimension_flatness`.
Stage 2: the sole theorem has proof `sorry`; no new definitions or auxiliary theorems.
The node changes only in `lean`; its mathematical statement and dependency lists are unchanged.

Source read: Stacks `flat.tex`, Tag 05UF, lines 7848–7862 (comparison through the closed
immersion i_1 and finite pi_1); `coherent.tex`, Tag 02KG, affine-base-change lemma;
`algebra.tex`, Tag 00HT, flat-localization lemma; `spaces-flat.tex`, Tag 0CWS,
conditions (1)–(3). The latest blueprint unit proof
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability.proof.md` was also read: this is a supporting finite-direct-image
lemma in the inherited compactification/proper-direct-image prerequisite chain, rather
than a unit statement. No source discrepancy or statement correction was found.

Clause-by-clause reading:

- Schemes S,W,Z and their structure maps: `{S W Z : Scheme.{u}}`, `(f : W ⟶ S)`,
  `(h : Z ⟶ W)`. All universes and variables are explicitly bound, with
  `autoImplicit false` and `relaxedAutoImplicit false`.
- Locally finite type W → S: `[LocallyOfFiniteType f]`; finite h: `[IsFinite h]`.
  There are no Noetherianity, flatness, surjectivity, separation, affine, finite-presentation
  or purity assumptions on these inputs beyond the node's hypotheses.
- Finite-type quasi-coherent G: `(G : Z.Modules)` and
  `(hG : G.IsQuasiCoherentFiniteType)`. The latter is the recorded conjunction of
  `SheafOfModules.IsQuasicoherent G` and `SheafOfModules.IsFiniteType G`.
- E = h_*G: every occurrence is the actual `((pushforward h).obj G)`.
  Mathlib's `pushforward_obj_obj` identifies its sections with `Γ(G, h ⁻¹ᵁ V)` by
  reflexivity; `pushforward` is restriction of scalars along `h.toRingCatSheafHom`.
  Thus this is the section/scalar prescription in the node, not another direct image.
- E is quasi-coherent and of finite type: the first conjunct
  `((pushforward h).obj G).IsQuasiCoherentFiniteType`.
- Every scheme T → S: `∀ (T : Scheme.{u}) (g : T ⟶ S)`.
  Write W_T = `Limits.pullback f g`, p = `pullback.fst f g`, q = `pullback.snd f g`.
  Write Z_T = `Limits.pullback h p`, a = `pullback.fst h p`, b = `pullback.snd h p`.
  Z_T = Z ×_W (W ×_S T) is a canonical iterated model of Z ×_S T with its map
  b ≫ q to T. Fibre-product associativity identifies it with the unnested model;
  neither its points nor its base structure are replaced by arbitrary data.
- E_T and G_T are respectively `(tensorPullback p).obj ((pushforward h).obj G)`
  and `(tensorPullback a).obj G`, exactly the recorded tensor pullback (not the
  distinct Mathlib `Modules.pullback`). The base-change conjunct is
  `IsIso (moduleBaseChangeMap h b p a (pullback.condition h p) G)`.
  Its source is E_T and its target b_*G_T; `moduleBaseChangeMap` is the existing
  map adjoint to the actual section-normalized pullback unit. `IsIso` asserts
  precisely that canonical map is invertible, rather than choosing an arbitrary iso.
- For every w over t = q w: `∀ w : W_T`, followed by an iff between flatness
  of the actual stalk of E_T over `T.presheaf.stalk (q w)` and flatness of the
  actual stalk of G_T at every `z : Z_T` satisfying `b z = w`.
  Each flatness expression is `@Module.Flat ... _ _ (Module.compHom _ ...stalkMap...)`.
  The right base ring is `O_{T,(b ≫ q) z}`, canonically `O_{T,t}` under `b z = w`;
  this avoids a superfluous transported copy of the stalk or an arbitrary scalar action.
  The universal quantifier is vacuous when the fibre is empty.
- Every n ≥ 0: `∀ n : ℕ`. The next conjunct is an iff between the universal
  pointwise threshold conditions for G_T and E_T. Each threshold is
  `(n : Cardinal.{u}) ≤ @Algebra.trdeg (T.residueField (... x))
    (source.residueField x) _ _ (...residueFieldMap x).hom.toAlgebra`.
  This uses the canonical extension of residue fields through the actual base map.
- All étale scheme charts: for each n the second iff universally quantifies
  `(U : Scheme.{u}) (a : U ⟶ Z_T)` with `Etale a` on the left, and analogously
  V → W_T on the right. It tests the actual tensor pullback to each chart, its
  stalk, and its transcendence degree over the image in T. The identity chart is
  included, and an empty chart contributes a vacuous point condition.
- One surjective étale scheme atlas: the final conjunct, still under `∀ n`,
  quantifies arbitrary U,V and arrows a : U → Z_T, b : V → W_T with
  `Etale a → Surjective a → Etale b → Surjective b`, and asserts the iff between
  the same chartwise point conditions. It works for any chosen atlas on either
  side and hence includes the node's “one atlas” test; every scheme has its identity atlas.

Recorded statement dependencies used (their full signatures and docstrings were read):

| Node | Module and declarations |
|---|---|
| def-pc-scheme | Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType |
| def-weil-finite-integral-morphism | Mathlib.AlgebraicGeometry.Morphisms.Finite: IsFinite |
| pqf-def-coherent | Sheaf.AlgebraicGeometry.CoherentFiniteType: Scheme.Modules.IsQuasiCoherentFiniteType; its imported IsQuasicoherent and IsFiniteType |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback, pullback.fst, pullback.snd; scheme pullbacks from Mathlib.AlgebraicGeometry.Pullbacks |
| def-pc-module-pullback | Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction: public tensorPullback, tensorPullbackObj and the section-normalized adjunction |
| def-pc-scheme-module-flat-over | WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic: Scheme.Modules.IsFlatOver; the statement spells out the node's equivalent stalkwise local condition using Module.Flat |
| def-weil-residue-field | Mathlib.AlgebraicGeometry.ResidueField: Scheme.residueField, Scheme.Hom.residueFieldMap |
| def-kun-transcendence-degree | Mathlib.RingTheory.AlgebraicIndependent.Basic: Algebra.trdeg |
| def-weil-etale-morphism | Mathlib.AlgebraicGeometry.Morphisms.Etale: Etale |

Additional existing constructions: `RingedSpace.moduleStalkFunctor` from
`WeilConjectures.Algebra.Homology.ModuleStalkFunctor`; `Module.compHom` for the actual
stalk-map scalar restriction; `Scheme.Modules.moduleBaseChangeMap` from
`WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction`;
`Surjective` from `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.
All are public imports because they occur in the statement. Pointwise flatness is inlined,
so there is no duplicate of `AlgebraicGeometry.moduleFlatAt` (a helper belonging to a
separate theorem node). Likewise the scheme-point conditions here are not a second
algebraic-space `dimensionFlatCondition` definition: that existing notion acts on
small-étale module sheaves and arbitrary algebraic-space charts, whereas G here is
an O_Z-module on the Zariski site, as the node requests.

The stated proof-dependency modules and the Mathlib leaves are imported privately.
`lem-sfb-space-dimension-flatness-base-change-sheaf` has neither a Lean attachment nor
an upstream audit declaration at the time of reading, so there is no module to import
for that proof-only prerequisite. It is not needed to type this statement. The seven
DAG proof steps and the names of all their cited nodes are in the theorem docstring.

Edge cases checked before writing and reread against the signature:

- Empty Z, W or test T: point conditions quantify over the appropriate empty carriers;
  zero direct images and vacuous tests behave as in the affine calculation.
- Non-surjective finite h and empty fibres above some w: the fibre quantifier has no
  nonemptiness premise. The corresponding direct-image stalk is zero and flat.
- G = 0: zero stalks are flat, and all threshold and chart conditions hold.
- n = 0: the cardinal inequality holds for every point, giving ordinary relative
  flatness of every stalk. No positive-threshold restriction is introduced.
- n above all fibre transcendence degrees: both conditions become vacuous; finite h
  gives algebraic residue extensions and hence equal degrees along its fibres.
- Arbitrary characteristic, non-Noetherian base, disconnected tests and arbitrary
  base change: none is restricted by the binders. No affine-only test restriction.
- Atlas charts may be empty, and the atlas morphism is explicitly surjective only
  in the single-atlas clause. Identity and arbitrary étale charts are retained.

Searches for an existing statement (msearch.py outputs recorded in searches.jsonl):

- `loogle`: `AlgebraicGeometry.Scheme.Modules.pushforward, AlgebraicGeometry.Scheme.Modules.tensorPullback, AlgebraicGeometry.Scheme.Modules.IsFlatOver`. 0 hits; no matches. loogle: unknown identifier 'AlgebraicGeometry.Scheme.Modules.tensorPullback'

- `leanfinder`: `For a finite morphism of schemes pushforward of a finite type quasi coherent module preserves relative flatness at points with transcendence degree at least n after base change`. 8 hits; AlgebraicGeometry.Flat.isStableUnderBaseChange, AlgebraicGeometry.Flat, AlgebraicGeometry.Flat.instHasRingHomPropertyFlat, Algebra.FormallyUnramified.flat_of_restrictScalars, AlgebraicGeometry.Flat.flat_appLE, AlgebraicGeometry.Scheme.Hom.flat_appLE, AlgebraicGeometry.flat_iff, RingHom.Flat.isStableUnderBaseChange. 

- `grep`: `pushforward.*[Ff]lat|[Ff]lat.*pushforward|dimension.*[Ff]lat|[Ff]lat.*dimension` in `AlgebraicGeometry`. 0 hits; no matches. 

- `leansearch`: `Finite pushforward of a quasi coherent module preserves flatness over a base and commutes with base change`. 8 hits; RingHom.Flat.isStableUnderBaseChange, Module.Flat.isBaseChange, AlgebraicGeometry.Flat.isStableUnderBaseChange, Module.Flat.of_isLocalizedModule, Algebra.FormallyUnramified.flat_of_restrictScalars, PresheafOfModules.pushforward₀_obj, Module.FaithfullyFlat.instTensorProduct, Module.Flat.localizedModule. 

The LeanFinder/LeanSearch hits cover flat morphisms, scalar restriction, localization
and base change separately, not this finite-direct-image dimension-threshold theorem.
The Loogle query reports no project tensorPullback identifier because its index is
Mathlib-only; its actual project declaration was then read directly.
Direct `rg` searches in `lean/WeilConjectures` and `lean/Sheaf` for
`dimension.*[Ff]lat|[Ff]lat.*[Dd]imension|finite.*pushforward|pushforward.*finite`
found the existing affine-base-change theorem, finite-pushforward finite-type theorem,
`SpaceDimensionFlatCondition`, `smoothTopDimensionFlatCondition`, and `moduleFlatAt`.
None states all of this node's conclusions. Searching the item id in
`lean/WeilConjectures` returned no match. Searches for the new declaration name in
Mathlib/source/project and `dag/lean_names_upstream.json` found no collision.
No new notion requires a new definition node, and no recorded dependency requires repair.

Validation: final scompile.py passed in sandbox mode (16.1 s) and the actual library
module (8.6 s), with exit 0 and no warnings. Required delivery dry run follows.

## Second reading by Q29

Performed by the same worker as a separate pass, with the original node and final Lean
signature open. The dispatcher explicitly forbids starting a second agent; the maintainer
performs the independent review after delivery.

I checked the scope of every quantifier and conjunction: finite-type quasi-coherence
is before the universal test T, canonical base change and stalkwise reflection are
inside it, and all three dimension tests are inside `∀ n`. The atlas clause uses
both étale and surjective for each chosen atlas and does not assume h surjective.
The original Zariski module G, its tensor pullbacks and the actual pushforward appear
throughout; no replacement étale sheaf or arbitrary isomorphism is assumed. On a fibre
`b z = w`, the composite base local ring on the right is the same as at `q w`.
Both transcendence-degree algebras come from the residueFieldMap for those same
base morphisms. The iterated pullback is the canonical fibre product of the node.

The clause table above covers every hypothesis and conclusion of the node. The
independent all-chart equivalence and the equivalence for arbitrary single atlases
both remain present, including identity and empty charts. No mathematical mismatch
was found. The first compile found an incorrect guessed import path
`Mathlib.AlgebraicGeometry.Morphisms.Surjective`; source inspection located the actual
class in `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, and the import was fixed.
No statement correction, dependency module or new node was necessary.

Compiler elaboration repair: scheme fibre products are qualified `Limits.pullback`
inside `Scheme.Modules` to avoid resolving `Modules.pullback`. The equality proof
`pullback.condition` receives its implicit `(f := h) (g := pullback.fst f g)`
arguments by name. No mathematical content was changed.

The final compile also fixes the category explicitly in every scheme fibre-product
term: `Limits.pullback (C := Scheme.{u}) ...`. Without it, a type-position
pullback can be inferred in `Type`, giving a different carrier. The explicit
category retains exactly schemes and their actual points, with no size restriction.
