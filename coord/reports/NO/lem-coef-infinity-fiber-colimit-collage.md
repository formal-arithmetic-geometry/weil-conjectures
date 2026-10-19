# Fiber colimit collage — stage 2

## Worker report

The delivery states `CategoryTheory.fiber_colimit_collage` in `Sheaf.CategoryTheory.FiberColimitCollage`. Its only theorem proof is `sorry`. The collage, inclusions, projection, and canonical fiber prisms are explicit constructions. No target or informal statement is changed. The inherited draft was incomplete: it concluded only that an extension existed. I repaired it to assert that every induced fiber cocone is colimiting, and replaced an intermediate component-edge-only formulation by equality of the entire coherent transformation in all simplicial degrees.

I read the whole item, its five proof steps, its definition dependency and that dependency's Lean declarations. I also read `FinalIndexColimit.lean` and its node for the existing cocone-transformation projection, and `EnhancedFunctorConeCalculus.lean` for the landed proof dependency. The online source statements were opened: [Kerodon 02ZW, Proposition the project server](https://kerodon.net/tag/02ZW), [02ZP, Proposition the project server](https://kerodon.net/tag/02ZP), and the directly applicable [02ZU, Lemma the project server](https://kerodon.net/tag/02ZU). With target base a point, they give the stated assembly of fiber colimits. No source correction is required.

Hypothesis and clause correspondence:

- A small ordinary base category is `{I : Type u} [Category.{u} I]`, and a strict functor to small categories is `U : I ⥤ Cat.{u, u}`. The common universe `u` contains all the small categories and the target simplicial set, following the enhanced-diagram dependency's convention; `u` is arbitrary.
- The Grothendieck category is Mathlib's `Grothendieck U`, whose objects, homs, composition, projection and canonical fiber inclusion were read in source. In particular its fiber inclusion is `Grothendieck.ι U i`; it does not replace a strict fiber by a comma category.
- The node's collage is `Collage I U`, with object type `Sum (Grothendieck U) I`. `CollageHom.left` and `.right` retain exactly the original homs; `.mixed` has type `X.base ⟶ Y`; there is no right-to-left constructor. `instCategoryCollage` composes mixed arrows using base composition, exactly as in the node. Its category-law fields have actual proofs, as needed for construction data.
- `collageProjection` extends the Grothendieck projection by the identity on the right. `collageLeft` and `collageRight` are the two full inclusions. `collageFiber U i` is `Grothendieck.ι U i ⋙ collageLeft`, and `collageFiberMap` is its nerve map.
- A coherent diagram in a quasicategory is `{E : SSet.{u}} [E.Quasicategory]` and `Q : nerve (Grothendieck U) ⟶ E`. The hypothesis `hcolim` says, for each `i`, that `coconeCategory (nerveMap (Grothendieck.ι U i) ≫ Q)` has a vertex satisfying the dependency's `IsColimiting`.
- The requested extension is `∃ Qbar : nerve (Collage I U) ⟶ E`, with exact restriction `nerveMap collageLeft ≫ Qbar = Q`.
- For each `i`, the conclusion supplies a vertex `c` in `coconeCategory (collageFiberMap U i ≫ Qbar)`. The preceding restriction equation identifies that diagram with the original fiber restriction of `Q`. The apex equation is `c.1.1 = Qbar.app ... (ComposableArrows.mk₀ (Sum.inr i))`, and the next clause is `IsColimiting (collageFiberMap U i ≫ Qbar) c`.
- The final equation is `coconeHomotopy (collageFiberMap U i ≫ Qbar) c = collageFiberPrism U i ≫ Qbar`. This identifies the whole coherent transformation, not merely the individual component edges. `collageFiberCocone` has component the actual mixed arrow labeled `𝟙 i`; Mathlib's `ComposableArrows.mk₁`, flip and uncurrying construct its ordinary prism. `collageFiberPrism` maps a simplex paired with a monotone time map to the resulting chain in that prism. Its zero end is the fiber inclusion, its one end is constant at `Sum.inr i`, and all mixed arrows are exactly those labeled `𝟙 i`.
- No preservation of colimits by transition functors or by `Q` is assumed. There is no extra nonemptiness, filteredness, finiteness or injectivity assumption.

Dependency interfaces used:

- `def-cbc-enhanced-diagrams-cones`: module `Sheaf.CategoryTheory.EnhancedDiagramsCones`, especially `SSet.Enhanced.coconeCategory`, `SSet.Enhanced.IsColimiting`, and Mathlib's `SSet.Quasicategory` and ordinary nerve. `IsColimiting` is initiality in the exact coherent comma category specified by that node.
- `lem-coef-infinity-final-index-colimit`: module `Sheaf.CategoryTheory.FinalIndexColimit`, declaration `SSet.Enhanced.coconeHomotopy`. This already landed node is added to `stmt_deps` solely to reuse the real projection from an existing comma cocone to its transformation; no theorem of that node is assumed or restated. Its full definition was read. This is an allowed addition of an existing landed declaration under brief-stage2 §5.
- `lem-cbc-enhanced-functor-cone-calculus`: the recorded module `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus` is imported privately as the available proof dependency. The remaining proof dependencies have no recorded Lean module in the shared snapshot, so no unavailable import is invented; stage 3 can add their imports when stated. Neither imported theorem node has a dependency path back to this item.
- Mathlib constructions reused directly include `Grothendieck`, `Grothendieck.ι`, `nerve`, `nerveMap`, `ComposableArrows.mk₀`, `ComposableArrows.mk₁`, `Functor.prod'`, `Functor.flip`, and `Functor.uncurry`. The collage and its canonical maps are objects introduced in this item's own statement, so their helper declarations belong to this module and are listed in `lean.declarations`; no independent notion is added.

Edge cases checked against the actual definitions:

- If `I` is empty, both collage parts are empty and all fiber conditions are vacuous; the empty simplicial map gives the required extension.
- If `U(i)` is empty, its cocone category has varying apices and only the required constant transformation, so a colimiting cocone requires an initial object. The separate apex equation is essential here: equality of transformations with empty domain alone would not specify the apex.
- If all fibers are empty, the extension must be a coherent diagram of initial objects on the right copy of `I`; the hypothesis is exactly what the source needs.
- A one-object base recovers the ordinary operation of adjoining a colimit cone. Nontrivial endomorphisms and repeated vertices are retained in the hom constructors and in the prism formula; no thinness or poset restriction is imposed.
- For a nonempty fiber the canonical component at `x` is the mixed arrow `(i,x) ⟶ i` labeled by the base identity. Higher coherence is fixed by the equality of simplicial maps, not by an arbitrary choice of edges.

Fresh searches performed through the prescribed wrapper:

- LeanFinder: `Homotopy coherent fiberwise colimits of a strict Grothendieck construction extend to the collage with colimiting fiber cocones` — 8 hits, including `CategoryTheory.Limits.fiberwiseColimit`, `fiberwiseColim`, `coconeOfCoconeFiberwiseColimit` and `coconeFiberwiseColimitOfCocone`. I read `Mathlib/CategoryTheory/Limits/Shapes/Grothendieck.lean`; its target `H` has an ordinary `Category` instance and its input is an ordinary functor. It does not state the arbitrary-quasicategory result here.
- Loogle: `"Quasicategory", "Cocone"` — 0 hits.
- Mathlib grep: `collage|relativeJoin|cocartesian|colimit` in `AlgebraicTopology/Quasicategory` — 0 hits.
- LeanSearch: `Coherent diagrams in a quasicategory on a Grothendieck construction extend to a collage using fiber colimits` — 8 ordinary-category colimit/Kan-extension hits, without the required coherent extension statement.
- Read-only `rg` in Mathlib, `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for the proposed declaration names and collage/Grothendieck terminology found no existing collage or exact theorem. A separate search for the item ID in `WeilConjectures` found none. Existing ordinary categorical joins have a unique arrow between any left and right object, so they are not the base-hom collage for arbitrary `I` and were not substituted for it.

The module compiles cleanly through `scompile.py` with the default per-file limit, including the module-system/library check. The module and every helper have source and blueprint docstrings, and the theorem docstring records the complete five-step proof plan with the matching DAG dependencies. Only `lean` and the authorized addition to `stmt_deps` differ from the shared node. No `STATEMENT-DISPUTED` issue, new definition node, or dependency repair is needed. The independent second reading and actual delivery remain the next worker's responsibility.

## Second reading by NO

I independently opened the sandbox node and the complete module, the shared node,
the statements and Lean records of both statement dependencies and all four proof
dependencies, and the actual definitions in `EnhancedDiagramsCones.lean`,
`FinalIndexColimit.lean`, `EnhancedFunctorConeCalculus.lean`, and Mathlib's
`CategoryTheory/Grothendieck.lean`. There is no repair note for this item. There
are no new definition nodes or delivered dependency modules to audit under H12/H13.

Source check: I read [Kerodon 02ZW](https://kerodon.net/tag/02ZW),
[02ZP](https://kerodon.net/tag/02ZP), and [02ZU](https://kerodon.net/tag/02ZU)
online myself. The first gives existence from fiber colimits, the second identifies
the resulting fiber restrictions as colimits, and the lemma retains chosen fiber
cones exactly. Specialize the target base to a point and its isofibration to the
quasicategory's map to that point. The nerve of the displayed Grothendieck
projection is cocartesian, using the arrows `(f, identity)`. Thus the source adds
no preservation, nonemptiness, or finiteness hypothesis. The explicit collage is
the corresponding relative join. No correction of the informal node is needed.

My object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

1. Small ordinary category `I`: `{I : Type u} [Category.{u} I]`. Strict functor
   to small categories: `(U : I ⥤ Cat.{u, u})`. These use the fixed sufficiently
   large universe convention of `def-cbc-enhanced-diagrams-cones`; `u` is arbitrary.
   No poset, skeletal, finite, or nonempty restriction is introduced. Pass.
2. `K = ∫ U`, with objects `(i,x)`, homs `(f,alpha)`, and the stated composition:
   Mathlib `Grothendieck U`. I read `Grothendieck.Hom`, `comp`, `forget`, and `ι`;
   the fiber component of composition is the transported composite in the node,
   with equality transports for a strict Cat-valued functor. Pass.
3. Projection `p`: Mathlib's base projection on `Grothendieck U`, extended by
   `collageProjection`. Its object/map fields return the base object/base arrow
   on the left, and the object/arrow itself on the right. Pass.
4. Disjoint full subcategories `K` and `I`: `Collage I U` is their `Sum`.
   `CollageHom.left` and `.right` give precisely their original homs, `.mixed`
   gives `X.base ⟶ Y`, and no constructor goes from right to left.
   `instCategoryCollage` composes the two mixed cases using `f.base ≫ g` and
   `f ≫ g`, respectively. `collageLeft` and `collageRight` are the canonical
   inclusions. No arrows are added or identified. Pass.
5. Coherent diagram into a quasicategory: `{E : SSet.{u}} [E.Quasicategory]` and
   `(Q : nerve (Grothendieck U) ⟶ E)`. These are the dependency's exact notions,
   rather than ordinary target functors or a nerve-only target. Pass.
6. Fiber restriction `Q_i`: `nerveMap (Grothendieck.ι U i) ≫ Q`. Its inclusion
   has base identity and the original fiber arrow; this is the strict fiber
   over `i`, including when `I` has nontrivial endomorphisms. Pass.
7. Every fiber has a colimit: `hcolim` quantifies `∀ i : I, ∃ t` in degree zero
   of `coconeCategory Q_i`, with `IsColimiting Q_i t`. The dependency defines
   this as initiality in its coherent comma category, retaining varying apices
   and all compatibility simplices. No chosen cocone is an extra input. Pass.
8. An extension exists and restricts to exactly `Q`: `∃ Qbar : nerve (Collage I U)
   ⟶ E, nerveMap collageLeft ≫ Qbar = Q ∧ ...`. The existential precedes the
   universal quantifier over fibers, as required. Pass.
9. For every `i` the cocone has apex `Qbar(i)`: the witness `c` is a vertex of
   `coconeCategory (collageFiberMap U i ≫ Qbar)`, and `c.1.1` is explicitly
   equated to `Qbar.app ... (ComposableArrows.mk₀ (Sum.inr i))`. The extension
   equation identifies its boundary with the preceding `Q_i`. Pass.
10. The cocone is induced by precisely the identity-labeled mixed arrows:
    `collageFiberCocone.app x` is `CollageHom.mixed (𝟙 i)`.
    `collageFiberPrismFunctor` uses `ComposableArrows.mk₁`, `.flip`, and
    `Functor.uncurry`; its time-zero restriction is `collageFiber U i` and its
    time-one restriction is constant at `Sum.inr i`. `collageFiberPrism` applies
    this functor to the product of the fiber chain and the monotone time map.
    The conclusion equates this whole prism after `Qbar` with the existing
    `coconeHomotopy ... c`. I read that projection: it uncurries the actual
    transformation coordinate of the comma vertex. Thus this fixes the entire
    coherent cocone, rather than just its component edges. Pass.
11. Each such induced cocone is colimiting: the conjunction contains
    `SSet.Enhanced.IsColimiting (collageFiberMap U i ≫ Qbar) c` for every `i`.
    There is no claim of a global colimit and no assumption that a transition
    functor or `Q` preserves any colimit. Pass.

Edge cases: empty `I` leaves both sum summands and every fiber condition empty.
An empty fiber requires an initial object of `E` through `hcolim`; equality of
the empty-domain prism alone would not fix its apex, which is why I checked the
separate apex equation. All-empty fibers and an empty target are included with
exactly the resulting existence conditions. An initial/zero object, when present,
is not excluded. Singleton categories, identity arrows, repeated vertices, and
nontrivial base endomorphisms survive the explicit hom and chain constructions.
There is no integer parameter or characteristic restriction here; degree zero
and all higher degrees occur in the actual simplicial maps. All objects and homs
are small in the dependency's common ambient universe, with no unbound universe
or auto-implicit binder. Pass.

Independent H4 searches, using different queries through the prescribed wrapper:

- LeanFinder: `Homotopy coherent left Kan extension from an opfibration to its
  cylinder with prescribed universal fiber cocones` returned eight cylinder,
  realization, and ordinary Kan-extension hits; none has this signature.
- Loogle: `"SSet", "IsColimiting"` returned zero hits.
- Grep: `mappingCylinder|relativeJoin|fiberwiseColim` returned ordinary fiberwise
  colimit declarations. I opened `Mathlib/CategoryTheory/Limits/Shapes/Grothendieck.lean`:
  its target `H` has an ordinary `Category` instance, and its diagram is an
  ordinary functor. This does not supply the arbitrary-quasicategory theorem.
- LeanSearch: `Extend an infinity category valued diagram from a Grothendieck
  category to its mapping cylinder using colimits on each fiber` returned eight
  ordinary categorical colimit/Kan-extension hits, with the same mismatch.
- Direct read-only `rg` for `collage|relative.?join|mapping.?cylinder` and the
  proposed declaration names in Mathlib, upstream `WeilConjectures`, the project's
  `lean/Sheaf`, and `dag/lean_names_upstream.json` found no exact declaration or
  duplicate collage construction. I opened the nearby project's
  `FinitePosetKanExtension.lean`: its main theorem assumes finite partial orders
  and an order embedding, and does not state this arbitrary-base collage lemma.

H5/H6/H8/H9: all helpers have real construction data; their proofs only discharge
the laws needed to form these constructions. The sole theorem is postponed by
one `sorry`. Every helper and the theorem have source/blueprint docstrings. The
theorem docstring follows all five node steps and names their dependencies.
The recorded available proof module is imported; the other three proof nodes
have no recorded Lean module in the shared snapshot. There are no private
notions, local instances, local notation, hidden `let`/`show` statement binders,
or over-100-character Lean lines. The node's `lean.statement` is verbatim equal
to the source signature. Comparing node records confirms only `lean` and the
authorized addition of the landed `lem-coef-infinity-final-index-colimit` to
`stmt_deps` changed; its helper is reused rather than duplicated.

Mismatches found in this second reading: none. I retained the Lean and node
unchanged and appended this independent audit. The inherited worker's repairs
already restore both colimitingness and the full induced coherent cocone.
`scompile.py NO lem-coef-infinity-fiber-colimit-collage
lean/Sheaf/CategoryTheory/FiberColimitCollage.lean` passed both sandbox and library
checks cleanly, within the default per-file limit (6.3 s and 4.4 s).
