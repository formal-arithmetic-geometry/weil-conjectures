## Worker report

The module `Sheaf.AlgebraicGeometry.RelationOpenLocusDescent` states
`AlgebraicGeometry.relation_open_locus_descent`. Its sole theorem has proof `sorry`.
No definition, helper theorem, dependency repair, or statement correction is needed.
The node copy changes only `lean`.

Read the statement and all four proof steps of the item, the statement and recorded
interfaces of all six statement dependencies, the recorded proof dependencies,
and the actual source declarations. Read Stacks More on Groupoids Tag 04LH,
`lemma-local-source`, including its proof, and Groupoids Tags 0233 and 03C6,
`lemma-equivalence-groupoid` and `lemma-diagram-pull`. The assignment abstracts the
isomorphism-invariant largest-open construction in 04LH; its hypotheses are exactly
the compatibility properties the proof uses. The present item is its stated
specialization to the identity base map and flat locally finitely presented maps.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; `universe u` is explicit, and every
  scheme over it is an object of `Over S`. All variables are bound and
  `set_option autoImplicit false` enforces this. There are no sites or derived
  categories in this statement, so the recorded size convention requires no
  additional size assumptions.
- The open assigned to every flat locally finitely presented `f : X ⟶ Y` is
  `D : ∀ {X Y : Over S} (f : X ⟶ Y), Flat f.left →
  LocallyOfFinitePresentation f.left → X.left.Opens`. Proof arguments restrict
  the domain exactly as required, without extending the assignment to other
  morphisms. Proof irrelevance identifies different witnesses of these properties.
  Mathlib's canonical open subscheme of an open gives its full restricted
  structure sheaf; an open is not an arbitrary subscheme with the same support.
- Isomorphism invariance is `hiso`. Both horizontal source/target identifications
  `a : X' ≅ X`, `b : Y' ≅ Y` are isomorphisms over `S`, and
  `a.hom ≫ f = f' ≫ b.hom` asserts they identify the arrows. Its conclusion is
  exactly `D f' hf' hlfp' = a.hom.left ⁻¹ᵁ (D f hf hlfp)`.
- Cartesian base-change compatibility is `hbase`. The arrows are
  `f : X ⟶ Y`, `g : Y' ⟶ Y`, `f' : X' ⟶ Y'`, `p : X' ⟶ X`.
  `IsPullback p.left f'.left f.left g.left` is their scheme pullback square.
  The arguments `hf`, `hlfp`, `hg`, `hglfp`, `hf'`, `hlfp'` impose flatness
  and local finite presentation on precisely `f`, `g`, `f'`. No property is
  required of `p`. The conclusion `D f' hf' hlfp' = p.left ⁻¹ᵁ (D f hf hlfp)`
  is equality under pullback along the source projection. An arbitrary cartesian
  representative is allowed, as the node requires.
- The relation schemes are `{V R : Over S}` and its two projections are
  `s t : R ⟶ V`. This pair uniquely gives the node's map to `V ×[S] V`
  by the universal property of that product; the product map need not be separately
  supplied as redundant data.
- For every test scheme over the base, `hinj` says that
  `r ↦ (r ≫ s, r ≫ t)` is injective on `T ⟶ R`.
- For every such test scheme, `hrel` says `Equivalence` of
  `fun a b : T ⟶ V ↦ ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b`.
  Thus the image on sections is exactly an equivalence relation, with reflexivity,
  symmetry, and transitivity all present. This is also the encoding already used
  by the landed consumer `exists_flat_relation_cm_open`; it is not a new definition
  of a relation or groupoid.
- `[hs : Flat s.left]`, `[ht : Flat t.left]`,
  `[hslfp : LocallyOfFinitePresentation s.left]`, and
  `[htlfp : LocallyOfFinitePresentation t.left]` are precisely the four geometric
  assumptions on the projections. None requires surjectivity as an extra assumption.
- The specified identity section is `e : V ⟶ R`, with
  `hes : e ≫ s = 𝟙 V` and `het : e ≫ t = 𝟙 V`. The node explicitly introduces
  this morphism; it is not an arbitrary unconstrained map. Reflexivity at `T = V`
  supplies it and `hinj V` makes it unique. Therefore supplying it with these
  identities does not strengthen the node's hypotheses. No flatness or local
  finite presentation is imposed on `e`.
- The conclusion is literally
  `D s hs hslfp = t.left ⁻¹ᵁ (e.left ⁻¹ᵁ (D s hs hslfp))`.
  The inner open is the node's `W = e⁻¹(D_s)`; the outer inverse image is
  `t⁻¹(W)`. No existential weakening of the specified `W` is used. Equality in
  `R.left.Opens` identifies the canonical open subschemes and their restricted
  structure sheaves, not just their sets of points.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `Scheme.Hom`, `Scheme.Opens`, and the global inverse-image notation.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`,
  the recorded notion underlying canonical open subschemes.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat` and
  `Flat.isStableUnderBaseChange` (the latter is the matched proof dependency).
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` and
  `locallyOfFinitePresentation_isStableUnderBaseChange`, the used clause (3)
  of the permanence proof dependency. The recorded QuasiSeparated module is
  also imported privately for that dependency's full matched interface.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback` and its projection/universal-property API;
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs`:
  `CategoryTheory.IsPullback`, the same fibre-product universal property on a square.
- `Mathlib.CategoryTheory.Comma.Over.Basic`: `CategoryTheory.Over` and its
  objects, arrows, and underlying maps.
- Proof imports: `WeilConjectures.Mathlib.CategoryTheory.Yoneda`,
  `CategoryTheory.bijective_yoneda_app_id`;
  `Sheaf.AlgebraicGeometry.GroupoidScheme`, `AlgebraicGeometry.IsGroupoidScheme`;
  `Sheaf.AlgebraicGeometry.GroupoidSourcePullbackTranslation`,
  `AlgebraicGeometry.groupoid_source_pullback_translation`.
  Their complete signatures and docstrings were read. The theorem docstring
  reproduces the four-step proof, naming all proof dependencies. All postponed
  proof work belongs to this one DAG node.

Edge cases checked before writing:

- Empty `V`: an `R ⟶ V` has empty source, and the asserted open equality is valid.
- Diagonal relation `R = V`, `s = t = e = id`: the conclusion is the identity
  inverse-image equality for any assigned open, without forcing it to be empty or full.
- The indiscrete relation `R = V ×[S] V` when both projections are flat and locally
  finitely presented: the identity is the diagonal, which need not itself be flat;
  it is correctly excluded from the domain requirements of `D`.
- Constant empty and constant whole-open assignments satisfy both compatibility
  hypotheses and the conclusion. There is no inhabitedness, nonemptiness, affine,
  Noetherian, quasi-compactness, or characteristic assumption.
- Test schemes have the same universe as the relation, so `T = V`, `T = R`, and
  all required pullbacks are available; no independently smaller test universe
  could make the relation hypotheses vacuous.

Searches made, with the prescribed `msearch.py Q21` wrapper:

- LeanFinder: "An isomorphism invariant source open locus for flat locally
  finitely presented scheme morphisms compatible with flat locally finitely
  presented base change descends through a scheme equivalence relation".
  Eight hits, headed by `UniversallyOpen.of_flat`, flatness base-change stability,
  and morphism-property descent; none treats descent of an assigned open locus.
- Loogle: `AlgebraicGeometry.Flat, AlgebraicGeometry.LocallyOfFinitePresentation`.
  Twelve hits concern universal openness, etaleness, flat descent, and fppf
  precoverings; none states this node's equality.
- Mathlib grep: `groupoid.*[Ll]ocus|[Ll]ocus.*groupoid|[Ee]quivalence[Rr]elation.*[Oo]pen`
  in `AlgebraicGeometry`: zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  `relationOpenLocus`, `sourceOpenLocus`, and equivalence-relation names:
  only the consumer's proof docstring references this node; other hits concern
  unrelated finite locally constant sheaves. Broader inspection found the useful
  relation-on-sections encoding in `FlatRelationCMOpen.lean`, not this theorem.
- Exact-name `rg` over Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` for
  `relation_open_locus_descent|RelationOpenLocusDescent`: no existing declaration.
  The prescribed node-id grep in `lean/WeilConjectures` also gives no match.

No STATEMENT-DISPUTED issue or node fault was found. The initial module compiled
cleanly on the server with `scompile.py`; the delivery checks recompile the final
module after adding the private permanence-dependency import.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
