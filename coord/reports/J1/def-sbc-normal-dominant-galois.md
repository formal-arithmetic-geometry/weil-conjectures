## Worker report

`Sheaf.AlgebraicGeometry.NormalScheme` adds `AlgebraicGeometry.IsNormalScheme` and
`AlgebraicGeometry.Scheme.GaloisCover.deckGroup`. The other notions of the bundled
blueprint definition already have declarations and are not redeclared.

- Integral: `AlgebraicGeometry.IsIntegral S` in
  `Mathlib.AlgebraicGeometry.Properties`; its `isIntegral_iff_irreducibleSpace_and_isReduced`
  identifies it with nonempty, reduced, irreducible. Dependency:
  `def-pc-integral-scheme` (`mathlib_match`, no Lean record).
- Normal: `IsNormalScheme S` is `IsIntegral S` and, for **every** `s : S`, both
  `IsDomain (S.presheaf.stalk s)` and `IsIntegrallyClosed (S.presheaf.stalk s)`.
  `IsIntegrallyClosed` means integrally closed in the fraction field of a domain.
- Dominant: `AlgebraicGeometry.IsDominant f` in
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, whose `denseRange` field is the
  density of the image in the target.
- Galois cover: `AlgebraicGeometry.Scheme.GaloisCover G C` in
  `WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor` has a finite etale surjective
  map `π`, a group action over `C`, and `isIso_sigmaDesc` for simple transitivity.
  Each action map is an automorphism since its inverse is the action by the group inverse.
  Its source docstring explains that the quotient condition follows from the torsor
  condition. No connectedness of the total space is imposed.
- Deck group: `Scheme.GaloisCover.deckGroup T := Aut (Over.mk T.π)` is exactly the group
  of scheme automorphisms of the total space over `C`; it does not require them to
  commute with the given `G` action.
- Geometrically connected fibres: `AlgebraicGeometry.GeometricallyConnected f` in
  `Mathlib.AlgebraicGeometry.Geometrically.Connected` is the geometric connectedness
  condition on every base change by a field-valued point of the target. Its fibre
  characterization is `GeometricallyConnected.iff_geometricallyConnected_fiber`.
- Geometrically reduced fibres: `AlgebraicGeometry.GeometricallyReduced f` in
  `Mathlib.AlgebraicGeometry.Geometrically.Reduced` has the analogous condition for
  `IsReduced`; `GeometricallyReduced.iff_geometricallyReduced_fiber` gives the fibre form.

`def-weil-pbc-scheme-conventions` is a convention node with `lean.existing: true` and
no declaration; the relevant scheme and morphism declarations above instantiate it.
The empty scheme is not integral and therefore not normal. The identity morphism is
dominant. The trivial group and disconnected trivial torsors remain allowed. A
separably closed field extension is included among the field extensions quantified
over by Mathlib's geometric predicates; the base change to an algebraic closure is
the standard equivalent test. No characteristic restriction appears.

Searches: `msearch.py` LeanFinder with “normal integral schemes dominant scheme
morphisms finite etale Galois cover torsor geometrically connected geometrically
reduced fibres” found only normalization results, no combined declaration;
`msearch.py` Loogle on `IsNormal, IsDominant, GaloisCover, GeometricallyConnected,
GeometricallyReduced` returned unknown `IsNormal`; `msearch.py` grep in
`AlgebraicGeometry` returned uses of the geometric predicates and dominance but no
normal-scheme definition. `rg` of Mathlib and `WeilConjectures` found the four
existing notions above, the source Galois cover, but no normal-scheme or deck-group
definition. `rg` of `lean/Sheaf` found no matching scheme declarations; searching
`def-sbc-normal-dominant-galois` in the source checkout found only docstring uses
in `EtaleTorsor` and `EtaleTorsorSpreading`.

Server compile: clean, exit code 0.

## Earlier second reading (a previous round; superseded)

Pending the independent second reader. The worker's clause-by-clause account above
is not an independent reading and must be checked before delivery.

## Second reading by J1

I independently opened the item node, its two dependency nodes, the delivered Lean,
Mathlib's recorded declarations, and the slopmaster2 Galois-cover declaration.
The item's source is a blueprint definition, not a Stacks tag: I read its original
Markdown on the server (the local literature checkout contains only indexes).
There are no ambient Noetherian, characteristic, separatedness, connectedness,
or base-field assumptions in that source. For the integral dependency I also read
Stacks `properties.tex`, Definition 01OK (`definition-integral`) and Lemma 01ON
(`lemma-characterize-integral`), on the server. Neither assumes finiteness or
Noetherian hypotheses. There are no new nodes, dependency modules, or statement
corrections in this delivery; the item statement remains unchanged.

The source's extra deck-group assertion and duplicate geometric-point wording
were already removed by the stage-1 review recorded in the node. I reviewed the
current node's clauses, rather than silently restoring those assertions.

The objects, hypotheses and clauses, with their Lean renderings, are:

| Node clause | Lean rendering and verdict |
| --- | --- |
| A scheme `S`, nonempty, reduced and irreducible | `Scheme.{u}` and `IsIntegral S`. I read `Properties.lean:240` and `isIntegral_iff_irreducibleSpace_and_isReduced`: the existing dependency `def-pc-integral-scheme` is exactly this notion. Pass. |
| Normal means integral AND every local ring is an integrally closed domain | The unchanged `IsNormalScheme S` has `IsIntegral S ∧ ∀ s : S, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s)`. `IsIntegrallyClosed` is integrally closed in `FractionRing`; the separate domain conjunct ensures this is a fraction field. Pass. |
| A morphism `f : X → Y` is dominant iff its image is dense | Existing `AlgebraicGeometry.IsDominant f`, `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`, has precisely `denseRange : DenseRange f`. No scheme-theoretic dominance or integrality is substituted. Pass. |
| A group `G`, schemes `Z,C`, and a finite etale cover `π : Z → C` | New `Scheme.GaloisCoverAction (G : Type v) [Group G] (C : Scheme.{u})` introduces `Z`, `π`, `IsFinite π`, `Etale π`, and `Surjective π`. Surjectivity is inherent in the source's torsor and quotient conditions. The formerly used `Scheme.GaloisCover` additionally required `Finite G`: repaired. |
| `G` acts over `C` by automorphisms | `smul`, `smul_π`, `one_smul`, and `mul_smul`. The last is the left-action law in categorical order. Taking the inverse group element gives both inverse equations, hence each action map is an isomorphism, therefore finite etale. No action is required to be faithful on an empty total space. Pass. |
| The quotient is `Z/G ≅ C` | The `quotient` field: for every scheme `W` and invariant morphism `f : Z ⟶ W`, a unique `q : C ⟶ W` satisfies `π ≫ q = f`. This is the scheme quotient universal property for the given action and quotient morphism. Pass. |
| The action is simply transitive on every geometric fibre | `simply_transitive` quantifies over every algebraically closed field `Ω`, every pair `x,y : Spec Ω ⟶ Z` over the same base point, and a unique `g : G` with `x ≫ smul g = y`. Algebraically closed field-valued lifts identify the points of the finite etale geometric fibre; surjectivity ensures each such fibre is nonempty. Thus the unique-element condition is exactly free and transitive. Pass. |
| Deck group is ALL automorphisms over `C` | Generalized `Scheme.Hom.deckGroup π := Aut (Over.mk π)`. An automorphism in `Over C` is exactly a scheme automorphism of `Z` over `C`. This is not the group of action-equivariant automorphisms. Pass. |
| Every point `s : S` has geometrically connected fibre over `κ(s)` | Existing `GeometricallyConnected f`, `Mathlib.AlgebraicGeometry.Geometrically.Connected`, and its `iff_geometricallyConnected_fiber` give exactly the pointwise fibre condition. `geometrically` quantifies over field-valued base changes. Testing all separably closed extensions is equivalent: algebraic closures are included, connectedness descends along field extension, and purely inseparable extensions are universal homeomorphisms. Pass. |
| Every point `s : S` has geometrically reduced fibre | Existing `GeometricallyReduced f`, `Mathlib.AlgebraicGeometry.Geometrically.Reduced`, and `iff_geometricallyReduced_fiber`. Testing all separably closed extensions includes an algebraic closure; reducedness descends along field extension and geometric reducedness can be tested over that algebraic closure. No perfectness or characteristic assumption is added. Pass. |
| Scheme/morphism conventions | `def-weil-pbc-scheme-conventions` fixes no separate definition. I read its record and use the named Mathlib primitives, including `IsFinite`, `Etale`, `Surjective`, and schemes. No private variants of these notions are introduced. Pass. |

Edge cases: the empty scheme is excluded from integrality and normality by
`IsIntegral.nonempty`. The identity on the empty scheme is dominant (its image
is dense in the empty target). Fibre predicates over an empty base are vacuous;
an empty fibre over a nonempty base fails geometric connectedness (Mathlib's
`ConnectedSpace` includes nonemptiness) and satisfies geometric reducedness.
The identity cover of the empty scheme is a Galois cover for **any** group,
including an infinite one: there are no geometric lifts, and its quotient
universal property holds because maps from the empty scheme are unique. This
was excluded by the first worker's use of `[Finite G]` and motivated the repair.
The trivial group and disconnected finite etale trivial torsors are allowed.
A group cannot be empty because it contains its identity. Zero rings give the
empty scheme, with the preceding behaviour. There is no `n` parameter and no
characteristic restriction. Schemes are universe-polymorphic in `u`, and the
acting group has an independent universe `v`; algebraic closures of residue
fields are available in `Type u`, sufficient to test these finite etale fibres.
No binder or universe is left implicit or unbound.

Independent searches used different wording from the worker:

- LeanFinder: “scheme all stalks integrally closed domain automorphism group over
  base” found normalization declarations and `IsIntegral`, no normal-scheme or
  deck-group definition. “finite etale scheme cover arbitrary group acts simply
  transitively geometric points” found abstract Galois-category results, which
  are different notions, and no arbitrary-group scheme cover.
- Loogle: `"stalk", IsIntegrallyClosed` returned zero hits.
- LeanSearch: “scheme stalks integrally closed domains normal scheme” returned
  Internal Server Error; unavailable, no conclusion drawn from that search.
- `msearch.py ... grep 'GaloisCover|deckGroup|GaloisCoverAction'` returned zero
  service hits. Direct `rg` on Mathlib, `WeilConjectures/`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` independently found the existing integral,
  dominance and geometric predicates, and the finite-group `Scheme.GaloisCover`
  at `EtaleTorsor.lean:515–546`. There is no `IsNormalScheme`, `GaloisCoverAction`,
  or `Hom.deckGroup` declaration with the required generality.

Mismatch repaired: the existing finite-group cover is usable for finite groups
but cannot type the empty-base infinite-group case that the node covers. The
new structure states the unrestricted notion already belonging to this item;
it is not a new definition node or a replacement of a dependency. The deck
name and argument were generalized from `GaloisCover.deckGroup T` to
`Hom.deckGroup π`, so this clause covers the same unrestricted case. I retained
the normality body verbatim and removed imports used only by the old restricted
cover or mentioned solely in documentation. The preceding worker report's
finite-cover account is superseded by this repair. The primary node signature
remains verbatim `def IsNormalScheme (S : Scheme.{u}) : Prop`; the declarations
list now includes the unrestricted cover structure and the generalized deck
group. No theorem is proved, no `sorry` occurs, and all definition data is real.
The item is a definition with no proof steps, so H8's proof-sketch requirement
for theorem statements is inapplicable. All main declarations have source and
blueprint docstrings; lines are at most 100 characters.

Server compilation of the repaired module succeeded with exit code 0 and no
warnings (`scompile.py`, 1.8 seconds).
