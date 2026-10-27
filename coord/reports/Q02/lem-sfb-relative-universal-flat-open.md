## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeUniversalFlatOpen` states
`AlgebraicGeometry.exists_relativeUniversalFlatOpen`. The sole proof is `sorry`.
No definitions, dependency repairs, new nodes, or statement corrections are needed.
The node copy changes only `lean`.

Clause-by-clause correspondence:

- Schemes S, X, Y are `{S X Y : Scheme.{u}}`; their three specified morphisms are
  `(p : X ⟶ S) (q : Y ⟶ S) (f : X ⟶ Y)`.
- The equality q composed with f equals p is `(hf : f ≫ q = p)`.
- Flatness of p is `[Flat p]`; local finite presentation is
  `[LocallyOfFinitePresentation p]`.
- The assumption that p sends every closed subset to a closed subset is exactly
  `(hp : IsClosedMap p)`, with no universal closedness requirement.
- Local finite type of q is `[LocallyOfFiniteType q]`; no closedness or separatedness
  of q is assumed.
- The specified locus U is `{x : X | (f.stalkMap x).hom.Flat}`: flatness of the
  local homomorphism from the target stalk to the source stalk, exactly flatness
  at x. Its complement is the nonflat locus.
- The assertion that F = S minus p(X minus U) is open is expressed as existence
  of `F : S.Opens` with `(F : Set S) = (p '' {x : X | (f.stalkMap x).hom.Flat}ᶜ)ᶜ`.
  Thus F is the prescribed set, not an unspecified representing open.
- Its restricted structure sheaf is built into Mathlib's `Scheme.Opens.toScheme`;
  `F.ι` is its canonical inclusion, with the existing `IsOpenImmersion F.ι`
  instance. The phrase about being an open subscheme therefore uses this actual
  construction and adds no arbitrary scheme or inclusion.
- Every test scheme and morphism is `∀ (T : Scheme.{u}) (h : T ⟶ S)`.
  The arbitrary universe u is shared with the original schemes and the chosen
  fibre products, as in the recorded fibre-product and relative-flat-locus APIs.
- The base-changed morphism is `pullback.map p h q h f (𝟙 T) (𝟙 S) ...`.
  Its first projection is f after projection to X and its second projection is
  the projection to T. The two proof arguments express the commutative diagram,
  using hf and the identity laws, and supply no mathematical assumptions.
- `Flat (...) ↔ ∃ l : T ⟶ F.toScheme, l ≫ F.ι = h` states precisely both directions
  of the required equivalence with factorization through this inclusion.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`: `AlgebraicGeometry.Flat`, together with
  `Flat.iff_flat_stalkMap` identifying the recorded notion with stalkwise flatness.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, its projections, and `pullback.map`;
  `Mathlib.AlgebraicGeometry.Pullbacks` supplies scheme pullbacks.
- `Mathlib.AlgebraicGeometry.Restrict`: `Scheme.Opens.toScheme`, `Scheme.Opens.ι`,
  and its canonical open immersion instance.

The declared proof imports are the existing relative flat locus module
(`AlgebraicGeometry.isOpen_flatLocus_and_baseChange`), PullbackCarrier for the subset
image identity, and Prime.Topology for the principal-open basis. OpenImmersion,
Restrict, and Flat already provide the other recorded proof dependencies. The
four-step natural-language proof in the docstring follows the node's proof,
including the actual complement construction, the subset image identity, and
both directions of open factorization.

Sources read: local Stacks `spaces-more-morphisms.tex`, lemma-where-flat (Tag 05XB),
statement and full proof; `more-morphisms.tex`, lemma-base-change-flatness-fibres
(Tag 05VK), statement and proof. These give exactly the hypotheses stated here.

Edge cases checked before drafting: if X is empty, U is empty and F is all of S,
so every base change is flat and every h factors; if f is everywhere flat then
F is again all of S; if a fibre contains a nonflat point, its base point is
excluded, including after extension of residue fields, by the source-flat-locus
base-change theorem. Empty T gives an empty source pullback and a unique map to
F, so both sides hold, including F empty. No reducedness, nonemptiness,
quasi-compactness, or finiteness condition on T was added. The identity base
change is included.

Searches made with `msearch.py Q02 lem-sfb-relative-universal-flat-open`:

- LeanFinder: "The complement of the image of the nonflat locus represents base
  changes making a morphism between relative schemes flat". Eight hits concern
  Flat, base-change stability, or universally open flat maps; no exact theorem.
- Loogle: `"Flat", "LocallyOfFinitePresentation", "IsClosedMap"`. Zero hits.
- Mathlib grep in AlgebraicGeometry: `flatLocus|flat_locus|where.flat|universal.*flat.*open`.
  Zero hits.
- LeanSearch: "The complement of the image of the nonflat locus is the universal
  open base change locus for flatness of a morphism between flat finitely presented
  relative schemes". Eight hits concern universally open maps or basic Flat APIs;
  no exact theorem.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for flat loci and universal
  flatness opens found relative-flat-locus-base-change and the stronger
  surjective-flat-open statement. Neither supplies this specified complement
  with the flatness-only universal property. Targeted item-id grep in
  WeilConjectures returned no hits. The proposed declaration name also has no
  matches in Mathlib, either project source tree, or dag/lean_names_upstream.json.

Validation: `scompile.py` compiled both its sandbox probe and the final library
module successfully (2.3 s and 1.4 s), without errors or warnings.
No STATEMENT-DISPUTED issue or other node fault was found.

## Second reading by Q02

I reread the node, source, and finished file directly. This is a worker self-check;
the maintainer supplies the independent review as prescribed in the dispatcher brief.
The schemes, three morphisms and triangle equation match; the four assumptions
on p and q match individually, with closedness only on p. The existential open's
set equality is the exact displayed complement; its scheme and inclusion are
Mathlib's restricted structure sheaf and canonical open immersion. The universal
quantifiers retain every T and h, and the pullback.map uses f and identity maps
on T and S. The equivalence is flatness, with no surjectivity requirement, and
an actual scheme-morphism factorization. All universe and object binders are
explicit and autoImplicit is disabled. No clause was dropped or strengthened;
no mathematical change was needed on rereading.
