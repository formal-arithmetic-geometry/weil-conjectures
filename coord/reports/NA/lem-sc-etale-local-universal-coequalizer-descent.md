## Worker report

The module `Sheaf.AlgebraicGeometry.EtaleLocalUniversalCoequalizerDescent` states
`AlgebraicGeometry.etaleLocalUniversalCoequalizerDescent`, with one `sorry` and no new
definitions. The item changes only in `lean`. No new nodes, dependency repairs, or
statement corrections are needed. There is no statement dispute.

Source read: Stacks `pione.tex`, Tag 0BN9, the entire finite-colimit proof and the
following remark on the forgetful functor to schemes; also `descent.tex`,
`lemma-coequalizer-fpqc-local`. The current blueprint in
`literature/blueprint/latest/blueprint/sec-curve-estimates/sk-thm-br/` states finite-group
quotients instead; the assigned conditional descent tool remains valid and its source
and statement are preserved.

Clause-by-clause rendering:

- `Y : Scheme.{u}` is the arbitrary base. `Z P : Over Y` and `a b : Z ⟶ P` are arbitrary
  schemes and morphisms over it. Neither source has a finiteness or étaleness condition.
- `I : Type w`, `U : I → Scheme.{u}`, `ι : ∀ i, U i ⟶ Y` give the set-indexed family;
  `hι : ∀ i, Etale (ι i)` gives exactly its étaleness. `hcover` asserts that every base
  point has a preimage under one member, exactly the images-cover condition.
- `Q i : MorphismProperty.Over (@IsFinite ⊓ @Etale) ⊤ (U i)` uses the dependency's exact
  Mathlib category: the structure map is both finite and étale, with all base morphisms
  admitted. `Over.mk (Q i).hom` forgets these properties when arbitrary maps are needed.
- `Over.pullback (ι i)` is Mathlib's canonical fibre-product functor. Its object on `P`
  has underlying scheme `pullback P.hom (ι i)` and second projection to `U i`; its map on
  `a` or `b` is their induced base-change map. Thus `q i` and `heq` are precisely the
  specified local quotient morphism and equalizing equation.
- `hlocal` quantifies over every `V : Scheme.{u}`, every `v : V ⟶ U i`, every arbitrary
  `H : Over V`, and every morphism `h` from the pulled-back `P`. The displayed equation
  is the equalizing hypothesis. `∃! k` is unique factorization through the canonical
  pullback of `q i`. These are iterated pullbacks, as explicitly allowed in the node;
  `Over.pullbackComp` identifies them canonically with pullback along `v ≫ ι i`.
- Existential `Q₀` is a finite étale scheme over `Y` in the same Mathlib category, and
  `q₀ : P ⟶ Over.mk Q₀.hom` is the global quotient map. `a ≫ q₀ = b ≫ q₀` is its
  equalizing equation.
- `∀ i, ∃ θ` supplies an isomorphism in `Over (U i)` from the base-changed global target
  to the specified `Q i`, and `(Over.pullback (ι i)).map q₀ ≫ θ.hom = q i` is exactly
  compatibility with its local quotient map. Quantifying the isomorphisms this way is
  equivalent to choosing their family; no coherence beyond the node's clause is added.
- The final quantifiers over `Y'`, `g`, `H`, `h`, and the equalizing equation give every
  requested arbitrary base change and arbitrary target. The final `∃! k` is its full
  universal property, not merely the universal property inside finite étale schemes.

Dependency declarations read and used:

- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, and `.lift`
  in `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`. The canonical functor
  `CategoryTheory.Over.pullback` in `Mathlib.CategoryTheory.Comma.Over.Pullback` uses
  exactly this construction, including the induced pullback maps.
- `def-weil-pbc-finite-etale-category`: its `mathlib_match`,
  `CategoryTheory.MorphismProperty.Over` in `Mathlib.CategoryTheory.MorphismProperty.Comma`,
  specialized to `@IsFinite ⊓ @Etale` with all morphisms. Its recorded base-change functor
  `MorphismProperty.Over.pullback` was also read; ordinary `Over.pullback` is used after
  forgetting finite étale conditions, because the universal property concerns arbitrary
  schemes. No separate finite étale definition is introduced.
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale` in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`. `IsFinite` is the standard class in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite`.

The proof-only imports retain all recorded proof dependencies with usable declarations:
Mathlib scheme coproducts, étale composition and source/target locality, open immersion
base change, and stability of étale coverings; plus the upstream modules
`WeilConjectures.AlgebraicGeometry.FiniteEtaleDescent`,
`WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf`, and
`WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`. Their relevant declarations are
`finiteEtaleDescent`, `smallEtaleRepresentablePresheaf_isSheaf`, and `Over.DescentDatum`.
The theorem docstring reproduces all six steps of the node's proof, including gluing
morphisms on arbitrary sources and arbitrary-base-change factorization.

Edge cases checked mathematically and against the binders:

- Empty index set forces an empty base by `hcover`; it is allowed. No `Nonempty I` is added.
- Empty base, empty cover members, empty sources or quotient targets are not excluded.
- Infinite covers and unbounded finite local ranks are allowed. The index universe `w`
  is independent of `u`. For the proof's coproduct argument, a subcover indexed by base
  points is small; uniqueness recovers comparisons on all original members. No `Small I`
  assumption is added.
- All test schemes use the same scheme universe as the base, so the universal property
  is not vacuous from quantifying in a smaller universe. `u` remains arbitrary.
- Identity base changes and morphisms factoring through no single cover member remain
  among the final quantifiers. There is no separatedness, quasi-compactness or uniform
  rank assumption on the base, cover or sources.
- The uniqueness is uniqueness of morphisms over the base, as stated, with no arbitrary
  choice of a replacement base-change map.

Searches actually run via `msearch.py NA lem-sc-etale-local-universal-coequalizer-descent`:

- LeanFinder: `Universal coequalizers of schemes with finite etale local targets descend
  along a jointly surjective etale covering family`: eight hits on open-cover gluing,
  jointly surjective coproduct maps and approximation; none states this descent lemma.
- Loogle: `CategoryTheory.Limits.IsColimit, AlgebraicGeometry.Scheme`: twelve hits,
  including `Scheme.Cover.ColimitGluingData.isColimitGluedCocone`, involving open-cover
  gluing rather than arbitrary étale descent of finite étale quotient targets.
- Mathlib grep: `coequalizer|Coequalizer` in `AlgebraicGeometry`: twelve hits, in scheme
  gluing, pullbacks and ideal subschemes; no exact match.
- LeanSearch: `Etale local universal coequalizers with finite etale targets descend to a
  scheme`: eight hits, mainly locally ringed space coequalizers and general categorical
  coequalizer factorization, not the required theorem.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for coequalizers and descent:
  existing finite étale finite-limits theorem is a consumer with a different statement;
  existing representable étale quotients concern a presheaf quotient, not this conditional
  descent theorem. Direct blueprint-ID grep in `WeilConjectures` found no attachment.
  Name search in these directories and `dag/lean_names_upstream.json` found no collision.

Validation: `scompile.py` compiled the theorem separately in sandbox and library module
modes without errors or non-sorry warnings. `set_option autoImplicit false` enforces that
all variables are bound explicitly. The final module will also be checked by delivery
preflight and its per-file compiler.

## Second reading by NA

The dispatcher forbids starting another agent; independent review belongs to the
maintainer's delivery review. This is a second self-reading, not an independent review.
Reopened the node and the signature and checked each clause above. In particular, the
hypothesis has an arbitrary `H : Over V`, the conclusion has an arbitrary `H : Over Y'`,
and only `Q` and `Q₀` lie in the finite étale subcategories. The arrows and comparison
isomorphisms are morphisms in the correct over-categories. Equalizing equations use
Lean's left-to-right composition in the correct order. Iterated local pullbacks retain
both the local base morphism and the original cover morphism. No omitted hypotheses,
extra conclusions, or silent statement changes were found. The initial compiler found
that dot notation on the infimum of morphism properties did not infer its category;
using the fully qualified `MorphismProperty.Over` fixed elaboration without changing
meaning.
