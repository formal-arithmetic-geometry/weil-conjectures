## Worker report

The module `Sheaf.AlgebraicGeometry.GroupoidQuasiFiniteLocusDescent` states
`AlgebraicGeometry.groupoid_quasiFiniteLocus_descends`, with its entire proof `sorry`.
The node's natural-language statement and accepted stage-1 split are unchanged.
There are no new notions, dependency repairs, or statement corrections.
The obsolete previous stage-1 refusal is superseded by the stage handoff in
`coord/brief-stage2.md` §0: the current queue explicitly assigns stage 2, and the
item has no existing Lean record.

Hypotheses and constructions, clause by clause:

- `{S U R B : Scheme.{u}}`, with explicit `universe u`, supplies the base, objects,
  arrows and slice scheme in the size convention. There are no auxiliary test
  universes or additional restrictions on their size.
- `s t : R ⟶ U`, `e : U ⟶ R`, `i : R ⟶ R`, `c : pullback s t ⟶ R`, and
  `hG : IsGroupoidScheme s t e i c` give exactly the recorded groupoid data and
  laws, with composition ordered `c(a,b) = a ∘ b`.
- `uS : U ⟶ S`, `rS : R ⟶ S` give the structural maps. `_hs` and `_ht`
  say that `s,t` are over `S`; `_he`, `_hi`, `_hc` say the same for identity,
  inverse and composition. The structural map on the composition domain is
  `pullback.fst s t ≫ rS`. It also equals the second projection's structural
  map by the pullback equation and `_hs`, `_ht`. These equations unpack
  the node's phrase “all structure morphisms being over S”; they add no
  geometric assumption. The node only asks that `g` be a scheme morphism.
- `g : B ⟶ U` is that arbitrary morphism. The three instances
  `[LocallyOfFiniteType s]`, `[LocallyOfFiniteType t]`,
  `[LocallyOfFiniteType g]` are exactly its three local finite-type assumptions.
- `H` is written explicitly as `pullback g t`, `p` as `pullback.fst g t`,
  and `h` as `pullback.snd g t ≫ s`. No replacement construction is introduced.

Conclusions, clause by clause:

- `∃ W : B.Opens` supplies the open subscheme `W` with its canonical scheme
  structure. `pullback.fst g t ⁻¹ᵁ W` is its inverse-image open in `H`.
- For every point `z` of the explicitly scheme-valued pullback, the equivalence
  `z ∈ (pullback.fst g t ⁻¹ᵁ W) ↔
  Scheme.Hom.IsQuasiFiniteAtPoint (pullback.snd g t ≫ s) z`
  identifies that open with the pointwise quasi-finite locus. Opens are equal
  exactly when their memberships agree; their canonical open subschemes then
  agree as well. Thus this clause includes equality as open subschemes, without
  choosing an arbitrary scheme or a noncanonical isomorphism.
- `Scheme.Hom.IsLocallyQuasiFinite
  ((pullback.fst g t ⁻¹ᵁ W).ι ≫ (pullback.snd g t ≫ s))` is the stated
  locally quasi-finite restriction, including the Stacks local finite-type
  requirement. Mathlib's weaker predicate is not substituted.
- The final implication is quantified over all `b : B`. Its antecedent uses
  the canonical scheme morphism `pullback.lift (𝟙 B) (g ≫ e)` evaluated at `b`,
  precisely the identity-section point `(b,e(g(b)))`. The compatibility proof
  uses `hG.identity_target`. Its conclusion is `b ∈ W`. An arbitrary point with
  those two projections would not specify the canonical point, so is not used.

Recorded declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.GroupoidScheme`:
  `AlgebraicGeometry.IsGroupoidScheme`, including its full structure fields and
  docstring. This module publicly supplies scheme pullbacks.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`,
  `locallyOfFiniteType_comp`, `locallyOfFiniteType_isStableUnderBaseChange`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion`, and the canonical opens/inclusion API.
- `WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism`:
  `AlgebraicGeometry.Scheme.Hom.IsQuasiFiniteAtPoint` and
  `AlgebraicGeometry.Scheme.Hom.IsLocallyQuasiFinite`; their full bodies and
  docstrings were read. In particular their finite-type conditions are retained.
- Proof import `Sheaf.AlgebraicGeometry.QuasiFiniteLocusOpen`:
  `AlgebraicGeometry.Scheme.Hom.isOpen_quasiFiniteAtPoint`, full statement and
  proof docstring read. The finite-type permanence proof matches are already
  available through public dependencies. The remaining proof-only node
  `lem-sfb-scheme-quasifinite-at-base-change` has no recorded Lean or Mathlib
  match, so has no module to import; it is not needed to type this statement.
  Its use remains named in the theorem's complete proof plan and unchanged DAG.
- `def-weil-size-convention` is explicitly a metatheoretic convention with no
  declaration to import; its role here is the declared universe `u`.

Sources read: `literature/stacks-project/more-groupoids.tex`,
`lemma-local-source` (04LH), including the full proof, and
`remark-local-source-apply` (047W), item (2). The latter takes P = locally
quasi-finite and Q = R = locally of finite type and explicitly requires no
flatness. The five-step declaration docstring follows the accepted split,
including both inverse formulas for the cartesian comparisons and descent via
`j = (id_H, sigma p)`.

Edge cases checked before writing: empty `B` gives empty `H`, with the empty open
and vacuous point clauses; the identity groupoid reduces to openness of the
quasi-finite locus of `g`. For the trivial additive-group action and `g = id`,
the positive-dimensional fibres give the empty locus. For a finite constant
(group) action and `g = id`, the saturation map is locally quasi-finite and
`W = ⊤`. No flatness, surjectivity, separatedness, finite presentation or
Noetherian hypothesis was introduced; nonflat groupoids remain allowed. The
identity section is a scheme morphism and is meaningful over every residue
field, so no rational-point or lift-of-points hypothesis is hidden.

Searches (all remote searches used `msearch.py Q157
lem-sfb-groupoid-quasifinite-locus-descent`; raw outputs are retained in
`searches.jsonl` in the sandbox):

- LeanFinder: “For a groupoid of schemes the quasi finite locus of the saturation
  map B times U R to U descends to an open subset of B”. Eight hits, concerning
  `LocallyQuasiFinite`, its restrictions and multiplicativity; no groupoid descent.
- Loogle: `"QuasiFinite", "Groupoid"`. Successful search, zero hits.
- Mathlib grep: `quasi.?finite.*locus|groupoid|quasiFiniteLocus` in
  `AlgebraicGeometry`. Five hits in `ZariskisMainTheorem.lean`, defining the
  individual-morphism locus. Read its declaration and membership lemma at
  lines 292–322: it does not give descent through a scheme groupoid.
- LeanSearch: “For a groupoid of schemes the quasi finite locus of its saturation
  morphism is the inverse image of an open subset of the source”. Eight hits
  on individual morphism properties, none stating the requested theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `IsGroupoidScheme`,
  groupoid/quasi-finite combinations, `quasiFiniteAtPoint`, `quasiFiniteLocus`.
  Found the existing groupoid definition, unrelated groupoid rank and orbit
  results, and individual quasi-finite loci; no same-statement declaration.
- `grep -rn` for the exact item id in `lean/WeilConjectures`: no hits.
- `rg` of `dag/lean_names_upstream.json` for groupoid saturation/locus names:
  no matching existing declaration.

Validation: module-mode compile through `scompile.py`. The first attempt exposed
an ambiguity between the pullback in schemes and the pullback in types when
binding a point; explicitly writing `↥(pullback g t : Scheme.{u})` resolves the
ambiguity without changing the mathematical statement. No statement is disputed.

## Second reading by Q157

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
