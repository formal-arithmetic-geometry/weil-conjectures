## Worker report

This is stage 2, not a repeat stage-1 split. The current queue lists this item at stage 2,
its split was reviewed by Q46, and it has no Lean record. The inherited unchanged-item
rejection concerned the earlier stage-1 attempt. I preserve its statement, accepted proof,
and proof dependencies. There is no released repair note for this item.

`Sheaf.AlgebraicTopology.PureCofaceWordRelations` states
`SimplexCategory.CofaceWord.related_of_eval_eq`, with its sole proof `sorry`.
`Sheaf.AlgebraicTopology.PureCofaceWord` provides the raw syntax and contextual relation
needed to state the result, under the new definition node below. Every definition has
actual data and no postponed proof. The theorem docstring carries all five accepted proof
steps, including the index-sum termination measure and the omitted-vertex calculation.

Clause-by-clause correspondence with the item:

- The objects `[a]`, `[b]` of the category of nonempty finite ordinals are
  `SimplexCategory.mk a`, `SimplexCategory.mk b`; natural-number binders include degree zero.
  `hab : a ≤ b` renders the explicitly fixed endpoint inequality.
- A raw finite composable sequence of cofaces is `CofaceWord a b`. Its constructors are
  `nil a`, the empty word, and `snoc w i`, adding the coface with index `i : Fin (b + 2)`
  from degree `b` to degree `b + 1`. There is no quotient by equality of values.
- `eval` sends the empty word to the identity and `snoc w i` to `eval w ≫ δ i`, hence
  composition in ordinary function notation is right to left as in the node.
  The hypothesis `h : w.eval = v.eval` is equality of the monotone maps: Mathlib's simplex
  morphisms are precisely their bundled order homomorphisms, with no extra map data.
- The conclusion `Related w v` is `Relation.EqvGen Step w v`. This inductive equivalence
  closure allows a step, zero steps, reversing a finite derivation, and concatenating two
  finite derivations. It therefore expresses finitely many replacements in either direction.
- The single `Step.context` constructor performs one adjacent two-letter replacement in
  arbitrary composable contexts `before` and `after`; `comp` is raw concatenation.
  Its left pair is inner `i`, outer `j.succ`; its right pair is inner `j`, outer
  `i.castSucc`. With the node's `r = n + 1` and outer `J = j + 1`, the condition `i ≤ j`
  is exactly `i < J`, and both sides are precisely the printed relation. Every allowed
  node relation has such a `j = J - 1`, including the extreme indices.
- Only `snoc` coface letters exist. A `CofaceWord a b` starts at `a` and raises degree by
  one at each letter until `b`; thus each vertex is between these endpoints. `Step` and
  its closure keep the same indexed type, so this also holds for every replacement and
  intermediate word. No separate unbounded derivation or mixed-quotient equality is used.

Dependency declarations read and used: `Mathlib.AlgebraicTopology.SimplexCategory.Basic`
provides `SimplexCategory`, `mk`, `δ`, and `δ_comp_δ`. The latter is the existing Mathlib
match for proof dependency `lem-weil-pbc-simplex-face-face-identity`, and is available through
the definition module's public import. The statement dependency
`def-weil-pbc-simplicial-set` is a Mathlib leaf: I read its recorded `SSet` in Basic,
`degenerate` and `nonDegenerate` in Degenerate, `Subcomplex` in Subcomplex, and `SSet.Finite`
in Finite. Its category and cofaces are the Mathlib simplex category used here; the theorem
has no simplicial-set variable and therefore needs only that category's Basic module.
`Mathlib.Logic.Relation` supplies the existing `Relation.EqvGen`, which is reused rather than
redefined. The only added statement dependency is `def-sfb-pure-coface-word`.

Edge cases checked before writing: `a = b` has only the empty raw word and permits the
reflexive zero-step derivation. For `b = a + 1` there is one coface, and equality of its
omitted vertex determines its index; no step can occur. The minimal two-letter case is
`a = 0`, `b = 2`, with `n = 0`, so the relation's `r = 1` is included. For `i = j`,
`Step.context` includes consecutive indices `i < i + 1`, as required. The extremes `i = 0`
and `j = n + 1` are valid and include omission of the last vertex via `j.succ`.
Every ordinal remains nonempty; no augmented degree minus one is introduced. Words with
endpoints in decreasing order cannot be constructed, and no extra condition excludes any
case of the node. No universe restriction is introduced: these are finite ordinal words.

Searches actually run with msearch.py, recorded in searches.jsonl and the new node:

- LeanFinder: "Two raw coface words with equal order preserving maps are related using
  only coface identities" returned `faces`, `P_δ`, `P_σ`, and mixed-presentation results.
  `P_δ` is a property of morphisms already in the mixed quotient, not raw words.
- Loogle: "SimplexCategoryGenRel, FreeSimplexQuiver" returned zero hits for that query.
- LeanSearch: "Raw words of coface maps and the equivalence relation generated only by
  coface identities" returned individual coface identities, mixed identities and face
  predicates, not this syntax and pure contextual congruence.
- Mathlib grep: `CofaceWord|cofaceWord|coface.word|pure.coface|coface.*relation` under
  AlgebraicTopology returned zero hits. I also read the raw mixed `FreeSimplexQuiver.Hom`,
  `homRel` and its mixed quotient in GeneratorsRelations/Basic. That raw quiver includes
  codegeneracies and its quotient admits all relations, so neither supplies this relation.
  GeneratorsRelations/NormalForms still lists unique pure-delta normal forms as a TODO.
- The same expression and the item id were searched in both project source roots,
  WeilConjectures and Sheaf. Only full mixed-presentation faithfulness and unrelated tensor
  coface results appeared; neither provides the restricted raw-word assertion.
- DAG text search found the item, its pure-codegeneracy sibling and its truncated-simplex
  consumer, plus full mixed-presentation and unrelated tensor results. No node defines
  raw pure-coface syntax and its restricted contextual rewrite relation.
  `tools/blueprint_refs.py search coface` found only two hypercover homology nodes;
  `ancestor` reports None, matching the item's inherited null blueprint ancestor.

Source read directly: literature/stacks-project/simplicial.tex, labels
lemma-relations-face-degeneracy (0167), part (1), and lemma-face-degeneracy-category (0168).
Both printed proofs are omitted; the restricted pure-coface proof is the accepted agent
argument in this DAG. There is no statement correction and no disputed statement.

Validation: both delivered modules compile separately in dependency order through
scompile.py against the published library, with no errors or non-sorry warnings.
The first probe exposed a dependent-pattern binder and a reserved identifier; both were
repaired before the successful compile. No live sources or tools were edited.

## New nodes

`def-sfb-pure-coface-word` defines raw typed coface words, concatenation, their evaluation,
a single contextual coface replacement, and its finite equivalence closure. Its module is
`Sheaf.AlgebraicTopology.PureCofaceWord`, with all five declarations recorded. This is the
syntax and replacement notion assumed in the item's prose, sourced to 0167(1)/0168. The
searches above rule out an existing pure raw-word notion in the DAG and library; the mixed
quotient cannot be substituted because its derivations may use degeneracies or leave the
endpoint degrees. Its inherited blueprint ancestor is null, exactly as the ancestor tool
reports; the `via` field prepends the item to the item's existing ancestry chain. The new
node preserves the item's chapter and unit and cites the existing simplex-definition node.

The first dry run required `import_flags` on the new node, although the brief does not
list that required schema key. Added the empty list; no import flags are asserted.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
