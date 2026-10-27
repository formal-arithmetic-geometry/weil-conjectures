## Worker report

The item is stated by
`SimplexCategory.CodegeneracyWord.related_of_eval_eq` in
`Sheaf.AlgebraicTopology.PureCodegeneracyWordRelations`. Its only proof is `sorry`.
The six-step natural-language proof from the node is included in its docstring.
The new prerequisite `def-sfb-pure-codegeneracy-word` supplies raw words,
concatenation, evaluation, contextual replacement, and its finite equivalence
closure, all with real definitions and no postponed proofs. The item's statement
is unchanged; only `lean` and the addition of this prerequisite to `stmt_deps`
are changed. No dependency repair or statement correction is needed.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| Nonempty finite ordinals and nondecreasing maps | `SimplexCategory.mk a` and its existing morphisms, namely `Fin (a+1) →o Fin (b+1)`. |
| Every nonnegative integer degree; `0 ≤ b ≤ a` | Explicit `{a b : ℕ}` and `(hba : b ≤ a)`. Naturals cover exactly the nonnegative degrees. |
| `σ_i^r : [r+1] → [r]`, `0 ≤ i ≤ r`, adjacent collapse | `SimplexCategory.σ (i : Fin (r+1))`, defined by the existing `Fin.predAboveOrderHom`. |
| Two arbitrary finite composable codegeneracy words | `(w v : CodegeneracyWord a b)`. The inductive syntax has only `nil` and `snoc`; `snoc` appends a letter from degree `b+1` to degree `b`. |
| Empty word for equal endpoints | `CodegeneracyWord.nil a : CodegeneracyWord a a`. |
| Composite, read right to left | `eval nil = 𝟙 _`; `eval (snoc w i) = eval w ≫ SimplexCategory.σ i`, so the last traversal letter is the leftmost function-composition factor. |
| Equal values as maps of ordered sets | `(h : w.eval = v.eval)`; equality of these morphisms is exactly equality of the underlying order homomorphisms. |
| Adjacent replacement in an arbitrary word | `Step.context` takes `before : CodegeneracyWord a (n+2)` and `after : CodegeneracyWord n b`; `comp` inserts the two-letter subword between them. |
| Precisely `σ_j^r ∘ σ_i^(r+1) = σ_i^r ∘ σ_(j+1)^(r+1)` | Set `r = n`. The first pair traverses `i.castSucc`, then `j`; the second traverses `j.succ`, then `i`. The parameters `i j : Fin (n+1)` and `hij : i ≤ j` give exactly `0 ≤ i ≤ j ≤ r`, including equality and the extremes. |
| Finitely many replacements, in either direction, allowing none | Conclusion `Related w v`, defined as `Relation.EqvGen Step w v`: the inductive relation has step, reflexivity, symmetry and transitivity constructors. |
| Every degree between `b` and `a` | A `CodegeneracyWord a b` starts at `a`, ends at `b`, and strictly decreases the degree by one at every letter. Every intermediate member of the equivalence closure has that same indexed type. The context fixes the pair's degrees to `n+2,n+1,n` on both sides. |
| No coface or mixed relation | There is no coface constructor in the syntax, and `Step` has just the displayed pure-codegeneracy relation constructor. |

Dependency declarations read and used:

- `def-weil-pbc-simplicial-set` is a Mathlib-status dependency. Its record names
  `SSet`, `SSet.degenerate`, `SSet.nonDegenerate`, `SSet.Subcomplex`, and
  `SSet.Finite` in Mathlib's `SimplicialSet.Basic`, `Degenerate`, `Subcomplex`,
  and `Finite` modules. I read those signatures and docstrings. Only the initial
  ordinal-category clause of the dependency is needed here: the existing
  `SimplexCategory`, `SimplexCategory.Hom`, `SimplexCategory.mk` from
  `Mathlib.AlgebraicTopology.SimplexCategory.Defs`, and `SimplexCategory.σ`
  from `Mathlib.AlgebraicTopology.SimplexCategory.Basic`. The latter is publicly
  imported by the definition module; it also supplies all the proof dependency
  on this node. No new simplicial-set definition is introduced.
- `def-sfb-pure-codegeneracy-word`: the new module publicly supplies
  `SimplexCategory.CodegeneracyWord`, `.comp`, `.eval`, `.Step`, `.Related`.
- `Relation.EqvGen`, read in `Mathlib.Logic.Relation`, supplies finite reversible
  closure. This is reused rather than defining another closure.

Edge cases checked before finalizing the statement:

- `a=b`, including `a=b=0`: only `nil` is possible; zero moves are allowed.
- `a=b+1`: a single codegeneracy is determined by its repeated pair, and no
  two-letter replacement is required.
- `b=0`: the ordinal `[0]` is nonempty and all codegeneracy indices remain
  legal. No artificial positive lower bound on a target degree is imposed.
- The smallest relation is `r=0`, `i=j=0`, from degree 2 through degree 1 to
  degree 0. The two words are distinct syntax and have equal constant values.
- `i=j` and `j=r` are retained; `castSucc` and `succ` implement the two distinct
  inclusions of `Fin (r+1)` into `Fin (r+2)` with the correct indices.
- No size parameter is restricted: finite ordinals and finite word syntax live
  in `Type`, as their mathematical definitions require, with no ambient test
  objects or coefficient universes.
- As an independent arithmetic sanity check, finite enumeration of all 2372
  words with `0 ≤ b ≤ a ≤ 6` found that each permitted adjacent move preserves
  the value and that every equal-value fiber is connected. This is a check of
  the statement, not a delivered proof.

Searches for an existing statement or notion:

- `msearch.py leanfinder`: "Two codegeneracy words with equal ordinal map values
  are connected using only codegeneracy relations" returned eight hits,
  including `SimplexCategoryGenRel.degeneracies`, `P_σ`, `standardσ`, and
  `mem_isAdmissible_iff`. These concern morphisms in the quotient by all simplex
  relations, rather than the required raw words and pure transformations.
- `msearch.py loogle`: `"SimplexCategoryGenRel", "normal"` returned
  `SimplexCategoryGenRel.exists_normal_form_P_σ`. I read its full signature and
  docstring in `GeneratorsRelations/NormalForms.lean` (286 onward); equality
  in that mixed quotient is insufficient for the statement's restrictions.
- `msearch.py leansearch`: "Raw typed codegeneracy words and finite
  transformations using only sigma sigma relations" returned eight hits,
  including the individual `SimplexCategory.σ_comp_σ` identity and the mixed
  quotient's normal-form theorem. Neither defines the missing syntax/relation
  or states this completeness assertion.
- `msearch.py grep`: `CodegeneracyWord|exists_normal_form_P_σ|standardσ_comp_standardσ`
  in `AlgebraicTopology/SimplexCategory` returned four normal-form-file hits.
  I also read `GeneratorsRelations/Basic.lean`: `FreeSimplexQuiver` has both
  coface and codegeneracy generators, and `homRel` contains all mixed relations.
- `rg` over `lean/Sheaf` and `lean/WeilConjectures` found the pure coface sibling
  but no pure codegeneracy word interface or theorem. The upstream
  `WeilConjectures.CategoryTheory.SimplexPresentationFaithful` contains a private
  `sigma_injective` theorem, read in full, about equality in the mixed quotient;
  it does not state the item. Searching `dag/lean_names_upstream.json` for the
  new names and `grep -rn` for the item's id in `lean/WeilConjectures` gave no hits.
- `rg` over `dag/nodes` found only the item and its truncated-presentation
  consumer for the pure-codegeneracy wording, with no definition node.
  `tools/blueprint_refs.py search codegeneracy` returned zero blueprint nodes;
  `ancestor` reported `blueprint.from.node = None`, used in the new node.

Sources read: local `literature/stacks-project/simplicial.tex`, the ordinal
category and generator definitions, Tags 0167(5) and 0168. The source omits
the presentation proof; the node explicitly supplies its pure-codegeneracy
argument as agent-written. No statement dispute or node fault was found.

Validation: both delivered modules compiled separately and in dependency order
through `scompile.py`, against the live published build. There were no errors
or unexpected warnings. The only theorem left postponed is the item's theorem.

## New nodes

`def-sfb-pure-codegeneracy-word` defines exactly the raw pure-codegeneracy
words, their evaluation and concatenation, and contextual pure-codegeneracy
replacements and finite reversible transformations needed by the item.
Its source is Stacks Tags 0167(5) and 0168. The four recorded `msearch.py`
results are preserved as returned in `mathlib_searches`, supplemented by the
project/DAG and blueprint-index searches above. Existing `FreeSimplexQuiver`
and the quotient normal-form APIs allow coface and mixed relations and do not
provide this pure syntax/relation interface. The existing pure coface node is
a different notion. Every declaration of the new module has the new node's
source/blueprint docstring; all definitions have real data. Its metadata uses
the item's chapter, unit and ancestry, and it is cited by the item.

## Second reading by Q70

I reopened the item, both completed modules, and the new definition node for a
separate clause-by-clause pass. This is the assigned worker's second pass;
the maintainer supplies the independent delivery review. No other agent was
started, as required by the dispatch brief.

The main possible mismatch was composition order. In traversal order the left
relation is `i.castSucc` then `j`, which evaluates to `σ_j^n ∘ σ_i^(n+1)`;
the right relation is `j.succ` then `i`, which evaluates to
`σ_i^n ∘ σ_(j+1)^(n+1)`. Thus the displayed source relation, its index bounds,
and the surrounding contexts agree exactly. I also checked that `Related`
closes the single raw step, rather than equality of evaluated words or the full
simplex relation. Its intermediates remain indexed words with the same
endpoints, which proves the degree-bound clause by the meaning of the syntax.
`nil`, `r=0`, equality of indices and the last possible index are all retained.
No correction was needed during this pass. The item record's signature is
verbatim from its file; the new definition record lists all five declarations.
