## Worker report

Repair of the stage-2 packet at returned head `108c1422c159`. The saved packet's
initial `deliver2.py --no-push` passed (dry-run commit `6f798f001d`), but its five
conjuncts did omit substantive clauses named by the maintainer. I retained its
bounded quotient, relation, comparison formula, image statement and module path,
and completed the missing interfaces. Only the item's `lean` field changes;
its mathematical statement, dependencies and six-step proof remain unchanged.
The other node fields have been refreshed from the current read-only main copy.

The delivered module is
`Sheaf.AlgebraicTopology.TruncatedCoendSkeletonImage`, in namespace `SSet`.
All helper declarations are listed in `lean.declarations` and belong to the
construction and six proof steps of this existing node. There are no new nodes
or dependency repairs. Every definition has specified data, every theorem has
proof `by sorry`, and each declaration cites its source and blueprint id.
Every theorem docstring supplies the applicable proof plan; the main docstring
includes all six DAG proof steps and the four recorded nondegenerate-decomposition
lemmas used in steps 2--4.

The node's hypotheses and clauses are rendered as follows. Names in this table
are in namespace `SSet`.

| Node text | Lean rendering |
| --- | --- |
| Any small simplicial set `S : Δᵒᵖ → Sets` | `(S : SSet.{u})`, with explicit universe `u`; no finite, nonempty, split, or nondegeneracy-preservation hypothesis |
| `k ≥ 0` | `(k : ℕ)`, including `0` |
| `Δ^a_q = Hom([q],[a])` | `(⦋q⦌ ⟶ ⦋a.1⦌)` in `truncatedCoendGenerator`; standard-simplex operators precompose this order map |
| Coproduct over `a ≤ k` | `Σ a : Fin (k + 1), S _⦋a.1⦌ × (⦋q⦌ ⟶ ⦋a.1⦌)`; `truncatedCoendGeneratorsSSet` bundles it simplicially |
| Relation coproduct over `a,b ≤ k` and `α : [a] → [b]` | `truncatedCoendRelationGenerator` and `truncatedCoendRelationsSSet`, with both indices in `Fin (k+1)` |
| Left arrow applies `S(α)`; right arrow postcomposes by `α` | `truncatedCoendRelationLeftRaw` and `truncatedCoendRelationRightRaw`, bundled as `truncatedCoendRelationLeft` and `truncatedCoendRelationRight` |
| Form the simplicial coequalizer `R_k(S)` | The quotient `truncatedCoend` by `Relation.EqvGen (truncatedCoendStep ...)`, bundled as `truncatedCoendSSet`; `truncatedCoendQuotientπ`, `truncatedCoendCofork`, and `truncatedCoendCofork_isColimit` give its categorical universal property |
| Degree-`q` representative `[x,β]` | `Quotient.mk (truncatedCoendSetoid S k q) ⟨a,x,β⟩`; the evaluation degree `q : ℕ` is unrestricted |
| `j_k[x,β] = S(β)x` | `truncatedCoendComparisonRaw`, `truncatedCoendComparison`, and the actual simplicial map `truncatedCoendComparisonNat` |
| Degreewise injectivity | Main theorem conjunct 1, `∀ q, Function.Injective (truncatedCoendComparison S k q)` |
| Image = simplices with nondegenerate ancestor of dimension at most `k` | Conjunct 2, range equality with `∃ r, r ≤ k ∧ ∃ y : S.nonDegenerate r, ∃ σ, Epi σ ∧ z = S.map σ.op y.1`; uniqueness is supplied by the recorded decomposition lemmas, not an extra hypothesis |
| Equivalently the simplicial subset generated in dimensions at most `k` | Conjunct 3, equality with `(S.skeleton (k + 1)).obj (op ⦋q⦌)`; Mathlib's definition uses dimensions strictly below its argument |
| Unrestricted coend `∫^a S_a × Δ^a` | `unrestrictedCoendStep`, `unrestrictedCoendSetoid`, `unrestrictedCoend`, `unrestrictedCoendOperator`, `unrestrictedCoendSSet`; `unrestrictedCoend_coequalizer` states the corresponding simplicial universal property |
| Its canonical identification with `S` | `unrestrictedCoendIso`, whose hom evaluates `[x,β]` and whose inverse is `unrestrictedCoendSectionNat`, `z ↦ [z,id]`; the two inverse equations also appear as conjuncts 6 and 7 |
| Canonical map from `R_k` to that unrestricted coend is `j_k` after identification | `truncatedToUnrestricted` and `truncatedToUnrestrictedNat` forget the bound; conjunct 8 is the degreewise composite equation and conjunct 14 the equation of simplicial maps using `(unrestrictedCoendIso S).hom` |
| Maps are simplicial | `truncatedCoendSSet_laws`, `unrestrictedCoendSSet_laws`, the bundled simplicial maps and their named naturality laws; main conjuncts 4 and 12 also state comparison/operator compatibility pointwise |
| Naturality in `S` | `truncatedCoendMapRaw f` and `unrestrictedCoendMapRaw f` apply `f` to the label; `truncatedCoendMapNat`, `unrestrictedCoendMapNat`, the two endofunctors and their identity/composition laws give functoriality; the comparison transformations give naturality, also conjuncts 9 and 10 |
| Naturality of the bounded/unbounded inclusion and inverse identification | `truncatedToUnrestrictedTransformation`, conjunct 11, and conjunct 17 (the inverse sends `f(z)` to `[f(z),id]`) |
| Truncation `R_k → R_(k+1)` | `truncatedCoendTruncationRaw`, `truncatedCoendTruncation`, `truncatedCoendTruncationNat`, retaining the same label and order map, with the index embedded in `Fin (k+2)` |
| All comparison and truncation compatibilities | Conjunct 5 gives `j_(k+1) ∘ trunc = j_k`; conjunct 15 gives compatibility with the unrestricted inclusion; `truncatedCoend_compatibilities` bundles all three equations of simplicial maps; `truncatedCoendTruncationTransformation` and conjunct 16 give naturality in `S` |
| Displayed categorical coequalizer assertion | Conjunct 13, `Nonempty (CategoryTheory.Limits.IsColimit (truncatedCoendCofork S k))`; only a proof of the universal property is postponed, not its objects or arrows |

The bounded coequalizer interface is literal: the relation and generator
simplicial sets have the displayed sigma coproducts as their degreewise data,
and their operators precompose the standard-simplex map. The left relation
arrow gives `(S(α)z,γ)`, the right one `(z,γ ≫ α)`. The cofork point is the
specified quotient, and its projection is `Quotient.mk`. Thus this is not a
replacement of `R_k` by the Kan-extension skeleton `SSet.sk`.

The `TruncatedCoendCompatible`, `truncatedCoend_coequalizer`, and
`unrestrictedCoend_coequalizer` interfaces additionally state the degreewise
unique descent and its operator compatibility for every target simplicial set.
Their target has the same arbitrary universe as `S`, which is the ambient
category of small simplicial sets in the node. The underlying quotients and
all label/operator maps have real data. Quotient well-definedness, simplicial
laws and naturality are separate named theorems using `sorry`; none is proved
inline in a definition.

Dependency declarations read and used:

- `def-weil-pbc-simplicial-set` is a Mathlib leaf. Its recorded declarations are
  `SSet` in `Mathlib.AlgebraicTopology.SimplicialSet.Basic`,
  `SSet.degenerate`/`SSet.nonDegenerate` in `...Degenerate`, and
  `SSet.Subcomplex` in `...Subcomplex` (also `SSet.Finite` in `...Finite`, not
  needed here). I read their signatures and source definitions. `SSet` is
  exactly `SimplicialObject (Type u)`, maps are natural transformations, and
  `nonDegenerate` is the complement of the recorded degeneracy predicate.
- `def-weil-pbc-category-colimit` records `CategoryTheory.Limits.colimit`,
  `Cocone`, `IsColimit`, and `colimit.desc` in
  `Mathlib.CategoryTheory.Limits.HasLimits`. The present cofork uses that
  `IsColimit` universal property through `Limits.Shapes.Equalizers`, including
  `Cofork.ofπ`; the explicit quotient already chooses the object.
- The proof dependency
  `lem-weil-pbc-simplicial-set-nondegenerate-decomposition` records
  `SSet.exists_nonDegenerate`, `unique_nonDegenerate_dim`,
  `unique_nonDegenerate_simplex`, and `unique_nonDegenerate_map` in
  `Mathlib.AlgebraicTopology.SimplicialSet.Degenerate`. I read all four full
  signatures. Their surjections are `Epi` in `SimplexCategory`, precisely the
  surjective order-preserving maps, matching the image clause.
- The generated subset is the existing `SSet.skeleton` in
  `Mathlib.AlgebraicTopology.SimplicialSet.Skeleton`; I read its supremum of
  `Subcomplex.ofSimplex` over nondegenerate dimensions `< n` and
  `ofSimplex_le_skeleton`. This justifies the shift from `k` to `k+1`.

Source reading: `literature/stacks-project/simplicial.tex`, the statement and
proof of `lemma-splitting-simplicial-sets` (Tag 017R) and the immediately following
warning that a simplicial map may take a nondegenerate simplex to a degenerate
one. The coend construction and its naturality follow the agent-authored six
steps in this exact node; the source is not claimed to state the coend theorem
verbatim.

Edge cases checked by reading the formulas:

- Empty `S`: every generator type and quotient is empty. All maps and universal
  properties remain meaningful; no artificial generator or nonempty assumption
  has been introduced.
- `k=0`: `Fin 1` retains the vertices, not an empty truncation. All high-degree
  classes are the degeneracies of vertices. For `Δ¹`, its two vertices remain
  distinct and its nondegenerate edge is excluded from the image.
- `q>k`: only `a,b` are bounded in the relation, never the evaluation degree.
  Factoring an order map through its image in the normal-form proof stays in
  the bounded indices even in this case.
- `Δ²` at `k=1`: the image contains its boundary and degeneracies, not the
  nondegenerate 2-simplex. Faces of a nondegenerate simplex are allowed to be
  degenerate; the proof applies decomposition after taking the face.
- A map collapsing the edge of `Δ¹` to a point is admitted by every naturality
  statement. The construction uses all labels and never requires a functorial
  splitting into nondegenerate simplices.
- Universe 0 and arbitrary universe `u` are both allowed. An external consumer
  compiled the unrestricted isomorphism at `SSet.{0}` and the categorical
  coequalizer/truncation interfaces at an explicitly declared arbitrary universe.

Searches made/rechecked (`searches.jsonl` keeps the raw launcher results):

- LeanFinder: `explicit bounded quotient of a simplicial set by coend relations
  and canonical map to simplicial set` returned standard simplices, `SSet.sk`,
  `SSet.cosk`, and nondegenerate-simplex APIs, not this comparison theorem.
- Loogle: `SSet.skeleton, Relation.EqvGen, Quotient.map` returned no hits.
- Mathlib grep: `truncatedCoend|unrestrictedCoend` in `AlgebraicTopology`
  returned no hits. Direct `rg` in the upstream `WeilConjectures` source and
  shared `lean/Sheaf` found neither these declarations nor this node id.
- The repair repeated LeanFinder with `The bounded simplex coend quotient
  embeds into a simplicial set as its skeleton, naturally, and includes into
  the unrestricted coend`. Its hits were `SSet.skeleton`, `SSet.sk`,
  `ofSimplex_le_skeleton`, `mem_skeleton`, `skeleton_obj_eq_top`,
  `iSup_skeleton`, and `SSet.N.toS`/`S.toN`. None states the bounded quotient
  comparison. The read source `Skeleton.lean` explicitly leaves the
  `SSet.sk`/`SSet.skeleton` identification as a TODO.
- An additional Loogle query `SSet.skeleton, SSet.sk, Cofork.ofπ` reported
  unknown unqualified identifier `Cofork.ofπ`, so that query alone is not
  evidence of absence. The recorded earlier Loogle query and direct source
  reading of the qualified `CategoryTheory.Limits.Cofork.ofπ` supply the usable
  search/signature checks. No existing notion was replaced.

Validation: `scompile.py` compiled the delivered module without errors or
warnings. It also compiled the separate, non-delivered
`scratchpad/Consumer.lean` against the module in a private overlay. That file
checks use of the public names from outside the namespace, the unrestricted
isomorphism at universe 0, the `IsColimit` interface at arbitrary universe,
comparison through the unrestricted isomorphism, and naturality of the
`k=0 → k=1` truncation. This is statement/interface validation, not proof
completion. All theorem proofs intentionally remain `sorry`.

## Second reading by Q91

This is the required worker self-check after repair, not an independent
maintainer review; the dispatcher explicitly prohibits starting another agent.
I reopened the unchanged node statement, all six proof steps, its dependency
records and full recorded signatures, and the completed Lean module.

H3, construction: the old packet had only types indexed by degrees. The repair
now has actual `SSet` objects with named functor laws, the two specified
simplicial relation arrows, a specified projection, a `Cofork`, and its
`IsColimit` assertion. Reading the data fields confirms that the sigma sums,
labels, order maps and two arrows are exactly the displayed coequalizer.

H3, image and hypotheses: the binders remain only arbitrary `SSet.{u}` and
`k : ℕ`; no proper, finite, nonempty, or extra preservation hypothesis was
added. The first three theorem conjuncts retain injectivity, the ancestor
image with `r ≤ k`, and the generated-subcomplex image with the explicit
`k+1` shift. `q` remains arbitrary in every construction and theorem.

H3, unrestricted comparison: the old packet had no unrestricted object or
map. The repair supplies the unbounded quotient with natural-number indices,
its operator and simplicial object, the identity-generator section and an
actual isomorphism whose hom and inv are those specified maps. Reading the
comparison equations shows that the bounded inclusion followed by its hom is
exactly `j_k`, both degreewise and as a simplicial map. A type mismatch between
a bounded and an unrestricted induced map in an intermediate draft was fixed;
the inclusion-naturality clause now uses `unrestrictedCoendMap` on its right.

H3, naturality and truncation: the old operator compatibility was naturality
only in degree, not in `S`. Reading the new endofunctors and transformations
checks identity/composition, naturality for all `f : S ⟶ T`, naturality of the
bounded/unrestricted inclusion, and naturality of truncation. The final clauses
also state inverse-section naturality and all maps to the unrestricted coend.
They admit maps collapsing nondegenerate simplices; there is no chosen
functorial splitting. Explicit `.{u}` on transformations with no `S` binder
prevents an accidental fresh, unbound universe parameter.

H6: I checked every declaration body. Every theorem is exactly `by sorry`.
No definition contains `sorry`, `by`, induction, simplification or arithmetic
tactics. Quotient lifts/maps refer to named relation-respect theorems; their
simplicial and natural-transformation fields refer to named law theorems.
The maps underlying the unrestricted isomorphism are actual quotient formulas;
only their inverse equations are postponed.

H8: every declaration has a source and this blueprint id. Every theorem
has a proof plan applying the appropriate quotient, naturality or uniqueness
argument. The main docstring now has the six numbered DAG proof steps,
including ordered-image factorization, all three uniqueness uses, the exact
image/minimal generated subset argument, unrestricted inversion, and the full
naturality/truncation checks. Source references distinguish simplicial.tex
from Categories Tag 002F. All Lean lines are at most 100 characters.

H11: the table above matches every hypothesis and clause to its exact data or
conjunct, including the three previously omitted interfaces. I rechecked the
empty, `k=0`, `q>k`, boundary, collapse-map and universe cases against those
formulas. The external consumer check and clean compilation confirm that the
interfaces can be read and used outside this file. No statement dispute or
source-based statement correction remains; the repaired Lean renders the
original reviewed node without changing its mathematics.
