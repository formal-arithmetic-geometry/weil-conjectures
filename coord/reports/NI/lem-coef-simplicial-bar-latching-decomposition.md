## Worker report

Item: `lem-coef-simplicial-bar-latching-decomposition`.
Module: `Sheaf.CategoryTheory.SimplicialBarLatchingDecomposition`.
Main declaration: `CategoryTheory.simplicialBarLatchingDecomposition`.

The theorem states `Nonempty (SimplicialBarLatchingClaim (M := M) (I := I))`.
The structure spells out the canonical bar construction, the actual latching colimit,
its degenerate-chain identification, the complementary nondegenerate summand, and both
naturalities. The sole postponed proof is this theorem, with the node's eight-step
natural-language proof in its docstring. Definitions have real data; structures specify
the data and equations asserted to exist by the theorem. There is no definition choosing
an object from this existence theorem.

This is an interface repair of the module already present on the base, rather than a
second definition or an `existing: true` rebinding. The old `decomposition` field asserted
only a pointwise `Nonempty` isomorphism to a sum-indexed coproduct; it did not identify the
isomorphism on the two summands or state its naturality. The old latching isomorphism was
not characterized on all latching injections, and degree-zero initiality was implicit.
The replacement uses Mathlib's colimit definition directly and specifies all these maps.
The target category's morphism universe and the small index category's universe are now
independent. No natural-language statement or dependency list is changed.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Small category `I` | `{I : Type w} [SmallCategory I]`, with arbitrary explicitly bound `w`. |
| Category `M` with all small coproducts | `{M : Type u} [Category.{v} M] [HasCoproducts.{w} M]`; `u`, `v`, and `w` are independent. Only coproducts indexed at the size of `I` are used. |
| Any functor `V : I → M` | Quantification over `I ⥤ M` in the claim's fields; the outer `stage` functor encodes dependence on `V`. |
| Simplex category and all nonnegative degrees | Mathlib `SimplexCategory`, `op ⦋n⦌`, and `n : ℕ`. |
| Chains `i₀ → ... → iₙ → j` with labels `V(i₀)` | `ComposableArrows (Over j) n` and `V.obj ((c.obj 0).left)` in `simplicialBarStage`. An `n`-chain in `Over j` is exactly a forward chain with final arrow to `j`; all earlier arrows to `j` are forced composites. |
| `SₙV(j)` is that coproduct | `stageIso` identifies the functorial bar with the actual `Sigma` coproduct `simplicialBarStage`. |
| Surjection repeats vertices, inserts identities, retains final arrow, acts identically on the label | `stageOperator` uses `(nerve (Over j)).map a.op`. It states the formula even for general ordinal maps; for a surjection `a(0)=0`, its leading `V.map` is the identity. Precomposition repeats vertices and sends repeated adjacent indices to identity arrows. The overcategory structure retains the final arrow. This is the canonical simplicial bar, not an arbitrary operator. |
| Objects of `Dₙ` are proper surjections | `simplicialBarProperSurjections n` is the object property on `Under ⦋n⦌` requiring `Function.Surjective θ.hom.toOrderHom` and `θ.right.len < n`. |
| Arrows `θ → θ'` are surjections `ρ : [a'] → [a]` with `θ = ρθ'` | `simplicialBarLatchingIndex n` is the opposite of that full subcategory. An underlying undercategory arrow goes from `θ'` to `θ`, with `θ'.hom ≫ ρ = θ.hom`. Its `ρ` is automatically surjective: the composite is surjective. Thus taking the full subcategory introduces no extra arrows. |
| Latching diagram `θ ↦ SₐV(j)`, insertion along `ρ` | `simplicialBarLatchingDegrees n ⋙ stage.obj V ⋙ (evaluation I M).obj j`; its maps are the bar's ordinal operators already characterized by `stageOperator`. |
| Canonical cocone to degree `n` | `simplicialBarCanonicalLatchingCocone` maps the opposite of `Under.forgetCone` through the bar. Its legs are exactly the proper-surjection insertion maps. |
| The latching diagram has a colimit | `latchingCocone` with point `((degenerate n).obj.obj V).obj j`, and `latchingIsColimit : IsColimit (Cocone.mk ... ...)`. No arbitrary-colimits assumption is made. |
| Colimit identified canonically with the degenerate-chain coproduct | `(degenerate n).iso V j` identifies the point with the literal subtype-indexed coproduct. `latchingInjection` characterizes every cocone leg on every source-chain injection, with `insertionDegenerate` supplying the canonical subtype membership. This fixes the comparison independently of any possible failure of monicity. |
| Canonical map to degree `n` is the coproduct injection | `degenerateInclusion_eq` gives its formula on every degenerate-chain injection; `latchingMap` identifies its composite with every latching leg with the actual canonical cocone. |
| `NₙV(j)` is the coproduct of chains with no identity internal arrows | `nondegenerate` is a `SimplicialBarSummand` with predicate `simplicialBarNondegenerateAt n`; its `iso` has target definitionally `simplicialBarNondegenerateStage V n j`. The degenerate predicate is its logical complement. |
| Canonical decomposition `SₙV(j) ≅ LₙS(j) ⨿ NₙV(j)` | `decomposition` asserts `IsColimit` of the `BinaryCofan.mk` formed by the two specified inclusions with vertex the degree-`n` bar. This is the universal-property form of precisely that canonical coproduct isomorphism, including its two injection equations. It also supplies the binary coproduct without asking for any further instance. |
| Test only the internal arrows | `simplicialBarNondegenerateAt` quantifies `k : Fin n` and tests `c.map' k (k+1)` against `eqToHom h`. Equality of objects is handled dependently. It never tests `(c.obj (Fin.last n)).hom`, the final arrow. Identity internal arrows in `Over j` correspond exactly to identity internal arrows in `I`. |
| Naturality under postcomposition in `j` | `stagePostcompose`, `SimplicialBarSummand.postcomposeIndex` and `.postcompose` specify the chain and label actions. `degenerateInclusion` and `nondegenerateInclusion` have components which are natural transformations of `I`-functors. `latchingPostcompose` explicitly states the square on every latching leg. |
| Naturality under `η : V → W` | `stageMap` and `SimplicialBarSummand.map` specify `η.app i₀` on each label. Both inclusions are outer natural transformations of coefficient-diagram functors. `latchingMapCoefficient` explicitly states the square on every latching leg. Consequently both the colimit identification and the binary coproduct comparison commute with the stipulated maps. |
| `n=0`: empty `D₀` and initial `L₀` | `θ.right.len < 0` is impossible, so `simplicialBarLatchingIndex 0` has no objects. `zero` explicitly asserts `IsInitial` of the latching point. The internal predicate over `Fin 0` is vacuous and the degenerate family is empty. |
| No model structure, cofibrancy, images, or monic injections | No such typeclasses, hypotheses, or fields occur. The comparisons use only coproduct injections and Mathlib colimit universal properties. |

### Dependencies and source reading

Read both statement-dependency nodes and their recorded interfaces:

- `def-weil-pbc-simplicial-set`: Mathlib `SSet` in
  `Mathlib.AlgebraicTopology.SimplicialSet.Basic`; `SSet.degenerate` and
  `SSet.nonDegenerate` in `.Degenerate`; `SSet.Subcomplex` in `.Subcomplex` and
  `SSet.Finite` in `.Finite`. Read their definitions and docstrings. The statement uses
  Mathlib's simplex category and nerve; it does not copy the definition of a simplicial set.
- `def-weil-pbc-category-colimit`: `CategoryTheory.Limits.Cocone`, `IsColimit`,
  and `colimit` from the `Mathlib.CategoryTheory.Limits` modules (recorded module
  `.HasLimits`). Read their complete signatures/docstrings, including `colimit.desc`
  and `CategoryTheory.IsFiltered` for the node's other clauses. The latching theorem
  uses actual `Cocone` and `IsColimit`, not a private universal-property definition.
- Proof dependency `lem-weil-pbc-simplicial-set-nondegenerate-decomposition`:
  read `SSet.exists_nonDegenerate`, `unique_nonDegenerate_dim`,
  `unique_nonDegenerate_simplex`, and `unique_nonDegenerate_map` in `.Degenerate`.
  That module is imported without `public` because these are proof dependencies.

Also read Mathlib `CategoryTheory.nerve`, `ComposableArrows`, `Under.forgetCone`,
`ObjectProperty.FullSubcategory`, `BinaryCofan`, and the candidate
`SimplicialObject.Splitting` interface. Read Stacks `simplicial.tex`,
`lemma-splitting-simplicial-sets` (Tag 017R), and its proof. Opened the specified
[Dugger PDF](https://pages.uoregon.edu/ddugger/hocolim.pdf): Definition 13.8 describes
the latching category and its canonical map; Remark 4.4 describes the identity-chain
summands; Remark 9.12 fixes the forward-chain/first-label convention. The general
coproduct formulation and eight proof steps are exactly those of the supplied DAG node.

### Edge cases

- `n=0`: no proper surjection, no internal arrow, empty degenerate coproduct and all
  final arrows (including identities) allowed in the nondegenerate coproduct.
- Empty `I`: the endpoint quantifiers are empty, and coefficient/bar functors remain
  well-typed. No `Nonempty I` was added.
- Terminal one-object category: in positive degrees every chain is degenerate, whereas
  at degree zero every chain is nondegenerate. The decomposition has exactly the
  expected empty complementary family.
- A nonidentity arrow `a → b` followed by final identity `b → b` is nondegenerate.
  Thus the final arrow is not accidentally tested.
- Multiple internal identities have several latching presentations. The diagram has
  their factorization arrows, and `IsColimit` requires compatibility with every one;
  unique nondegenerate normal form handles their overlap in the postponed proof.
- Nonidentity automorphisms and mutually inverse arrows remain nondegenerate when all
  individual internal arrows are nonidentity, even if some composites are identities.
- Nonmonic postcomposition `j → k` can identify final arrows, but retains each internal
  arrow and reflects whether it is an identity. The summand action is therefore valid
  for arbitrary endpoint arrows, not only monomorphisms.
- No zero object or disjointness/monicity property of coproducts is used. Universe `w`
  is not identified with `u` or `v`.

### Searches

Ran the prescribed `msearch.py NI lem-coef-simplicial-bar-latching-decomposition`:

| Tool | Query | Result |
| --- | --- | --- |
| leanfinder | `The latching colimit of the simplicial bar construction is the coproduct of chains with an identity internal arrow` | 8 hits: Dold-Kan Gamma constructions and `SimplicialObject.Splitting.isColimit'`; these require additive chain complexes or an already supplied splitting, not the arbitrary-category labelled-chain latching calculation. |
| loogle | `"SimplicialObject.Splitting"` | 12 hits defining splittings, their indices, cofans, and isomorphism transport. Read `Split.lean`; these supply no such bar construction or latching colimit. |
| grep | `latching.*nondegenerate|nondegenerate.*latching` | 0 Mathlib hits. |
| leansearch | `The latching object of the simplicial bar construction is the coproduct of chains containing an identity internal arrow` | 8 hits on homological identity squares, augmented constant simplicial objects, simplicial identities, and splitting indices; no exact match. |

Local `rg` for `simplicialBar`, `bar.*[Ll]atching`, and `[Ll]atching.*bar` in the
upstream `WeilConjectures` and side `lean/Sheaf` trees found the previously landed
module of this same item; its missing canonicality/naturality clauses are explained
above. `grep -rn` for the full blueprint id in upstream returned no match.
Checked the upstream name index and searched every newly introduced helper name
in Mathlib, upstream, and side sources: no collision or independently owned notion.
The existing `SimplicialBarLatchingClaim` is replaced in its owning module rather
than duplicated. Searches for the removed old internal helpers found no external
consumers. No new nodes or dependency modules are needed: all helpers implement
objects introduced explicitly in this item's own statement.

### Validation

Compiled the complete module with the prescribed `scompile.py` wrapper; both sandbox
and module-path checks pass with no errors or warnings. All variables and universes
are explicit with `autoImplicit false`. The only theorem has proof `by sorry`.
The node copy changes only `lean`; no statement correction or disputed statement is
needed. The delivery dry run and push are recorded by the launcher tools.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
