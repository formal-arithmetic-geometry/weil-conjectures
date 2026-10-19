## Worker report

The item is stated in `lean/Sheaf/TraceFormula/ConvexChainRationalRank.lean` as
`AddCommGroup.convexChainRationalRank`. It quantifies a type `Γ` with an additive
commutative group structure, a linear order, and `AddLeftMono Γ`, which is the
unbundled Mathlib encoding of a totally ordered abelian group. It takes a natural
number `n` and a family `H : Fin (n + 1) → AddSubgroup Γ`. The hypothesis `hconvex`
spells out the node's convexity clause: for every member `H i`, elements `h₁,h₂`
in that subgroup and an element `x` between them, `x` is in the subgroup. The
hypothesis `hstrict` gives each strict inclusion `H i.castSucc < H i.succ` for
`i : Fin n`, exactly the strict chain `H₀ ⊊ … ⊊ Hₙ`. The conclusion is
`Cardinal.lift (Cardinal.mk (Fin n)) ≤ AddCommGroup.rationalRank Γ`; the lift is
required because `Fin n` has universe `0` while the rational rank of `Γ : Type u`
is a cardinal in universe `u`, and it is the universe-correct Lean rendering of
the node's `Cardinal.mk (Fin n) ≤ rrk Γ`.

The proof is intentionally `sorry`, as required at stage 2. Its docstring records
the source route: choose positive representatives at strict inclusions, use
ordered-group torsion-freeness and convexity to obtain a linearly independent
family after rationalization, then apply the independent-family/cardinal-dimension
bound.

## Dependency modules

The recorded dependency `lem-trf-torsionfree-rationalization-injective` had no
Lean declaration (`lean: null`). I copied its node record and supplied
`lean/Sheaf/GroupTheory/TorsionfreeRationalizationInjective.lean`. That module
states the dependency exactly: `rationalizationMap` is the canonical additive
homomorphism `g ↦ 1 ⊗ g` into `ℚ ⊗[ℤ] G`, and
`rationalizationMap_injective` assumes that every positive integer multiple
annihilating an element forces that element to be zero, concluding injectivity.
The map is a real tensor-product construction; only the theorem proof is
postponed. The item imports this module and `Sheaf.GroupTheory.RationalRank`.
The rational-rank dependency uses the landed declaration
`AddCommGroup.rationalRank` in `Sheaf.GroupTheory.RationalRank`. The field
leaf is Mathlib's `Field` class. The independent-family proof dependency is the
Mathlib leaf `LinearIndependent.cardinal_lift_le_rank`, so it has no project
module to import.

## Edge cases

For `n = 0`, `Fin n` is empty, `hstrict` is vacuous, and the conclusion is the
zero-cardinal inequality. The formulation permits the zero group and rational
rank zero. It does not impose finite generation or finite rational rank, so it
also covers infinite-cardinal rational rank. The convexity condition includes
endpoints and all intermediate elements, and strictness is required at every
finite adjacent index only.

## Searches

I checked the shared DAG for duplicate nodes and searched the project and upstream
Lean trees with `rg -n 'convex|Convex|rationalRank|rational rank|convexChain'`.
The existing project declaration `AddCommGroup.rationalRank` was used. The item
search records inherited from the reviewed stage-1 split report no exact theorem:
LeanFinder query “strict chain of convex subgroups ordered abelian group bounded by
rational rank” returned Archimedean-subgroup hits only; Loogle query
“ConvexSubgroup rational rank ordered group” returned no usable match; grep for
`convex.*subgroup|Convex|archimedean.*rank` found no theorem; LeanSearch returned
only Archimedean-class and finitely-generated-rank results. The dependency search
for the canonical torsion-free tensor injection likewise found no exact Mathlib or
project declaration, so the dependency module above was added under stage-2 rule
(B). The exact search output is retained in `searches.jsonl`.


## Final self-check

The saved packet was retained. Both modules compiled in the first completed dry run.
Its two preflight diagnostics were signature-record mismatches: the preflight
extractor excludes the terminating `:=`. Removed only that delimiter from each
`lean.statement`, preserving the declaration signatures. The dependency record now
lists both the canonical map and its injectivity theorem. Expanded both theorem
docstrings to carry every proof step of their DAG nodes, and imported the dependency's
localization proof modules. No theorem was proved.

Re-read the current item, all three statement dependencies, the rational-rank
definition, the canonical tensor map, Mathlib's `Field`, the definition of
`AddLeftMono`, and `LinearIndependent.cardinal_lift_le_rank`. An additive commutative
group with linear order and left-monotone addition is exactly the ordered group
in the item; commutativity supplies monotonicity on the other side. The field
mention is contextual and introduces no separate field variable or extra assumption.
Tensor symmetry matches the dependency's `G ⊗ ℚ` with the recorded rationalization
`ℚ ⊗ G`; its canonical map is `g ↦ 1 ⊗ g`. In the dependency, `hT` quantifies every
integer `m > 0` and element `g`, assumes `m • g = 0`, and concludes `g = 0`; the
conclusion is injectivity of that specific canonical map. There is no arbitrary map
or additional module structure on `G`. Every type and universe variable is bound.
No statement correction or disputed statement was needed.

## Second reading by Q107

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
