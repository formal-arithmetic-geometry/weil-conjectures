## Worker report

The module `Sheaf.CategoryTheory.SurjectiveTowerLimitAcyclic` states
`CategoryTheory.surjectiveTowerLimitAcyclic`. It represents an inverse system indexed by
`ℕᵒᵖ` (the paper's levels `n ≥ 1` are `n : ℕ`), with abelian-group values in
`AddCommGrpCat`. The hypothesis `hB` renders the clause that every transition
`g_n : B_{n+1} → B_n` is surjective, using
`Function.Surjective (B.map (homOfLE (Nat.le_add_right n 1)).op)`. The conclusion
`∀ q : ℕ, 1 ≤ q → IsZero (...)` renders vanishing of every right derived inverse
limit `R^q lim B` for `q ≥ 1`; the functor is the categorical inverse-limit functor
`lim` and right derived functors are `rightDerived`.

The declaration uses the dependency declarations `CategoryTheory.roosTowerEnoughInjectives`
from `Sheaf.CategoryTheory.DerivedLimitRoosAbelianGroups`,
`CategoryTheory.towerLimitAdditiveLeftExact` from
`Sheaf.CategoryTheory.Limits.TowerLimitAdditiveLeftExact`, and the tower-category
and derived-functor notions supplied by Mathlib (`ℕᵒᵖ ⥤ AddCommGrpCat`, `lim`,
`Functor.rightDerived`, `IsZero`). The local additive instance is obtained from
`towerLimitAdditiveLeftExact.1`; the local enough-injectives instance is
`roosTowerEnoughInjectives`.

Edge cases checked: `q = 1` is included; `q = 0` is excluded by `1 ≤ q`; the
empty-index issue does not arise because `ℕ` is nonempty and represents the paper's
positive levels; arbitrary universe `u` is retained; the zero tower satisfies the
surjectivity hypothesis and the conclusion.

Searches for an existing declaration: `msearch.py F1 lem-pc-tower-surjective-lim-acyclic
leanfinder "surjective transition maps inverse system abelian groups derived inverse limit acyclic"`
found only surjectivity lemmas for limits of types, with no derived-limit theorem;
`msearch.py ... loogle "CategoryTheory inverse limit derived functor surjective"` returned
no hits; grep of Mathlib for `Mittag`, `lim^1`, and derived inverse-limit terms found no
such AddCommGrp tower theorem; `rg` over `WeilConjectures` and `lean/Sheaf` found no
existing declaration of this node. Thus a new statement module is required.

No statement correction or disputed statement was needed.

## Earlier second reading (a previous round; superseded)

The node and module were read together. `B` is exactly the inverse system of abelian
groups, and `hB` quantifies every consecutive transition with the correct opposite
arrow. The `rightDerived` expression is the right-derived functor of the inverse-limit
functor on the tower category, and `IsZero` states the node's zero conclusion for every
positive degree. No hypothesis or clause is added or omitted; the indexing convention
covers all levels `n ≥ 1` via `n : ℕ`.

## Second reading by F1

I independently opened the item node, its module, all five statement-dependency
nodes and their recorded declarations. The node introduces the following objects,
hypothesis and conclusion; each matches the Lean:

- The inverse system `(B_n,g_n)` of abelian groups at positive integer levels:
  `B : ℕᵒᵖ ⥤ AddCommGrpCat.{u}`. The level `n` in Lean denotes the paper's
  level `n+1`. Mathlib `Functor.ofOpSequence` and `NatTrans.ofOpSequence` in
  `Mathlib.CategoryTheory.Functor.OfSequence` implement exactly the tower and
  its levelwise compatible morphisms recorded by `def-weil-inverse-system`.
  Arbitrary functors of this shape, rather than a special constructor image,
  are allowed. Verdict: exact.
- Every consecutive transition `g_n : B_{n+1} → B_n` is surjective:
  `hB : ∀ n : ℕ, Function.Surjective
  (B.map (homOfLE (Nat.le_add_right n 1)).op)`. The preorder arrow points
  from `n` to `n+1`; its opposite points from `op (n+1)` to `op n`.
  The coercion is the underlying function of an additive homomorphism.
  Verdict: exact, no additional hypothesis on `B`.
- The ambient tower category is abelian: Mathlib
  `CategoryTheory.Abelian.functorCategoryAbelian` applies to the functor category,
  with the abelian instance of `AddCommGrpCat` in
  `Mathlib.Algebra.Category.Grp.Abelian`. Verdict: matches `lem-pc-tower-abelian`.
- This category has enough injectives: the exact signature
  `roosTowerEnoughInjectives : EnoughInjectives (ℕᵒᵖ ⥤ AddCommGrpCat.{u})`
  in `Sheaf.CategoryTheory.DerivedLimitRoosAbelianGroups` supplies a local
  instance. Mathlib's injective-resolution instance converts enough injectives
  into `HasInjectiveResolutions`; it is not an extra theorem hypothesis.
  Verdict: matches `lem-pc-tower-enough-injectives`.
- The inverse-limit functor is additive and left exact:
  `towerLimitAdditiveLeftExact` in
  `Sheaf.CategoryTheory.Limits.TowerLimitAdditiveLeftExact` states `.Additive ∧
  PreservesFiniteLimits` for exactly this `lim`. Its first projection supplies
  the local additive instance. Mathlib `lim.obj B` is `limit B` and its map is
  `limMap`; this is the categorical inverse limit, not a product.
  Verdict: matches `lem-pc-tower-limit-left-exact`.
- Right derived functors mean cohomology after applying the functor to an
  injective resolution: Mathlib `Functor.rightDerived` in
  `Mathlib.CategoryTheory.Abelian.RightDerived`, read together with
  `InjectiveResolution.isoRightDerivedObj`, has precisely this meaning.
  Verdict: matches `def-sp-left-exact-additive`.
- Every positive-degree derived limit vanishes:
  `∀ q : ℕ, 1 ≤ q → IsZero (((lim :
  (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).rightDerived q).obj B)`.
  `IsZero` means a zero object (equivalently its identity is zero), hence the
  zero abelian group; literal equality with a chosen zero object would be
  inappropriate. The degree quantifier follows the tower and its hypothesis.
  Verdict: exact, every conclusion clause present.

Source check: the repository's `literature/stacks-project/` is absent on this
machine. I read the local Stacks source copy
`/home/ubuntu/c1-stacks-review/more-algebra.tex`, section `Rlim of abelian groups`,
label `lemma-compute-Rlim` (Tag 07KW, confirmed in that copy's `tags/tags`).
It introduces all inverse systems of abelian groups, imposes no finiteness,
Noetherian, characteristic, field or scheme hypothesis, and asserts both higher
vanishing above degree one and right acyclicity of ML systems. Surjective towers
are ML. I also read `algebra.tex`, label `lemma-ML-exact-sequence` (Tag 0598:
countable directed index and ML kernel), and `derived.tex`, label
`proposition-enough-acyclics` (Tag 05TA: additive functor between abelian
categories). Countability is supplied by `ℕ`; the Lean conclusion is the source's
surjective special case selected by the node, not the whole ML claim.

Edge cases: the fixed index is nonempty, so an empty index set is not within the
node. Lean `n=0` is paper level 1 and includes the first transition. Degree `q=0`
is excluded exactly by `1 ≤ q`; degree 1 and all larger degrees are included.
The zero tower is allowed and has surjective transitions. Universe `u` is explicit
and arbitrary, including `u=0`; no group-size restriction is added. Empty schemes
and characteristic cases are inapplicable because no scheme or ring parameter is
introduced. Every variable and universe is explicitly bound.

Independent searches, using different query words from the worker:
`msearch.py ... leanfinder "Mittag Leffler countable abelian group tower higher
right derived limit zero"` returned eight candidates, including
`Functor.isZero_rightDerived_obj_injective_succ` (requires an injective object,
not a surjective tower), Grothendieck-category results and direct-limit results;
none states this node. `msearch.py ... loogle '"rightDerived", "IsZero"'`
returned only the injective-object vanishing theorem. LeanSearch with
"A countable inverse system of abelian groups with onto maps has zero positive
derived limits" was unavailable (Internal Server Error); no negative verdict
is inferred from that failure. `rg` for `surjectiveTowerLimitAcyclic`,
`limAcyclic`, `LimitAcyclic`, `Mittag`, and both orders of `lim`/`rightDerived`
over Mathlib CategoryTheory, the source `WeilConjectures`, and project `lean/Sheaf`
found type-valued ML theory, the project's Roos computation and Milnor sequence,
and no exact existing theorem. The Roos theorem vanishes above degree one for
all towers, but does not give degree-one vanishing for surjective towers, so
cannot replace this item. No new definition node or dependency module is needed.

Mismatches and repairs: the signature and node record were already correct and
are unchanged. Removed unused imports `InjectiveSplitTower` and
`InjectiveTowerEmbedding`. The additive instance lacked a source/blueprint
docstring and was exported globally; documented it and made it local. It is
only the projection of the dependency theorem, with no new notion or hollow data.
The theorem's proof docstring compressed the node's three steps and omitted the
named tools and the limit-surjectivity base-case argument; replaced it with the
complete three-step natural-language proof and dependency ids. The only theorem
proof remains `by sorry`; no statement is proved or weakened. There is no
statement correction and no disputed statement.
