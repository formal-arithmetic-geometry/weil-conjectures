## Worker report

Stated `Module.directSum_toModule_injective_of_filtration_successor_maps` in
`Sheaf.LinearAlgebra.FiltrationSuccessorMapsIndependent`. Its sole proof is `sorry`.
The docstring contains the five accepted proof steps. No definition, new node,
dependency repair, or statement correction is needed. Only the item's `lean`
record changes.

The prior ending was a stage-1 already-split refusal. The current standing brief
section 0 explicitly permits stage-2 statement work after that refusal. The node
has a passing stage-1 review by Q77/L, no Lean record, and a stage-2 queue entry.
Its reviewed statement and split are preserved.

Hypothesis and clause correspondence:

- A commutative ring is `(R : Type u) [CommRing R]`.
- The ambient R-module is `(X : Type v) [AddCommGroup X] [Module R X]`.
- A set ordinal is `(κ : Ordinal.{w})`; the stages through the endpoint are
  `(F : Set.Iic κ → Submodule R X)`.
- The increasing-family hypothesis is `(hmono : Monotone F)`, using the induced
  ordinal order on the interval subtype.
- The modules for every α < κ are `(A : Set.Iio κ → Type z)` with dependent
  `AddCommGroup` and `Module R` instances. The four universes are explicitly
  declared and independent.
- Each `t α` is a linear map from `A α` into the actual submodule
  `F ⟨Order.succ α.val, Order.succ_le_of_lt ... α.property⟩`.
  Ordinal successor is α + 1; its endpoint bound follows from α < κ.
- `hind` quantifies over every such α and every `a : A α`, requiring membership
  of `(t α a : X)` in `F ⟨α.val, le_of_lt ... α.property⟩` to imply `a = 0`.
- `DirectSum.toModule R (Set.Iio κ) X` takes the family of composites of `t α`
  with the successor submodule's `subtype` inclusion. This is exactly the
  linear map sending a finitely supported family to the sum of its component
  images in X. Its domain is Mathlib's `DirectSum (Set.Iio κ) A`, definitionally
  the dependent functions of finite support. The domain is inferred from `t`.
- `Function.Injective` is the asserted injectivity. For a linear map on a direct
  sum this is equivalent to the node's coordinate formulation: a zero-image
  family is zero, hence all its components vanish, and conversely injectivity
  follows by subtraction. This is one conclusion, not an additional assertion.
- There is no hypothesis that the initial stage is zero, that the endpoint is
  all of X, that limit stages are continuous, or that successors are generated
  by the given maps. None is hidden in the interval or module types.

Dependency declarations used:

`def-weil-pbc-direct-sum-modules` is a Mathlib leaf with a `mathlib_match`, so
its absence of `lean` is expected. I read the recorded source declarations:
`DirectSum` and `DirectSum.induction_on` in `Mathlib.Algebra.DirectSum.Basic`,
and the module instance, `DirectSum.lof`, and `DirectSum.component` in
`Mathlib.Algebra.DirectSum.Module`. These give finite support, componentwise
module operations, inclusions, and components exactly as the node requests.
The latter module is publicly imported; it publicly imports the former.
`DirectSum.toModule` in that same module constructs the finite-sum linear map;
its `toModule_lof` equation confirms its values on individual summands.
`Mathlib.SetTheory.Ordinal.Basic` supplies ordinal successor and the order facts.
The only proof dependency is the same direct-sum node, already imported.

Source checked: `literature/stacks-project/algebra.tex`, Tag 058V,
`lemma-direct-sum-devissage`, lines 20409–20455. Its injectivity paragraph
separates the last component and uses independence from the preceding stage.
The node's accepted maximal finite-support argument uses exactly this property
and does not require the other dévissage hypotheses used for surjectivity.

Edge cases checked before writing:

- κ = 0: the index subtype is empty, the direct sum is zero, and injectivity
  holds for every possible initial submodule, including a nonzero one.
- κ = 1: the assertion reduces to one map injective modulo F(0); in particular
  its ordinary kernel is zero since zero lies in F(0).
- A limit endpoint still gives a finite support with a largest index. No
  continuity or exhaustion is needed, and arbitrary gaps in the filtration
  are allowed.
- If adjacent stages agree, `hind` forces the corresponding source module
  to be zero; the statement remains correct.
- Zero modules, a zero ambient module, and the zero ring are included. No
  nontriviality, finite generation, projectivity, or characteristic assumption
  has been imposed.
- Without `hind`, two maps into the same stage can have equal nonzero values;
  their difference gives a nonzero kernel family. Thus the hypothesis is
  substantive and is not automatically discharged by a module instance.

Searches made on 2026-10-23:

1. `msearch.py` LeanFinder: “The sum of maps into successive ordinal filtration
   stages is injective when each map is injective modulo the preceding stage”.
   Eight hits: Nobeling injective_sum_to and projection maps, GoodProducts
   injectivity, CantorScheme and OrderedFinpartition injectivity. These concern
   different objects and hypotheses, not the general R-module assertion here.
2. `msearch.py` Loogle: `DirectSum, Function.Injective`. Six hits including
   `DirectSum.lmap_injective`, `map_injective`, `of_injective`, `mk_injective`,
   and `toAddMonoid_injective`. Componentwise maps between direct sums and
   single-component inclusions do not establish the stated sum into X.
3. `msearch.py` grep: `filtration.*[Ii]njective|[Ii]njective.*filtration|iSupIndep`
   in LinearAlgebra. Twenty-five hits on eigenspaces, ordinary independence,
   and `iSupIndep`/DFinsupp criteria. I read DFinsupp lines 480–565: the
   injectivity theorem assumes independence from all other summands, whereas
   deriving independence from the one-sided filtration condition is the work
   of this node. It is not an exact existing declaration.
4. `msearch.py` LeanSearch: “An ordinal indexed sum of linear maps is injective
   if each map into a successor submodule has zero kernel modulo the predecessor”.
   Eight hits, including the componentwise injection results, the iSupIndep
   criteria, and `DirectSum.toModule`. The latter is used for the canonical
   map; none states the requested filtration theorem.
5. `rg` in both project source roots for filtration/injectivity and successor
   independence found filtered-complex/injective-object results, and the
   stronger split-filtration linear equivalence, but no exact statement.
   The item-id search in both roots and `dag/lean_names_upstream.json` found
   no declaration for this item. Searching Mathlib LinearAlgebra and both
   project roots for successor-independence names also found no match.

Compilation: prescribed `scompile.py Q62` wrapper, both sandbox and actual
module-name checks passed cleanly. The first draft needed explicit ordinal
arguments on the successor bound; these are now present. Every variable and
universe is explicitly bound. No diagnostic commands remain in the module.

No statement fault or dispute found.

## Second reading by Q62

No second worker was started: the dispatch expressly forbids other agents.
The maintainer's independent review reads this delivery, as required by the
current direct-delivery brief. This section does not claim an independent
worker review.
