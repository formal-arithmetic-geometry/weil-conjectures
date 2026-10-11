## Worker report

The module states `IsLocalRing.depth_le_supportDim`.  It uses Mathlib's
`Module.supportDim R M`, whose support is the set of primes where localization is
nonzero and whose Krull dimension is the supremum of lengths of strict prime chains.
The explicit nonzero hypothesis is rendered by `[Nontrivial M]`; finite generation by
`[Module.Finite R M]`; commutativity, Noetherianity, and locality by
`[CommRing R] [IsNoetherianRing R] [IsLocalRing R]`.  The conclusion is the node's
inequality, with the depth coerced from `ℕ∞` to `WithBot ℕ∞`, the codomain of
`Module.supportDim`.

The dependency declarations used are `Sheaf.RingTheory.Depth` (`IsLocalRing.depth`),
Mathlib `IsNoetherianRing`, Mathlib `Module.Finite`, Mathlib `LocalizedModule` as the
localization notion underlying support, and Mathlib `Module.supportDim`.

Edge cases checked: `[Nontrivial M]` excludes the zero module (whose support dimension
is `⊥`); support dimension may be infinite; depth may be `∞`, and the coercion in the
conclusion handles both cases.  No finite-dimensional or positive-dimension assumption
is added.

Searches: `msearch.py leanfinder` for depth bounded by support dimension (no depth
statement; candidates `Module.supportDim_*`); `msearch.py loogle` for
`RingTheory.Sequence.IsRegular, Module.supportDim` (only the regular-sequence support
formula); grep of Mathlib for depth (no declaration); grep of `WeilConjectures/` and
`lean/Sheaf` (the only project depth declaration is `Sheaf.RingTheory.Depth`, and no
existing theorem for this node).  `Module.supportDim` was inspected in
`Mathlib/RingTheory/KrullDimension/Module.lean` and confirmed to be the Krull dimension
of `Module.support`.

## Second reading by M1

Independent reading against the node and Stacks Algebra Tag 00LK,
`lemma-bound-depth`; read the source in `/home/ubuntu/c1-stacks-review/algebra.tex`
lines 17760–17835 (the repository's literature checkout is absent). The tags table
maps 00LK to `algebra-lemma-bound-depth`. The source introduces exactly a Noetherian
local ring and a nonzero finite module, with no additional standing field,
characteristic, dimension, or finiteness hypothesis. Verdict: the signature says
exactly what the node and source say; no statement correction is needed.

Object/hypothesis/conclusion checklist:

- Commutative ring `R`: `{R : Type u} [CommRing R]`. Exact.
- Noetherian: `[IsNoetherianRing R]`. Opened the recorded Mathlib declaration in
  `RingTheory/Noetherian/Defs.lean`: it is `IsNoetherian R R`, equivalently every
  ideal is finitely generated. Exact match for def-weil-pbc-noetherian-ring.
- Unique maximal ideal `m`: `[IsLocalRing R]`. Opened
  `RingTheory/LocalRing/Defs.lean`; the class includes ring nontriviality and the
  local-ring condition, and supplies the canonical maximal ideal. Naming `m`
  separately would add no data to this statement. Exact.
- Finite `R`-module `M`: `(M : Type v) [AddCommGroup M] [Module R M]
  [Module.Finite R M]`. Opened the dependency's recorded Mathlib declaration in
  `RingTheory/Finiteness/Defs.lean`: the top submodule is finitely generated.
  This is finite generation, not finiteness of the underlying set. Exact.
- Nonzero `M`: `[Nontrivial M]`. A module is zero exactly when its underlying
  additive group is subsingleton. Exact.
- Support at primes, with localization at their complements: `Module.supportDim
  R M`. Opened `RingTheory/KrullDimension/Module.lean`, `RingTheory/Support.lean`,
  and the dependency's `Algebra/Module/LocalizedModule/Basic.lean`.
  `supportDim` is `Order.krullDim (Module.support R M)`; support is exactly primes
  whose `LocalizedModule p.asIdeal.primeCompl M` is nontrivial. Localization is
  the fraction construction, with `mk_eq` giving the required equivalence
  relation. No private localization or support notion is introduced. Exact.
- Dimension as supremum of chain lengths: opened `Order/KrullDimension.lean`.
  `krullDim` is the supremum of `LTSeries.length`, counting strict inclusions
  among `n + 1` entries. The subtype of support has the inherited prime order.
  Exact, including unbounded lengths.
- Local depth: `IsLocalRing.depth (R := R) M`. Opened the dependency node and
  `Sheaf.RingTheory.Depth`: this is `(maximalIdeal R).depth M`; `Ideal.depth`
  takes the supremum of regular-sequence lengths when `IM ≠ M` and infinity
  when `IM = M`. It uses the recorded regular-sequence notion. Exact.
- Conclusion: `(IsLocalRing.depth (R := R) M : WithBot ℕ∞) ≤
  Module.supportDim R M`. This reverses the written `dimension ≥ depth` only
  typographically. The canonical coercion embeds extended natural numbers in
  the dimension's codomain and adds no hypothesis. Exact single conclusion.

Edge cases: the zero module is excluded by the node and `[Nontrivial M]` alike;
its dimension would otherwise be bottom and its depth infinity. The zero ring
admits no nonzero module and is not a local ring under the stated convention.
Nonzero modules have nonempty support, so bottom is not an extra dimension case.
Depth zero, dimension zero, the empty regular sequence, and infinite depth or
support dimension are represented without extra binders or bounds. There is no
index set or scheme in this node, so empty index sets and empty schemes are not
applicable. No restriction on characteristic is present. Independent universes
`u v` cover ring and module sizes with no `Small` assumption. All variables and
universes are explicitly bound.

Independent searches, with different wording from the first worker:

- `msearch.py ... leanfinder "local module depth upper bound Krull dimension
  annihilator"`: eight candidates, including support dimension versus ring
  dimension and the quotient-annihilator formula; no depth bound theorem.
- `msearch.py ... loogle "IsLocalRing.depth"`: six results from the service's
  newer `Mathlib.RingTheory.Depth.Basic`, including a regular-sequence supremum
  formula, but no desired theorem. This module and these declarations do not
  exist in the pinned source tree: the service index is not the project version.
- `msearch.py ... leansearch "depth of a finite nonzero module is bounded above
  by dimension of support over a Noetherian local ring"`: unavailable, HTTP
  Internal Server Error; no absence conclusion drawn from this service.
- `rg` for `(theorem|lemma|def).*depth`, `depth.*supportDim`, and
  `supportDim.*depth` in pinned Mathlib RingTheory, all upstream
  `WeilConjectures`, and repository `lean/Sheaf`: no existing statement.
  Inspected upstream `Regular/ProjectiveDimension.lean` depth references:
  prose only, not a declaration of this inequality. Checked the upstream name
  index for the proposed name and depth/dimension combinations: no match.
  The pinned project depth definition is the recorded dependency and is reused.

Mismatches found and repairs: H8/H9, missing copyright/header and module source
comment; H8, theorem docstring omitted the node's complete natural-language
proof. Added the standard header and module source docstring, and expanded the
theorem docstring with all five proof steps and their dependency node ids.
The signature, imports, theorem name, and node record were already right and
were preserved. No new nodes, dependency modules, definitions, private copies,
or proofs were added; the only theorem body remains `by sorry`. The node's
`lean.statement` is verbatim the unchanged signature before `:=`.

Validation: `scompile.py M1 lem-weil-pbc-depth-le-support-dimension
lean/Sheaf/RingTheory/DepthLeSupportDimension.lean` compiled the repaired module
cleanly on the server (exit 0, no warnings). Lines are at most 100 characters.
