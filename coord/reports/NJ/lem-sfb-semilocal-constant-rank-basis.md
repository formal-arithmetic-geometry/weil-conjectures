## Worker report

The module `Sheaf.RingTheory.SemilocalConstantRankBasis` states
`Module.semilocal_constant_rank_basis`, with its proof postponed by `sorry`.
It makes no definitions. The node is unchanged except for its `lean` record.
The source is Stacks Project, Algebra, Tag 02M9,
`lemma-locally-free-semi-local-free` (read in `literature/stacks-project/algebra.tex`,
lines 19290–19305). The theorem records the node's explicit constant-rank finite
principal-cover formulation. The declaration docstring carries all five proof
steps, including the Chinese-remainder weights and the zero-ring case.

Hypotheses and conclusion, clause by clause:

- A commutative ring: `{R : Type u} [CommRing R]`.
- Semilocal means finitely many maximal ideals: `[Finite (MaximalSpectrum R)]`.
  Mathlib's `MaximalSpectrum R` is precisely the type of maximal ideals, so this
  does not impose Noetherianity, a product decomposition, or a local-ring condition.
- An arbitrary `R`-module: `{M : Type v} [AddCommGroup M] [Module R M]`.
  The module universe is independent of the ring universe.
- The nonnegative integer rank: `n : ℕ`.
- Finitely many elements: `m : ℕ` and `t : Fin m → R`.
  Binding a chosen finite cover is the implication form of the node's existential
  cover hypothesis: every witness to that hypothesis gives the same conclusion.
- They generate the unit ideal: `ht : Ideal.span (Set.range t) = ⊤`.
- For every member, localization is free with exactly `n` basis vectors:
  `hfree : ∀ i : Fin m, Nonempty (Module.Basis (Fin n)
  (Localization.Away (t i)) (LocalizedModule.Away (t i) M))`.
  The scalar action is Mathlib's canonical localized-module action.
- The conclusion is `Nonempty (Module.Basis (Fin n) R M)`.
  `Fin n` indexes exactly `n` elements; relabeling it by `1,...,n` does not change
  the assertion. `Module.Basis.repr` is an equivalence to `Fin n →₀ R`, so this
  also expresses the node's equivalent `M ≅ R^{⊕n}` clause. No second conclusion
  or extra hypothesis is imposed.

Statement dependency declarations read and used:

- `def-weil-ring-localization-away`: `Localization.Away`,
  `Mathlib.GroupTheory.MonoidLocalization.Away`; the recorded abbreviation
  localizes at `Submonoid.powers (t i)`.
- `def-weil-pbc-module-localization-away`: `LocalizedModule.Away`,
  `Mathlib.Algebra.Module.LocalizedModule.Basic`; the recorded abbreviation
  is the actual fraction localization of `M` at the same powers.
- `def-weil-pbc-free-module`: `Module.Free`,
  `Mathlib.LinearAlgebra.FreeModule.Basic`. Its data is existence of
  `Module.Basis`; the more precise fixed-index basis is used here because the
  node specifies the cardinality. `Module.Basis` represents a coordinate linear
  equivalence, rather than only linear independence or spanning.

The module also publicly imports `Mathlib.RingTheory.Spectrum.Maximal.Defs`
for `MaximalSpectrum`. Both already-stated proof dependencies are plain imports:
`Sheaf.RingTheory.LocalTrivializationResidueRank` provides
`Module.local_trivialization_residue_rank`, and
`Sheaf.RingTheory.BasisOfMaximalResidueBases` provides
`Module.bijective_linearCombination_of_maximal_residue_bases`.
Their full declarations and proof docstrings were read. These interfaces supply
exactly the local basis/residue-rank step and prescribed global-basis step.
No dependency repair or new node is needed.

Edge cases checked before writing:

- Zero ring: no `Nontrivial R` assumption appears. Every module over it is zero;
  the coordinate module is also zero, and has the asserted basis for any `n`.
- Empty cover: `m = 0` makes `hfree` vacuous, and `ht` becomes `⊥ = ⊤`, which
  forces the zero-ring case. The theorem therefore admits exactly the node's
  empty-cover case, without assuming a nonempty index type.
- Rank zero: `Fin 0` is empty; the hypothesis says all localizations vanish,
  and the conclusion is the empty basis of the zero module.
- One maximal ideal: the Chinese-remainder product is the empty product `1`.
- Repeated or zero cover elements are allowed. A zero localization is the zero
  module over the zero ring and imposes no unintended nontriviality condition.
- Independent universes `u` and `v` cover arbitrary module sizes. Both are
  explicitly bound and `autoImplicit` is disabled.

Searches for an existing exact statement:

- `msearch.py leanfinder`: "A module free of constant rank n on a finite principal
  cover over a semilocal ring has a basis with n elements". Eight hits, led by
  `Module.nonempty_basis_of_flat_of_finrank_eq`; the others concerned PID bases,
  `Module.finBasis`, or submodule bases. No exact principal-cover statement.
- `msearch.py loogle`: `Module.nonempty_basis_of_flat_of_finrank_eq`. One hit.
  Read its full signature and docstring in `Mathlib/RingTheory/LocalRing/Module.lean`.
  It assumes `Module.Finite R M`, `Module.Flat R M`, and specified residue tensor
  dimensions. Converting our cover to those hypotheses requires additional
  mathematics, so the existing declaration cannot directly record this node.
- `msearch.py leansearch`: "A semilocal ring module trivialized with rank n on a
  finite principal open cover has a basis indexed by Fin n". Eight hits including
  the same finite-flat theorem and general basis constructors; no exact match.
- `msearch.py grep`: `nonempty_basis.*|semilocal|SemiLocal` in
  `RingTheory/LocalRing`. Three hits, all related to the same finite-flat theorem.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `semilocal|semiLocal|SemiLocal|constant_rank_basis|basis.*principal|principal.*basis`
  found related semilocal submodule, restriction-length, normalization and
  geometric rank material. In particular the upstream `FlatRank.lean` theorem
  `Module.finrank_eq_mul_of_rankAtStalk_eq` is a rank multiplication statement
  with finite-flat algebra hypotheses, not this assertion.
- Search of upstream sources for this item's id returned no hit. Searches of
  Mathlib, upstream, Sheaf, and `dag/lean_names_upstream.json` for
  `nonempty_basis_of_principal|nonempty_basis_of_semilocal|semilocal_constant_rank_basis`
  found no pre-existing declaration under the proposed name.

No statement dispute, correction, or node fault was found.

Validation: `scompile.py NJ lem-sfb-semilocal-constant-rank-basis` compiled the
module in sandbox and library mode against the live published server build,
with no errors or warnings. No local compilation or global build was run.

## Second reading by NJ

A separate self-review pass compared the final source with the node and its three
recorded notions. This is not represented as an independent second worker's
review; the dispatcher brief assigns the independent review to the maintainer.
The comparison checked `[Finite (MaximalSpectrum R)]`, both module universes,
`n m : ℕ`, the unit ideal hypothesis, every localized basis scalar and carrier,
and the global `Fin n` basis conclusion. All clauses match. In particular there
is no `[Nontrivial R]`, `[Nonempty (Fin m)]`, finite-module hypothesis, flatness
hypothesis, or positivity restriction. The `R^{⊕n}` wording is the equivalent
coordinate description of the same basis, not an omitted additional assertion.
No mathematical changes were needed. Before the final compile, an unused direct
prime-localization import was removed and the maximal-spectrum import reduced
to its definitions module. The full five-step proof docstring was checked against
the node's proof, including the non-idempotent Chinese-remainder weights.
