## Worker report

The module `Sheaf.Combinatorics.ProductChainProperIntervalHomology` constructs the
complex A(m) introduced in this item's statement and states
`ProductChainProperInterval.homology`. All objects and differentials have actual
data. The only postponed proofs are `boundary_squared` (the alternating-deletion
square-zero assertion in the item's proof step 1) and `homology` (the item's two
homology calculations). Both have source and complete proof docstrings. All nine
public declarations are listed in `lean.declarations`. No new mathematical notion
beyond the complex introduced in this item is required. No node statement or
dependency list was changed.

The source paragraph (3) of
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`
was opened. It supplies the direct-image motivation, not this combinatorial
calculation. The module honestly follows the agent-formulated statement and all
seven proof steps already recorded in the node. The exact external combinatorial
reference remains WANTED as in the original node; no quotation from it is claimed.

Hypothesis and clause correspondence:

- r >= 1 is `(hr : 1 ≤ r)`, with `r : ℕ` explicitly bound. The tuple is
  `(m : Fin r → ℕ)` and nonzero is `(hm : m ≠ 0)`.
- `ProperInterval m` is the subtype of tuples `v ≤ m`, `v ≠ 0`, `v ≠ m`.
  The ambient function order is coordinatewise. The omitted lower bound `0 ≤ v`
  is automatic for natural coordinates, not an omitted mathematical assumption.
- `ChainBasis m n = Fin n ↪o ProperInterval m` consists exactly of increasing
  sequences of n distinct comparable vertices. Order reflection imposes no extra
  condition: a strictly increasing map from a finite linear order reflects order.
- `Chains m n = ChainBasis m n →₀ ℚ` is free on that basis. Thus the auxiliary
  natural index n corresponds to homological degree n - 1. At n = 0 there is one
  empty embedding even if the interval is empty, so this module is canonically
  ℚ, with generator `Finsupp.single` of the empty embedding and coefficient 1.
- `boundary m n` is `Finsupp.linearCombination ℚ` of the displayed finite sum.
  The a-th face is precomposition with `a.succAboveOrderEmb`, deleting vertex a,
  with coefficient `(-1 : ℚ) ^ a.val`. For n = 0 the sum has one term of sign +1,
  so every vertex maps to the empty-chain generator. For n >= 1 it is precisely
  the alternating deletion in the node.
- `boundary_squared` postpones only the proof of the explicitly given maps'
  square-zero identity. `complexNat` uses `ChainComplex.of` with that proof;
  no differential or other data is chosen from an existence assertion.
- `augmentedDegreeEmbedding.f n = (n : ℤ) - 1`. Its injectivity and shape
  compatibility are arithmetic structure proofs. `complex m` extends
  `complexNat m` along this embedding by Mathlib's zero-extension construction.
  Consequently its degree k >= 0 is free on k + 1 vertices, its degree -1 is
  the empty-chain copy of ℚ, and every degree below -1 and the differential
  out of degree -1 are zero. The canonical free module on a singleton realizes
  the specified augmentation copy of ℚ without an arbitrary identification.
- The first conjunct assumes `(∃ i : Fin r, 2 ≤ m i)` and concludes
  `∀ k : ℤ, IsZero ((complex m).homology k)`, exactly the nonsquarefree clause.
- The second conjunct assumes `∀ i, m i = 0 ∨ m i = 1`. The count s is
  `(Finset.univ.filter (fun i : Fin r ↦ m i = 1)).card`. It is cast to ℤ
  BEFORE subtracting 2. Vanishing is required at every integer k unequal to
  that integer s - 2, and `Module.finrank ℚ` at s - 2 equals 1. In particular
  no natural-number truncated subtraction is used.

The recorded statement dependency is used directly:
`Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`,
`HomologicalComplex.homology`; its signature and docstring were opened, along
with `ChainComplex` and `ChainComplex.of` in
`Mathlib.Algebra.Homology.HomologicalComplex`. Homology is the standard categorical
kernel modulo image, agreeing with the dependency's explicit module quotient
via `ShortComplex.moduleCatHomologyIso` (its source and docstring were also read).
`ModuleCat` has its Mathlib abelian instance, so all these homology objects exist.
The definition was not privately copied.

The available proof dependency is imported without `public`:
`Mathlib.Algebra.Homology.HomologySequence`, giving the recorded
`CategoryTheory.ShortComplex.ShortExact.homology_exact₂` and the adjacent
`homology_exact₁`, `homology_exact₃` and `δ` (their full signatures and docstrings
were opened). The other proof dependency,
`lem-sfb-poset-augmented-chain-prism`, has no Lean record or Mathlib match in the
read tree and is not needed to TYPE this statement; it is consequently not
imported. Its role in the eventual proof is spelled out by name in the theorem
docstring. This is not a missing statement dependency or an extra assumption.

Edge cases were checked directly on the displayed bases and differentials:

- m = (1) and m = (0,1): the interval is empty, only the empty-chain module
  remains, and the exceptional degree is (1 : ℤ) - 2 = -1.
- m = (2): the interval has one vertex; the sole nonzero boundary is the
  identity from its vertex copy of ℚ to the empty-chain copy, so it is acyclic.
- m = (1,1): there are two incomparable vertices. The augmentation is
  (x,y) ↦ x+y, with one-dimensional kernel in degree 0 = s - 2.
- Zero coordinates add no vertices or order relations; deleting them preserves
  all strict chains. The Boolean count ignores them as required.
- For a coordinate m_j >= 2, the max-with-one contraction stays below the
  excluded top: max(v_j,1) = m_j forces v_j = m_j. This uses exactly the stated
  threshold 2. All degrees below -1 vanish by the actual zero extension.
- The all-zero tuple and r = 0 are excluded by precisely the node's hypotheses.
  There is no new positivity, bound, dimension or finiteness hypothesis.

Searches for an existing statement/construction (all through the prescribed
msearch tool except the direct repository searches):

- LeanFinder: `Reduced rational homology of the proper part of a product of finite chains`.
  Eight hits: incidence-algebra Euler characteristic, Dold–Kan, group and singular
  homology. None describes the augmented strict-chain homology in this node.
- Loogle: `"OrderComplex"`. No hits.
- Mathlib grep: `augmentedChain|orderComplex|order complex|proper.*interval.*homolog`.
  Only an unrelated `ComplexOrder` hit in GramMatrix; no match.
- LeanSearch: `Reduced homology of the order complex of the proper part of a product of finite chains`.
  Eight hits: Euler characteristic of products, simplicial products and unrelated
  homology declarations. Euler characteristic does not determine these homology
  groups, and no exact statement matched.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for proper intervals,
  poset/augmented chains, `OrderComplex`, and the chosen namespace and helper
  names; and the item id in `lean/WeilConjectures`. The only relevant mention
  was the proof docstring in `RationalPolynomialBarContraction`, which USES this
  calculation and does not define or state it. No duplicate was found. The
  upstream names index also has no matching declaration.

The first server compile exposed the wrong order-embedding composition method
and a function equality needing explicit unfolding for arithmetic injectivity.
The deletion is now `a.succAboveOrderEmb.trans c`, and the embedding proof exposes
its integer formula. A subsequent prescribed scompile run compiled BOTH the
sandbox module and its final library module name with exit code 0 and no warnings.
Delivery preflight and final delivery follow this report through deliver2.py.

No STATEMENT-DISPUTED issue was found. The previous worker's unchanged-node failure
was a stage mismatch: Q21 had supplied the stage-1 split, but the node still lacked
a Lean record. This delivery supplies the actual stage-2 statement and changes
that record, retaining Q21's reviewed mathematical split.

## Second reading by Q12

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
