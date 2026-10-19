## Worker report

The module `Sheaf.RingTheory.NormalizationCompletedBranchLift` states
`RingTheory.normalizationCompletedBranchLift`, with `sorry` as its whole proof.
It defines no new notion and changes only the item's `lean` record. The previous
N4 delivery was the stage-1 split, not a stage-2 statement: the current node has
no `lean` binding. Thus the earlier unchanged-node refusal is repaired by supplying
the missing statement and binding, rather than resubmitting the stage-1 node.

Read the current node, its ten proof steps, its three statement dependencies and
all their records. Read the recorded Mathlib signatures and docstrings for
`IsNoetherianRing`, `integralClosure`, `IsIntegral`, `AdicCompletion`, and the
canonical completion maps. Read `FractionRing`, `minimalPrimes`, and
`IsLocalRing.maximalIdeal` at their definitions as well. Read Swanson–Huneke's
Lemma 4.8.3 (printed p. 84, PDF page 98) and Corollary 2.1.13 (printed p. 27)
in the author-hosted text:
https://www.math.purdue.edu/~iswanso/book/SwansonHuneke.pdf . The first lifts the
specified closed normalization point to normalization of the reduced completion;
the second decomposes that normalization into branch factors. The node states
this component form with its canonical maps. The Lean statement retains that form.
The complete ten-step DAG proof, including all its dependency names, is carried
in the theorem docstring for stage 3.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Commutative Noetherian local domain A | `(A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsDomain A]` |
| Unique maximal ideal m | `IsLocalRing.maximalIdeal A`; Mathlib's local-ring condition is equivalent to having a unique maximal ideal for this nontrivial commutative ring |
| Domain means 1 ≠ 0 and no zero divisors | `IsDomain A`, which supplies both nontriviality and no zero divisors |
| K = Frac(A) | Canonical `FractionRing A`, localization at `nonZeroDivisors A` |
| B is the integral closure of A in K | `integralClosure A (FractionRing A)` throughout; B is an abbreviation in the node, not extra independent input data |
| q is a prime of B | `(q : Ideal (integralClosure A (FractionRing A))) [q.IsPrime]` |
| q contracts to m | `hqA : q.comap (algebraMap A (integralClosure A (FractionRing A))) = IsLocalRing.maximalIdeal A` |
| H is the m-adic completion with canonical iota | `AdicCompletion (IsLocalRing.maximalIdeal A) A` and `AdicCompletion.of (IsLocalRing.maximalIdeal A) A` |
| n is kernel of the first projection H → A/m | `RingHom.ker (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal A)).toRingHom` |
| A minimal prime p of H exists | `∃ p : Ideal H, p ∈ minimalPrimes H ∧ ...`, with H expanded in the signature |
| H/p is the domain component | `H ⧸ p`; membership in `minimalPrimes H` includes primality, hence this quotient is a domain |
| T is its normalization in its own fraction field | Explicit `integralClosure (H ⧸ p) (FractionRing (H ⧸ p))` everywhere, with H expanded |
| An A-algebra homomorphism j from B to T exists | `∃ (j : B →+* T) ...`, together with the final equality for every `a : A` |
| A prime ideal M of T exists | `(M : Ideal T)` and `M.IsPrime` |
| j inverse image of M is q | `Ideal.comap j M = q` |
| M contracts to n/p in H/p | `Ideal.comap (algebraMap (H ⧸ p) T) M = Ideal.map (Ideal.Quotient.mk p) n` |
| j restricts to A → H → H/p → T | Final `∀ a : A, j (algebraMap A B a) = algebraMap (H ⧸ p) T (Ideal.Quotient.mk p (AdicCompletion.of (IsLocalRing.maximalIdeal A) A a))` |
| Minimal means minimal among all prime ideals | `minimalPrimes H` is precisely `Minimal Ideal.IsPrime`, via its definition and `IsMinimalPrime.iff_minimal` |
| Fraction denominators are nonzero | `FractionRing` localizes at `nonZeroDivisors`; in the two domain cases this is exactly the nonzero elements |

The `j` compatibility clause spells out exactly what the node calls an A-algebra
homomorphism. No independently supplied algebra structure on T or arbitrary
comparison map replaces the quotient-and-inclusion construction. Mathlib defines
`FractionRing R` for every commutative ring; its use before the prime witness is
extracted requires no quotient-domain instance binder. The asserted minimality
already implies that this concrete localization is the fraction field of H/p.
The completion includes the n=0 component, which is the unique element of A/A;
removing it gives exactly the positive-index inverse limit in the node.

Statement dependencies used, without private copies:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (every ideal is finitely generated).
- `def-weil-pbc-integral-closure`:
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, `integralClosure`,
  with carrier given by `IsIntegral`.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion`; `Mathlib.RingTheory.AdicCompletion.Algebra` supplies the
  canonical ring/algebra structure, `AdicCompletion.of`, and `AdicCompletion.evalOneₐ`.

All recorded proof dependencies are imported: faithfully flat and flat-module
facts, completion locality and Noetherianity, finite/minimal-prime facts, module
localization, tensor universal property, radical/prime spectrum, integral lying
over, and prime factors of finite products. The recorded
`WeilConjectures.RingTheory.AdicCompletionNoetherian` source was absent from the
old local checkouts, so its current source was read with `scompile.py --source`;
it gives precisely `AdicCompletion.isNoetherianRing`. Its published module is
used directly. No dependency interface repair was needed.

Edge cases checked: if A is a field, m=q=p=M=0 and both normalization rings are A.
For a complete normal local domain the identity branch supplies the result.
The zero ring is excluded exactly by the node's domain hypothesis. Analytically
reducible domains are permitted: p is existentially selected, not fixed in
advance. Nilpotents in the completion are permitted; no reducedness, excellence,
dimension-one, finite-normalization or residue-field assumption is imposed.
The arbitrary universe u covers every ring in the node; the canonical completion,
quotients, localizations and subalgebras stay in u, with no unrelated field or
index universe. There is no empty branch-list input or hidden nonemptiness
assumption in the statement.

Searches made with `msearch.py` under this group and item (raw results retained
in sandbox `searches.jsonl`):

- LeanFinder query: "A prime of the integral closure of a Noetherian local domain
  over the maximal ideal lifts to the normalization of a minimal-prime branch of
  its completion". Eight hits: `IsLocalization.AtPrime.mem_primesOver_of_isPrime`,
  `IsDedekindDomain.primesOverEquivPrimesOver`,
  `IsLocalization.OverPrime.mem_normalizedFactors_of_isPrime`,
  `IsDedekindDomain.primesOverEquivPrimesOver_apply`, `IsLocalRing.primesOver_eq`,
  `primesOver_ncard_ne_zero`, `IsLocalRing.primesOverFinset_eq`, and
  `Ideal.nonempty_primesOver`. These concern localization, Dedekind domains or
  generic lying over, not completion-branch normalization lifting.
- Loogle query: `"AdicCompletion", "integralClosure"`. Zero hits.
- Mathlib grep query: `integralClosure|normalization`, subdirectory
  `RingTheory/AdicCompletion`. Zero hits.
- `rg` in the slopmaster2 `WeilConjectures` tree and project `lean/Sheaf`, for
  the exact item id, `normalizationCompletedBranchLift`, and `completed.branch`:
  no matching statement. Broader normalization/completion/integralClosure
  searches located `CurveNormalizationCompletion`, which assumes a local
  algebraic curve, and analytically-unramified N-1 results, which require reduced
  completion. Neither gives this general Noetherian-domain lift. The declared
  theorem name has no existing declaration in either source tree.

No statement correction, new node, dependency module or statement dispute is
needed. One theorem is postponed by `sorry`; there are no data definitions or
extra theorem declarations. The natural-language statement and its dependencies
are unchanged. Compilation with every proof-dependency import completed with exit code 0 and no
warnings, both in the sandbox and at its library module path, through `scompile.py`.
The wrapper separately validates each file under the prescribed compiler limit.

## Second reading by NR

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
