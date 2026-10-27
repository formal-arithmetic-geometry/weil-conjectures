## Worker report

The module `Sheaf.RingTheory.AdicRelationMatrixInitialIdeals` states
`Ideal.exists_adic_relation_matrix_initial_ideals`, with its proof `sorry`.
There are no new definitions or helper theorems. The node changes only in
`lean`; its reviewed stage-1 statement, dependencies, and proof are preserved.
The inherited BLOCKED report concerned stage-1 unchanged-item validation,
not an obstruction to this stage-2 assignment. There is no released repair
note for this item. The sandbox initially contained only dispatcher markers;
there was no interrupted delivery to repeat.

Source read: `literature/stacks-project/more-algebra.tex`, lines 175–295,
Tags 07VE (`lemma-approximate-complex`) and 07VF
(`lemma-approximate-complex-graded`), including both proofs. The conclusion is
the common-subquotient equality displayed in 07VF's proof, specialized to
finite free modules and the maximal ideal. No statement correction is needed.

The hypothesis and clause correspondence is as follows.

- A commutative Noetherian local ring is `{P : Type u} [CommRing P]
  [IsNoetherianRing P] [IsLocalRing P]`. The arbitrary explicit universe `u`
  includes all ring sizes. The specified maximal ideal is `(q : Ideal P)
  [q.IsMaximal]`. `IsLocalRing.maximal_ideal_unique` and
  `IsLocalRing.eq_maximalIdeal` show that this is exactly the unique maximal
  ideal in the node, without restricting which local ring or ideal is allowed.
- The nonnegative ranks are `{r t : ℕ}`, with no positivity assumptions.
  A row is `(b : Fin r → P)`, acting by `dotProduct b`; a relation matrix is
  `(K : Matrix (Fin r) (Fin t) P)`, acting by `Matrix.mulVec K`.
  These operations are the actual finite sums of coefficient products.
- The equality `im K = ker b` is
  `h_exact : Function.Exact (Matrix.mulVec K) (dotProduct b)`.
  The definition says, for every vector `y`, that `dotProduct b y = 0`
  if and only if `y` lies in the range of the matrix action. Thus it asserts
  both inclusions, and entails the original complex condition.
- The uniform positive integer threshold is `∃ h : ℕ, 1 ≤ h ∧ ...`.
  It is chosen before both perturbed arrays, which have exactly the same
  `Fin r` and `Fin t` indices as the original ones.
- The row coefficient condition is
  `∀ i : Fin r, b i - b' i ∈ q ^ h`; the matrix coefficient condition is
  `∀ (i : Fin r) (j : Fin t), K i j - K' i j ∈ q ^ h`.
  Subtraction has the same orientation as in the node.
- The perturbed complex condition is `Matrix.vecMul b' K' = 0`.
  Its coordinate `j` is precisely `∑ i, b' i * K' i j = 0`.
  No exactness or surjectivity is imposed on the perturbed matrices.
- The two generated ideals are `Ideal.span (Set.range b)` and
  `Ideal.span (Set.range b')`. The conclusion quantifies over every
  `d : ℕ` and equates
  `q ^ (d + 1) + (Ideal.span (Set.range b) ⊓ q ^ d)` with the analogous
  expression for `b'`. Ideal infimum is intersection; ideal addition is
  the ideal sum (`Ideal.add_eq_sup`), and powers are Mathlib's ideal products.
  In particular `q ^ 0 = 1 = ⊤` gives the node's degree-zero convention.

Dependency interfaces read and used:

- `def-weil-pbc-noetherian-ring`: the recorded Mathlib declaration
  `IsNoetherianRing`, `Mathlib.RingTheory.Noetherian.Defs`, lines 193–206.
  Its docstring and definition identify it with finite generation of all
  ideals. This is publicly imported and used as an instance hypothesis.
- Proof dependency `lem-weil-pbc-artin-rees`: the Mathlib match
  `Ideal.exists_pow_inf_eq_pow_smul` in `Mathlib.RingTheory.Filtration`,
  lines 388–391. Its full signature and docstring were read; this module
  is imported non-publicly as required for the future proof.
- Proof dependency `lem-sfb-perturbed-image-artin-rees-bound`: the live node
  is unsplit and has neither a `lean` record nor a `mathlib_match`.
  It supplies no recorded module to import. The four-step proof docstring
  names it at its exact use. It is a proof dependency only, so its absence
  does not require an additional statement dependency or a replacement
  definition in this delivery.

Other Mathlib interfaces inspected in full at the relevant definitions:
`Function.Exact` in `Mathlib.Algebra.Exact.Basic` (generated additively from
`Function.MulExact`, lines 44–48); `dotProduct`, `Matrix.mulVec`, and
`Matrix.vecMul` in `Mathlib.Data.Matrix.Mul` (lines 69–73, 691–700,
710–719); `IsLocalRing` in `Mathlib.RingTheory.LocalRing.Defs` (lines 27–35);
the maximal ideal and uniqueness declarations in
`Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs` and `.Basic` (lines 29–32
and 44–57); ideal addition in `Mathlib.RingTheory.Ideal.Operations`.
No custom encoding of these notions is introduced.

Edge cases checked before writing: `r = 0` makes both generated ideals zero
and all row and matrix congruences vacuous; the conclusion is equality of
`q^(d+1)` with itself. `t = 0` makes the image of `K` zero and the original
row injective, exactly as original exactness requires; the perturbed complex
condition is then vacuous. Degree `d = 0` is included. For a field, `q = 0`
and `h ≥ 1` force the perturbed coefficients to equal the originals.
The zero ring has no maximal ideal and is correctly excluded by both the
informal hypotheses and `IsLocalRing`. No separatedness, completeness,
residue characteristic, nonzero coefficient, or positive-rank assumption
was added. For `b = 0` and a surjective `K`, the original exactness is
meaningful and the perturbed complex condition remains essential.

Searches actually run with the prescribed `msearch.py` wrapper:

- LeanSearch: "Initial ideals of nearby generators and syzygy matrices in a
  Noetherian local ring agree degree by degree". Eight hits, including
  `HomogeneousIdeal.ext'`, `Ideal.degreeLE`, `Ideal.leadingCoeff`, and
  finite-generation facts. None asserts stability under perturbation.
- LeanFinder: "In a Noetherian local ring sufficiently close generators and
  syzygy matrices defining a complex have equal initial ideals in every
  degree". Eight hits, including `AdicCompletion.map_exact`,
  `Ideal.exists_pow_inf_eq_pow_smul`, `Ideal.adic_basis`, and local-cohomology
  results. None states stability under simultaneous perturbation.
- Loogle: `"dotProduct", "toLin"`. Zero hits; no exact existing statement.
- Mathlib grep: `initialIdeal|initial_ideal|approximateComplex|approximate_complex|perturb`
  under `RingTheory`. Zero hits.
- Local project `rg` over `lean/WeilConjectures` and `lean/Sheaf` for adic
  relations, initial ideals, approximate complexes and perturbations found
  other power-perturbation, initial-form approximation, and toric lemmas,
  and the consumer `ArtinObjectGradedApproximation`; none states this node.
  Searching the exact node id in `lean/WeilConjectures` and the upstream
  declaration index found no declaration. A further exact-name search over
  Mathlib, both project libraries, and the upstream index found no collision.

The module docstring identifies both source tags. The theorem docstring
carries the accepted four-step proof, including the two Artin-Rees bounds,
the perturbation lemma, and both inclusions separately in low and high
degrees. All variables and the universe are explicitly bound, with
`autoImplicit false`. There are no local definitions, notation, or instances.
No statement fault or disputed assertion was found.

Validation: the prescribed `scompile.py` compiled the file on the server
both as a sandbox module (6.7 seconds) and with its actual library module
name (3.9 seconds), with no errors or non-sorry warnings.

## Second reading by NP

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
