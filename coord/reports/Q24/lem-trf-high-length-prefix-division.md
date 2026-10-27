## Worker report

The module `Sheaf.RingTheory.HighLengthPrefixDivision` states
`AddMonoidAlgebra.positiveMonoid_high_length_prefix_division`, with `sorry` as its
only theorem proof. Three explicit helpers in the owning node's module construct
`positiveMonoid_prefixSum`, `positiveMonoid_prefixCell`, and
`positiveMonoid_prefixResidual`. They introduce precisely the displayed `s_I`,
`E_I`, and `c^I` of the item, not independent notions or additional assumptions.
All are listed in `lean.declarations`. No definition contains postponed data.
No node statement, dependency list, or proof was changed; no extra nodes or
dependency repairs are needed.

I read the complete item, the statement and Lean record of its sole statement
dependency `lem-trf-positive-monoid-convolution-length`, and that dependency's
complete Lean declaration and docstring. The recorded module is
`Sheaf.RingTheory.PositiveMonoidConvolutionLength`, declaration
`AddMonoidAlgebra.positiveMonoid_convolution_length`; it is publicly imported.
It is also the only proof dependency. Its interface supplies an existentially
characterized maximum length and convolution ring, rather than named definitions
of those objects. This statement therefore binds `ν` with its exact attained-maximum
characterization and binds a ring with the dependency's exact four operation formulas.
These characterize the objects uniquely and introduce no extra mathematical hypothesis.
They do not choose arbitrary data from an underdetermined existence statement.

I read ILO Exposé VI §1.6(i)–(ii), printed p. 70 (PDF p. 76), using `pdftotext`.
It gives the formal monoid models, not this auxiliary theorem, as the node's source
record correctly explains. I also read the current blueprint's
`sec-trace-formula/sk-i-curve-zero/_section.md` and `lem-trf-local-term-locality.md`
and its proof. The delivered module documents the auxiliary coefficient argument
and reproduces the seven proof steps, without claiming that ILO states the result.

Hypotheses, objects, and clauses correspond as follows:

- Finite-rank free abelian `G` is `(G : Type u) [AddCommGroup G]
  [Module.Free ℤ G] [Module.Finite ℤ G]`, exactly as in the dependency.
- The additive submonoid is `(P : AddSubmonoid G)`. Its finite list is
  `(s : ℕ) (g : Fin s → P)`; `hg` requires every generator to be nonzero and
  `hgen` says the closure of their ambient images equals `P`. Bundling each
  generator in `P` is equivalent to the dependency's ambient generators and
  generation equality. `Fin s` permits the empty list and repeated generators.
- The positive integral weight is `(wgt : G →+ ℤ)` with `hpos` requiring
  positivity on every nonzero `p : P`.
- `(A : Type v) [CommRing A]` has independent universe and no completeness,
  topology, Noetherianity, or nontriviality assumption. The coefficient families
  are exactly `P → A`.
- `[ring : CommRing (P → A)]` specifies the ring on these families. `hzero`,
  `hone`, `hadd`, and `hmul` are respectively zero-family, delta-at-zero unit,
  componentwise addition, and finite convolution (the same `∑ᶠ` on the fiber
  of pairs used by the dependency). The locally bound ring instance is used by
  all multiplication, sums, products and zero terms in the theorem, rather than
  the usual pointwise ring instance on functions.
- `(ν : P → ℕ)` and `hν` give `IsGreatest` of lengths of decompositions into
  nonzero summands; the empty sum is included by `Fin 0`. `hνzero : ν 0 = 0`
  states the normalization explicitly. `(n : ℕ) (hn : 1 ≤ n)` fixes the positive
  cutoff. `H_n` is always written `{p : P | n ≤ ν p}`.
- `T` is `Fin n → Fin s`, with its standard finite-type instance, and
  `[LinearOrder (Fin n → Fin s)]` permits any fixed total order. There is no
  assumption that this order is related to exponents or weights.
- `positiveMonoid_prefixSum g I` is literally `∑ j, g (I j)` in `P`.
- The first conclusion says every high-length `p` equals a prefix sum plus
  some `q : P`, with an actual tuple `I : T`.
- `positiveMonoid_prefixCell ν g n I` contains exactly high-length `p` for which
  the difference `(p : G) - (positiveMonoid_prefixSum g I : G)` belongs to `P`
  and `I ≤ J` for every eligible `J`. Subtraction really occurs in `G`.
- The second conclusion gives `Disjoint` for all distinct tuples; the third is
  the indexed-union equality with `H_n`. Neither coverage nor either partition
  clause has been omitted.
- The high-length tail is the explicit function
  `fun p ↦ if n ≤ ν p then a p else 0`.
- `positiveMonoid_prefixResidual ν g n a I` is the function on *all* `q : P`
  with value `a (positiveMonoid_prefixSum g I + q)` when that exponent is in
  the cell, and zero otherwise. Its only noncomputability is classical decision
  of cell membership; it is not a finite-support family or a chosen witness.
- The fourth conclusion identifies every coefficient of
  `Pi.single (positiveMonoid_prefixSum g I) 1 * positiveMonoid_prefixResidual …`
  with `a p` on `E_I` and zero off it. `Pi.single p 1` is exactly the node's `z^p`.
- The fifth conclusion is equality of coefficient functions between the tail
  and `∑ I : Fin n → Fin s, z^(s_I) * c^I`. This is a finite sum in the specified
  convolution ring, with no support or convergence restriction on its terms.
- The sixth conclusion is `z^(s_I) = ∏ j : Fin n, z^(g (I j))`, multiplication
  in that same ring.
- The last conclusion treats `s = 0`: `P = ⊥`, the high-length set is empty,
  `IsEmpty (Fin n → Fin s)`, and, for every `a`, both the tail and its finite
  sum equal the ring zero. This states the empty-sum identity explicitly.

Edge cases checked before writing: an empty generator list with positive `n`
gives `P = {0}` and no tuples, and is covered by the last conclusion; `G = 0`
forces that situation. `n = 1` gives singleton generator prefixes. If no
exponent has length at least `n`, all cells and residuals are zero and the tail
identity still holds. Zero is outside `H_n` since `ν 0 = 0`. Repeated generators
or relations among generators cause several eligible tuples, resolved uniquely
by the fixed total order, without requiring freeness of `P` or uniqueness of
generator expressions. For example, in the submonoid of `ℤ` generated by 2 and
3, exponent 6 admits lengths 3 and 2: the maximum-length definition and the
least-eligible partition do not confuse these decompositions. The zero coefficient
ring and arbitrary infinite coefficient support are permitted. No case `n = 0`
is claimed, consistently with the node.

Searches performed with `msearch.py` (Q24, this item):

- LeanFinder: "Partition a formal series on a finitely generated positive monoid
  by the least eligible generator tuple and express its high length tail as a
  finite sum of monomial shifts". Eight hits, including `Nat.Partition.genFun`,
  `MvPowerSeries.inv.aux`, partition generating-function identities and
  `FormalMultilinearSeries.compAlongOrderedFinpartition`. None gives this statement.
- Loogle: `MvPowerSeries, "idealOfVars"`. Two hits:
  `MvPowerSeries.truncTotal_sub_truncTotal_mem_pow_idealOfVars` and
  `MvPowerSeries.truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars`.
  They concern polynomial truncation on free exponent monoids, not the partition
  and arbitrary residual families here.
- Mathlib grep: `sum.*monomial|monomial.*sum|divMonomial` restricted to
  `RingTheory/MvPowerSeries`. Fourteen hits in Trunc, PiTopology, Evaluation,
  Order and Basic. They are coefficient formulas or infinite topological sums
  on free exponent monoids, not this finite-prefix division statement.
- LeanSearch: "Finite partition of high length monoid coefficients by least
  eligible generator tuple gives a finite sum of monomial shifted arbitrary
  coefficient functions". Eight hits, including `Finset.sum_partition`,
  `MvPolynomial.coeff_sum`, `OrderedFinpartition.sum_sigma_eq_sum`, polynomial
  coefficient maps and partition generating functions. No exact match.

Local `rg` searches in both `lean/Sheaf` and `lean/WeilConjectures` for
`positiveMonoid|PositiveMonoid|prefixDivision|prefix_division|highLength|high_length|convolutionLength`
found the dependency and an unrelated chart instance. Searching
`prefix.*(division|monoid)|first.*eligible|high.length|prefix_division|highLength`
found only the higher-level FinitePatternFactorization and MonoidCompletionCoefficients
proof plans and unrelated coefficient projection modules, not this statement.
The exact node-id search in `lean/WeilConjectures` returned no match. A full
Mathlib/project search for each proposed helper name and theorem name returned
no pre-existing declaration.

No statement dispute or node fault was found. Compilation and delivery validation
are recorded below after the prescribed server checks.

Validation: `scompile.py` compiled the complete file both as the isolated sandbox
module and as `Sheaf.RingTheory.HighLengthPrefixDivision`, with no errors or
unexpected warnings (15.0 s and 9.6 s). The initial elaboration failure was repaired
by explicitly typing the monomial families as `P → A`; this changes no mathematical
content. The longest Lean source line is 90 characters. All variables and the two
universes are explicitly bound. The node's `lean.statement` is the complete verbatim
theorem signature from the final file.

## Second reading by Q24

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
