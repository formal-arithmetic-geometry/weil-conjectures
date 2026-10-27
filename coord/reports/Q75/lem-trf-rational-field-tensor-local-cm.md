## Worker report

Item: `lem-trf-rational-field-tensor-local-cm`. The new module is
`Sheaf.RingTheory.RationalFieldTensorLocalCohenMacaulay`; its sole declaration is
`Algebra.TensorProduct.rationalField_localization_and_local_depth_eq_dimension`.
This stage-2 delivery states the theorem with `sorry`; it introduces no definitions,
new nodes, dependency repairs, or statement corrections. Only the item's `lean`
field changes. The theorem docstring contains all six steps of the accepted proof.

Source read: `literature/stacks-project/algebra.tex`, Tag 045M,
`lemma-tensor-fields-CM`, lines 47267–47294, particularly its final two proof
sentences identifying the purely transcendental tensor base as a polynomial
localization and invoking polynomial Cohen–Macaulayness. The item's statement is
an expanded formulation of that input, rather than the full field-tensor lemma.

Hypotheses and clauses, in order:

- A field k: `(k : Type u) [Field k]`.
- The extensions F/k and L/k: `(F : Type v) (L : Type w) [Field F] [Field L]`
  and `[Algebra k F] [Algebra k L]`. The three universe parameters are independent.
- The finite number r of generators, allowing zero: `(r : ℕ)`.
- The elements t_1,...,t_r in F: `(t : Fin r → F)`.
- Algebraic independence, defined in the node as injectivity of polynomial
  evaluation: `hind : Function.Injective (MvPolynomial.aeval t :
  MvPolynomial (Fin r) k →ₐ[k] F)`. No replacement by a different independence
  predicate is needed.
- F being the smallest subfield containing k and the t_i:
  `hgen : IntermediateField.adjoin k (Set.range t) = ⊤`. Mathlib's `adjoin`
  is constructed by `Subfield.closure (Set.range (algebraMap k F) ∪ Set.range t)`.
- P is exactly `MvPolynomial (Fin r) L`.
- W is the coefficient image of all nonzero k-polynomials:
  `(nonZeroDivisors (MvPolynomial (Fin r) k)).map
  (MvPolynomial.map (algebraMap k L))`. Since a polynomial ring over a field is
  an integral domain, its non-zero-divisors are exactly its nonzero elements.
  Thus this is precisely W, not a larger multiplicative set.
- A is the actual algebra tensor product `F ⊗[k] L`, with Mathlib's commutative
  ring multiplication, not a newly supplied algebra or multiplication.
- The L-algebra isomorphism is the existential `e : @AlgEquiv L ...` from
  `Localization W` to `F ⊗[k] L`. The last explicit argument is Mathlib's
  `Algebra.TensorProduct.rightAlgebra (R := k) (A := F) (B := L)`, whose
  structure map is l ↦ 1 tensor l. The other algebra structure is the canonical
  one on the polynomial localization. An explicit argument avoids file-local
  instance changes and makes the statement usable on import.
- The fraction formula is the universal quantification over
  `(α : Fin r →₀ ℕ) (l : L) (s : nonZeroDivisors (MvPolynomial (Fin r) k))`.
  The fraction is `Localization.mk (MvPolynomial.monomial α l)` with denominator
  `MvPolynomial.map (algebraMap k L) s`. Its membership proof is the explicit
  image witness `⟨s, s.property, rfl⟩`. The value is
  `((∏ i : Fin r, t i ^ α i) / MvPolynomial.aeval t (s : MvPolynomial (Fin r) k))
  ⊗ₜ[k] l`. Thus the numerator, evaluated denominator, and order of tensor
  factors agree with the node. Every w in W has such an s by definition.
- A is Noetherian: `IsNoetherianRing (F ⊗[k] L)`.
- Every prime p of A: `∀ (p : Ideal (F ⊗[k] L)) [p.IsPrime]`.
- Its ring is exactly `Localization.AtPrime p`, asserted to satisfy both
  `IsNoetherianRing` and `IsLocalRing`.
- Its depth equals its Krull dimension:
  `(IsLocalRing.depth (R := Localization.AtPrime p) (Localization.AtPrime p)
  : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime p)`.
  Depth is naturally in ℕ∞ and dimension in WithBot ℕ∞, so the displayed coercion
  compares them without discarding infinity. The self-module is finite by the
  canonical self-module instance; no Noetherianity hypothesis is smuggled into
  the theorem's binders.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, line 180; the
  commutative ring and division-ring structure with nontriviality.
- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, line 95,
  with `algebraMap`; specialize to the supplied fields, exactly as its record says.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`,
  `Mathlib.Algebra.MvPolynomial.Basic`, line 82; `MvPolynomial.algHom_ext`,
  line 436; `MvPolynomial.aeval`, `Mathlib.Algebra.MvPolynomial.Eval`, line 593,
  with `aeval_X` and `aeval_C` immediately below. The polynomial and evaluation
  constructions in the statement are these recorded declarations.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, line 81, the actual quotient by
  bilinearity. Algebra multiplication and the canonical right-factor algebra
  come from `Mathlib.RingTheory.TensorProduct.Basic`, particularly `rightAlgebra`
  at line 492. This equips the same tensor type with the requested multiplication.
- `def-weil-pbc-module-localization`: `LocalizedModule`,
  `Mathlib.Algebra.Module.LocalizedModule.Basic`, line 89, and its fraction
  constructor and relation at lines 99–104. For the self-module its underlying
  quotient is definitionally `Localization W` (the source explicitly checks this
  at lines 92–95). The ring localization has the required multiplication; there
  is no private copy of module localization.
- `def-weil-pbc-noetherian-ring`: `IsNoetherianRing`,
  `Mathlib.RingTheory.Noetherian.Defs`, line 196, with the ideal-finiteness
  characterization immediately below.
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, line 57, defined as the
  localization at `p.primeCompl` and equipped with the canonical local structure.
- `def-weil-pbc-depth`: `Ideal.depth` and `IsLocalRing.depth`,
  `WeilConjectures.RingTheory.Depth`, full definitions read. The latter is depth
  with respect to the maximal ideal, using the supremum of regular-sequence
  lengths and infinity when IM=M. No retired Sheaf twin is imported.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim`,
  `Mathlib.RingTheory.KrullDimension.Basic`, line 30, the order Krull dimension
  of `PrimeSpectrum` with values in `WithBot ℕ∞`.

Proof dependencies are imported without `public`: the recorded module
`Sheaf.RingTheory.PolynomialAlgebraCohenMacaulay` and its theorem
`MvPolynomial.isNoetherianRing_and_local_depth_eq_dimension` (full signature
and docstring read); `Mathlib.RingTheory.Localization.Submodule` for
`IsLocalization.isNoetherianRing`; `Mathlib.RingTheory.Localization.BaseChange`
for `IsLocalizedModule.rTensor` and `IsLocalizedModule.map_lTensor`; and
`Mathlib.RingTheory.Regular.RegularSequence` for `RingTheory.Sequence.IsRegular`.
Their full signatures and relevant source docstrings were read. The already
publicly imported definition dependencies supply the other proof-dependency
notions. The explicit regular-sequence proof import records its role in the
field base case, though the depth module already exposes its definition.

Edge cases checked before writing:

- r=0: `Fin 0` is empty, the monomial product is 1, and `adjoin k ∅ = ⊤`
  says that F is just the base field up to its given embedding. The localization
  of L at nonzero constants is L. The formula and depth-dimension zero agree.
- r=1 and L=k: W consists of all nonzero polynomials and the tensor is the
  rational function field; the same formula specializes to ordinary fractions.
- L=F: the tensor need not be a field. W inverts only the base-coefficient
  polynomials, so the conclusion does not incorrectly invert all L-polynomials
  or assert that A is a field.
- α=0 and l=0 give constants and zero respectively; s=1 gives the expected
  polynomial monomial. The denominator cannot be zero, by independence and
  the nonzero-divisor condition over the domain k[x].
- No characteristic restriction, separability, finiteness of L/k, or common
  universe is imposed. Zero rings are correctly excluded by the field binders;
  the prime-local statement does not quantify over a nonprime ideal.

Searches actually run for this item using the prescribed `msearch.py`:

- `leanfinder`: "A rational function field tensored with a field extension is a
  localization of a polynomial ring and its local rings have depth equal to
  dimension". Eight hits, including `FunctionField`,
  `RatFunc.rank_ratFunc_ratFunc`, `RatFunc.finrank_ratFunc_ratFunc`, and
  function-field integer-ring statements. None asserts this localization
  isomorphism with its formula and local-depth conclusions.
- `loogle`: "IsLocalization, TensorProduct". Twelve hits, including
  `IsLocalization.tensorRight`, `tensor`, `algebraTensorEquiv`, `mk'_tmul`,
  `tmul_mk'`, and `tensorProduct_tensorProduct`. These provide the localization
  ingredients but do not assert the finite purely transcendental specialization
  together with the local depth-dimension equality.
- `grep`: "CohenMacaulay|cohen.macaulay|rational.*tensor|tensor.*rational",
  subdirectory `RingTheory`. Zero hits.
- `leansearch`: "A rational function field tensored with a field extension is a
  localization of a polynomial ring and is Cohen Macaulay". Eight hits,
  including `RatFunc.instIsFractionRingPolynomial`,
  `IsLocalization.tensorProduct_isLocalizedModule`, `IsLocalization.tensor`,
  and `MvPolynomial.isLocalization`. The latter localizes polynomial
  coefficients, and the others cover fractions or localization/tensor
  ingredients. There is no complete match.
- Local `rg` in `lean/WeilConjectures` and `lean/Sheaf` for rational-tensor terms,
  the item id, and `local_depth_eq_dimension`. Relevant ring-theory results are
  the polynomial-algebra dependency and its consumers; unrelated rational
  sheaf-tensor results do not match. The chosen full declaration name is absent
  from both source trees and `dag/lean_names_upstream.json`.

No `STATEMENT-DISPUTED` issue or node fault was found.

Validation: the prescribed `scompile.py Q75 lem-trf-rational-field-tensor-local-cm`
compiled the module in both sandbox and library contexts successfully (2.5 s and
1.4 s respectively). No errors or unexpected warnings were printed. Final
wrapper preflight and per-file compilation are recorded by the delivery tool.

## Second reading by Q75

I reread the node, the source proof and the finished signature in a separate pass.
The two field extensions remain arbitrary and have independent universes;
`hind` is exactly the injectivity stipulated in the node, and `hgen` expresses
field generation, rather than algebra generation or finite-dimensionality.
`nonZeroDivisors k[x]` is exactly k[x] minus zero because k is a field. Taking
its coefficient image therefore gives precisely W. The explicit `rightAlgebra`
argument is essential: the target's L-algebra map sends l to 1 tensor l, so the
isomorphism uses the right tensor factor for scalars as required. Every
monomial fraction and all its coefficients are covered by the three universal
binders in the formula. The denominator subtype's image witness is actual data,
not an assumed membership assertion.

I also checked that the final conjunct states all three local-ring properties,
and compares depth and dimension using the same coercion as the recorded
polynomial-algebra theorem. No extra hypothesis is needed to form the depth
of a ring over itself. The r=0 case survives both the generation hypothesis and
the empty product convention. No signature mismatch was found. I expanded the
proof docstring to make fraction inverses, cross multiplication, multiplicativity
and the allowed prime-local denominators explicit; the statement did not change.
This is the worker's own second pass; the maintainer supplies the independent
review specified in the dispatcher brief.
