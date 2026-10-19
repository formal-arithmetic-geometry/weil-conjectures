## Worker report

Item: `lem-per-polynomial-conormal-completion` (Q119, stage 2).
Module: `Sheaf.RingTheory.PolynomialConormalCompletion`.
Declaration: `Algebra.polynomial_conormal_completion`.

The module states the complete conormal-and-differential comparison, with one named
sorry theorem and no definitions or auxiliary postponed theorems. The node is copied
unchanged except for `lean`. Its seven proof steps are included in the theorem docstring.
Source read: `literature/stacks-project/restricted.tex`, the full statement and proof
of `lemma-NL-is-completion` (Tag 0GAF), and `equation-NL` with its surrounding setup.
No statement correction, missing dependency, new node, or statement dispute was found.

Hypotheses and conclusions, in the order of the node:

| Natural-language clause | Lean rendering |
| --- | --- |
| A is a commutative Noetherian ring | `(A : Type u) [CommRing A] [IsNoetherianRing A]` |
| I is any ideal of A | `(I : Ideal A)`; no properness or Jacobson hypothesis |
| r is a nonnegative integer and S is its polynomial ring | `(r : ℕ)` and `MvPolynomial (Fin r) A` |
| B is a commutative A-algebra | `(B : Type v) [CommRing B] [Algebra A B]` |
| alpha is an A-algebra homomorphism and is surjective | `(α : MvPolynomial (Fin r) A →ₐ[A] B)` and `hα : Function.Surjective α` |
| K is the finitely generated kernel | `RingHom.ker α.toRingHom` and `_hK : (RingHom.ker α.toRingHom).FG` |
| P is lim S/I^n S | `AdicCompletion (I.map (algebraMap A (MvPolynomial (Fin r) A))) (MvPolynomial (Fin r) A)` |
| B-hat is lim B/I^n B | `AdicCompletion (I.map (algebraMap A B)) B` |
| alpha-hat is induced on compatible sequences | existential A-algebra map `αhat`, whose first conjunct identifies every n-th output coordinate from any polynomial lift of the n-th input coordinate |
| alpha-hat is surjective | `∃ hαhat : Function.Surjective αhat` |
| its kernel J is KP | `RingHom.ker αhat.toRingHom = (RingHom.ker α.toRingHom).map (algebraMap S P)` |
| conormal source and target | `(Extension.ofSurjective α hα).Cotangent` and `(Extension.ofSurjective αhat hαhat).Cotangent`, Mathlib's kernel modulo its square with the B and B-hat module actions |
| the canonical conormal map is an isomorphism | `e : (Bhat ⊗[B] conormal) ≃ₗ[Bhat] completedConormal`, with every pure tensor `b ⊗ [k]` sent to `b • [q]`, where `q.val` is the canonical image of `k.val` in P |
| differentiation descends coordinatewise | `D : Fin r → P →ₗ[A] P`, with the n-th coordinate of `D i p` equal to the class of `MvPolynomial.pderiv i f` for every lift f of the n-th coordinate of p |
| the derivatives are continuous | `∀ i, @Continuous ... (D i)` for the explicit inverse-limit topology `⨅ n, TopologicalSpace.induced (AdicCompletion.evalₐ ... n) ⊥` on both sides |
| d0 is well-defined and B-linear | `d₀ : conormal →ₗ[B] (Fin r → B)` with `d₀ (Extension.Cotangent.mk k) i = α (MvPolynomial.pderiv i k.val)` |
| d-hat is well-defined and B-hat-linear | `dhat : completedConormal →ₗ[Bhat] (Fin r → Bhat)` with `dhat (Extension.Cotangent.mk q) i = αhat (D i q.val)` |
| finite-free base-change identification | `t : (Bhat ⊗[B] (Fin r → B)) ≃ₗ[Bhat] (Fin r → Bhat)` with `t (b ⊗ w) i = b * algebraMap B Bhat (w i)` |
| differential equals the scalar extension of d0 | `∀ z, dhat (e z) = t (LinearMap.lTensor _ d₀ z)` |

`S`, `P`, `Bhat`, `conormal`, and `completedConormal` in the table abbreviate the
fully expanded terms in the actual theorem; there are no local abbreviations or lets.
The finite index type makes function modules `Fin r → B` the usual finite direct sums.
The finite-free identification is fixed by its coordinate formula, including r = 0.

The tensor factors are written in Mathlib's scalar-extension convention, with B-hat
on the left so that its standard `TensorProduct.leftModule` instance applies.
The node's right-factor map is exactly `e ∘ TensorProduct.comm B conormal Bhat`;
the right-factor finite-free comparison is similarly `t ∘ TensorProduct.comm`.
Their formulas are `[k] ⊗ b ↦ b[k]` and `w ⊗ b ↦ (b w_i)_i`.
Conjugating `LinearMap.lTensor Bhat d₀` by these canonical symmetries is
`LinearMap.rTensor Bhat d₀`. Thus the last equation is precisely the node's
right-factor equation with its canonical identification, and retains linearity
over B-hat. No alternative coefficient ring is substituted.

All maps in the conclusion are characterized on every coordinate or on module
generators. Existence is asserted by the theorem; it is not an assumption on an
arbitrary map. For any kernel element k, the coordinate condition implies that its
canonical completion image belongs to the completed kernel; hence a q in the
conormal formula exists. Quantifying over such q removes an in-statement proof
term while specifying exactly the canonical map. Proof irrelevance makes its choice
of membership proof immaterial. The n-th coordinate conditions also imply the
completed Leibniz rule, since polynomial differentiation has that rule.

Dependency declarations used (their source signatures and docstrings were read):

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` and `isNoetherianRing_iff_ideal_fg`.
- `def-weil-pbc-mv-polynomial-ring`: `Mathlib.Algebra.MvPolynomial.Basic`,
  `MvPolynomial` and `MvPolynomial.algHom_ext`; its evaluation universal property
  `MvPolynomial.aeval` was also read in `Mathlib.Algebra.MvPolynomial.Eval`.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion`; `Mathlib.RingTheory.AdicCompletion.Algebra`, the commutative
  ring and algebra instances and `AdicCompletion.evalₐ`. These are compatible
  sequences modulo powers of the extended ideal, exactly the node's completion.
- `def-weil-pbc-module-tensor-product` is a Mathlib leaf with no Lean record:
  its `mathlib_match` gives `TensorProduct`, `TensorProduct.tmul`,
  `TensorProduct.lift`, and `LinearMap.rTensor`. We use those notions and the
  symmetric left-factor scalar-extension convention from
  `Mathlib.LinearAlgebra.TensorProduct.Tower` and `LinearMap.lTensor`.
- `def-weil-pbc-polynomial-partial-derivative`: `Mathlib.Algebra.MvPolynomial.PDeriv`,
  `MvPolynomial.pderiv`, including its monomial and variable formulas.
- Proof-only import `Mathlib.RingTheory.FiniteType` supplies
  `Algebra.FiniteType.isNoetherianRing` for
  `lem-weil-pbc-finite-type-algebra-noetherian`.
- Proof-only import `Mathlib.RingTheory.AdicCompletion.Exactness` supplies
  `AdicCompletion.map_injective`, `map_exact`, and `map_surjective` for
  `lem-weil-pbc-completion-exact-finite-modules`.
- Proof-only import `Mathlib.RingTheory.AdicCompletion.AsTensorProduct` supplies
  `AdicCompletion.ofTensorProductEquivOfFiniteNoetherian`,
  `ofTensorProduct_tmul`, and `ofTensorProduct_naturality` for
  `lem-weil-pbc-completion-finite-module-tensor`.

The additional Mathlib interface `Algebra.Extension.ofSurjective`,
`Algebra.Extension.Cotangent`, and `Algebra.Extension.Cotangent.mk` in
`Mathlib.RingTheory.Extension.Basic` was read in full at its construction,
module-action and quotient-generator declarations. This reuses the existing
quotient-ring action on K/K² rather than declaring a second conormal construction.
`Mathlib.Topology.Order` supplies the lattice of topologies and induced topology.

Edge cases checked mathematically before finishing the statement:

- r = 0: `Fin 0` is empty, both free modules are zero, the derivative family is
  empty, and all the conormal and completion clauses remain present.
- I = 0: the completion recovers the original ring; derivatives and comparison
  specialize to the ordinary presentation and its conormal map.
- I = A: all completed rings are zero rings, and both tensor modules and completed
  conormal modules vanish. No `Nontrivial` or proper-ideal hypothesis excludes this.
- K = 0: both conormal modules are zero and the completed kernel remains zero.
- K = S, equivalently B is the zero ring: its completion and conormal are zero,
  while J = P; J/J² = 0, so the claimed equivalence remains correct.
- A may itself be the zero ring; no characteristic restriction appears.
- Universes u and v are independent, and all binders and universes are explicit.
  No topology on A, S or B is assumed; the displayed completion topology is exactly
  the subspace inverse-limit topology of discrete quotient rings.

Searches made for an existing full statement:

1. `msearch.py` LeanFinder: "Completing a polynomial presentation over a Noetherian
   ring preserves the conormal module and its partial derivative differential".
   Eight hits, chiefly `Algebra.PreSubmersivePresentation.cotangentComplexAux_apply`,
   `Algebra.SubmersivePresentation.aevalDifferentialEquiv_apply` and ordinary
   presentation differential results. They do not compare completion at an
   arbitrary base ideal and require presentation data absent here.
2. `msearch.py` Loogle: `AdicCompletion, Ideal.Cotangent`: zero hits.
3. `msearch.py` grep of Mathlib RingTheory:
   `completion.*[Cc]otangent|[Cc]otangent.*completion|AdicCompletion.*[Pp]resentation`.
   One hit in `AdicCompletion/LocalRing.lean`, `Ideal.mapCotangent` inside
   `spanFinrank_maximalIdeal_eq`. Its full surrounding lemma was read: it compares
   maximal-ideal cotangent dimensions of local rings, not the arbitrary presentation
   and base-ideal comparison in this item.
4. `msearch.py` LeanSearch: "Completing a polynomial presentation preserves the
   conormal module and the partial derivative differential". Eight hits including
   `MvPolynomial.pderiv`, `Algebra.PreSubmersivePresentation.differential`, and
   `KaehlerDifferential.mvPolynomialBasis_repr_apply`; no completion comparison.
5. `rg` of the upstream `WeilConjectures` tree for the node id and the combinations
   conormal/completion found no existing declaration of this item. Concept searches
   in upstream RingTheory and the side library's `lean/Sheaf/RingTheory` found
   `CompletionKaehlerDifferentialComparison`, ordinary symmetric conormal transport,
   and Koszul conormal comparisons. These state different comparisons, not this
   polynomial-presentation completion theorem. Mathlib's cotangent base-change
   file was also read; it concerns extension to `T ⊗[R] S` with a flatness assumption,
   rather than this entire completion-and-differential assertion.

Validation: `scompile.py Q119 lem-per-polynomial-conormal-completion` compiled this
module both as a sandbox file and under its library module name with no errors or
warnings. The initial elaboration found the need for a public topology-lattice
import and explicit completion source/target rings in the representative formula;
these were repaired without changing the mathematical statement. The required
final dry run and delivery are performed after the record and report are written.

## Second reading by Q119

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
