## Worker report

The module `Sheaf.RingTheory.RegularQuotientParameterApproximation` states
`IsRegularLocalRing.quotient_of_parameter_approximation`, with its entire proof `sorry`.
No new notion, helper declaration, dependency repair, or statement correction is needed.
The statement was checked directly against Milne, Algebraic Groups (2017), 13.2 and
Lemma 13.3, printed pp.254–255 (PDF pages 266–267), using pdftotext.

Clause-by-clause correspondence:

- The commutative regular local ring is `(A : Type u) [CommRing A]
  [IsRegularLocalRing A]`. Mathlib's regular-local class includes Noetherianity,
  localness and nontriviality, so no such assumption is lost or separately added.
- The residue field κ is `IsLocalRing.ResidueField A`, definitionally the quotient
  by `IsLocalRing.maximalIdeal A`. The cotangent vector space is
  `IsLocalRing.CotangentSpace A`, the maximal ideal modulo its square, with Mathlib's
  canonical residue-field module structure. Its finite dimensionality follows from
  the Noetherian instance inherited from regularity.
- The integer d is `(d : ℕ)` with
  `hd : d = Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A)`.
  This is the stated value of d, rather than a new restriction on A.
- The ideal and its containment are `(J : Ideal A)` and
  `hJ : J ≤ IsLocalRing.maximalIdeal A`.
- The integer range `0 ≤ s ≤ d` is `(s : ℕ) (hs : s ≤ d)`; the lower bound is built
  into the natural-number type.
- Every integer n ≥ 1 is `∀ n : ℕ, 1 ≤ n → ...`. Inside that quantifier,
  `∃ (v : Fin d → IsLocalRing.maximalIdeal A)` supplies all d lifts, with membership
  in the maximal ideal encoded by their subtype.
- Their classes form a κ-basis precisely by the existential
  `b : Module.Basis (Fin d) (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A)`
  and `∀ i : Fin d, b i = (IsLocalRing.maximalIdeal A).toCotangent (v i)`.
  No basis is assumed outside the existential for each n.
- The congruence of ideals is equality of their suprema with
  `IsLocalRing.maximalIdeal A ^ (n + 1)`. Ideal supremum is ideal sum.
  The first s lifts generate
  `Ideal.span (Set.range (fun i : Fin s ↦ (v (Fin.castLE hs i) : A)))`.
  `Fin.castLE hs` includes the first s zero-based indices into all d indices.
- The conclusion `IsRegularLocalRing (A ⧸ J)` gives the ordinary quotient ring its
  regular local structure; regularity is a proposition and the local structure is
  the induced one, since a local ring's maximal ideal is unique.
- `ringKrullDim (A ⧸ J) = ((d - s : ℕ) : WithBot ℕ∞)` gives exactly the finite
  Krull dimension d−s. The bound hs makes natural subtraction the usual subtraction.
- Existentials for v and b are inside the quantifier over n, so no compatibility
  between tuples is assumed. If s = 0, the range indexed by `Fin 0` is empty and
  its ideal span is zero.

Dependency declarations read and used:

- `def-weil-regular-scheme`: the ring clause of its `mathlib_match` is exactly
  `IsRegularLocalRing`, in `Mathlib.RingTheory.RegularLocalRing.Defs`. Its recorded
  `Sheaf.AlgebraicGeometry.IsRegularScheme` declaration was also read; that module
  states the scheme clause and is not needed for this ring-only theorem.
- `def-weil-vector-space-dimension`: `Module.finrank`, imported from
  `Mathlib.LinearAlgebra.Dimension.Finrank`.
- `def-weil-pbc-krull-dimension-ring`: `ringKrullDim`, imported from
  `Mathlib.RingTheory.KrullDimension.Basic`.
- Standard constituent notions are reused from Mathlib: `Module.Basis`,
  `IsLocalRing.ResidueField`, `IsLocalRing.CotangentSpace`, `Ideal.toCotangent`,
  `Ideal.span`, and ideal powers and quotients. They are not redefined.

Available proof dependencies are imported privately: Mathlib's quotient-local
structure (`Mathlib.RingTheory.LocalRing.Quotient`), surjective Noetherian image
(`Mathlib.RingTheory.Noetherian.Basic`), Nakayama's local generation criterion
(`Mathlib.RingTheory.LocalRing.Module`), and
`WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence`
(`IsRegularLocalRing.isRegular_and_quotients_of_generators`). The
`lem-sfb-regular-local-graded-cotangent-criterion` node has no recorded Lean
module in the read snapshot; it is needed only for the future proof, not to state
this item, so it has no import. The full three-step node proof is included in
the theorem docstring.

Edge cases checked before writing:

- A field has d = s = 0 and J = 0: the lifted and remaining bases are empty,
  and the quotient is the same field of dimension zero.
- s = 0 permits the empty generating tuple at every order; the hypothesis forces
  J into every power of the maximal ideal, hence J = 0 by Krull intersection.
- s = d permits the empty complementary basis: the conclusion has dimension zero.
- n = 1 is included; n = 0 is deliberately not required by the node.
- A fixed partial parameter ideal satisfies every approximation using the same
  tuple, but the signature also permits independently varying tuples.
- J = (y²) in k[x,y] localized at (x,y) fails the hypothesis (already in the
  higher jets), so a singular quotient is not accidentally included.
- The zero ring is excluded by regular-local nontriviality exactly as in the node.
  The universe u is arbitrary; there is no extraneous size constraint.

Searches for an existing statement:

- `msearch.py ... leanfinder` with “A quotient of a regular local ring is regular
  if its ideal agrees modulo every power of the maximal ideal with partial regular
  parameter ideals”: eight regular-sequence hits, including
  `RingTheory.Sequence.IsWeaklyRegular.regular_mod_prev`, none giving the criterion.
- `msearch.py ... loogle '"IsRegularLocalRing"'`: twelve hits, including
  `IsRegularLocalRing.iff_finrank_cotangentSpace` and the class definition; none
  giving the varying-parameter approximation theorem.
- `msearch.py ... grep 'Cotangent|cotangent|parameter' RingTheory/RegularLocalRing`:
  five lines in Defs.lean describing cotangent dimension, no approximation result.
- `msearch.py ... leansearch` with “Regular local quotient from parameter
  approximations modulo all powers of the maximal ideal”: eight hits, including
  Nakayama and power-quotient transition maps, none matching the theorem.
- `rg -n 'parameter.*approx|approx.*parameter|cotangent.*[Bb]asis|[Bb]asis.*cotangent|
  regularQuotient|regular_quotient' lean/WeilConjectures lean/Sheaf`: existing
  cotangent-basis and regular-quotient results, including
  RegularLocalQuotientKernelParameters and RegularQuotientCompletionKernelTest,
  but no theorem with these hypotheses. Their statements concern generation of
  an already regular quotient or completion, respectively.
- `rg -n 'lem-sfb-regular-quotient-parameter-approximation' lean/WeilConjectures`:
  no declaration carrying this node. The proposed declaration name is new.

No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by N0

A separate self-review of the node and completed signature checked every binder
and conclusion against the correspondence above. In particular, the review checked
that d is fixed by cotangent finrank, the lifts lie in the maximal ideal, the basis
is over the residue field rather than over A, the tuple depends on n, the first
s indices use the canonical inclusion, ideal addition is supremum, and both
regularity and the exact finite dimension appear in the conclusion. Empty tuples,
s = d, and d = 0 remain included. No mismatch was found and no statement was changed.
This is a self-review; the maintainer's independent review follows delivery.
