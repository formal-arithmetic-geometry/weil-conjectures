## Worker report

States `Ideal.inf_span_eq_mul_of_h1_regular_quotient` in
`Sheaf.RingTheory.H1RegularGeneratorIdealIntersection`, with exactly one theorem
and its postponed `sorry` proof. No definitions, helper nodes, dependency repairs,
or statement corrections are needed. The source was read in full at
`literature/stacks-project/more-algebra.tex`, Tag 0665,
`lemma-H1-regular-in-quotient`, lines 7471–7494. Its statement and the node agree.
The declaration docstring carries the five-step low-degree boundary-lifting proof.

Hypothesis and conclusion mapping:

- A commutative ring: `{A : Type u} [CommRing A]`, with explicit `universe u`.
- An arbitrary ideal: `(I : Ideal A)`.
- Any finite length, including zero: `{r : ℕ}`.
- The sequence of elements: `(g : Fin r → A)`; the shift from 1-based paper
  indices to `Fin r` changes no data or order.
- Reduction modulo the specified ideal: `fun i : Fin r ↦ Ideal.Quotient.mk I (g i)`.
- H₁-regularity of those images:
  `RingTheory.Sequence.IsH1Regular (R := A ⧸ I) (...)`. The recorded definition
  is precisely `IsZero ((ExteriorAlgebra.koszulComplex (A ⧸ I) r ...).homology 1)`.
- The generated ideal G: Mathlib `Ideal.span (Set.range g)`; no duplicate definition.
- The entire conclusion I ∩ G = IG:
  `I ⊓ Ideal.span (Set.range g) = I * Ideal.span (Set.range g)`.
- No Noetherian, locality, properness, or nontriviality binders occur.

Dependency declarations read and used:

- `WeilConjectures.RingTheory.KoszulRegularSequence`:
  `RingTheory.Sequence.IsH1Regular`, clause (4) of
  `def-weil-pbc-koszul-regular-sequence`; imported publicly for the hypothesis.
- `WeilConjectures.AlgebraicGeometry.KoszulComplex`:
  `ExteriorAlgebra.koszulComplex`, `koszulBoundary`, and `koszulBoundary_comp`;
  proof dependency, imported non-publicly.
- `Sheaf.Paper.KoszulDifferentialSquareZero`:
  `ExteriorAlgebra.koszul_differential_square_zero`; proof dependency,
  imported non-publicly.
- Mathlib `LinearAlgebra.ExteriorPower.Basis`: `Module.Basis.exteriorPower`
  and `exteriorPower.coe_basis`, with `exteriorPower.zeroEquiv` and
  `exteriorPower.oneEquiv` from `LinearAlgebra.ExteriorPower.Basic`;
  these are the recorded mathlib_match of `lem-weil-pbc-exterior-power-free-basis`.
  The basis module is imported non-publicly for the proof dependency.

Edge cases checked mathematically before writing:

- r = 0: `Set.range g` is empty, G = 0, and both ideals in the conclusion are zero.
- r = 1: H₁-regularity is injectivity of multiplication by the image of g;
  no degree-two lift is needed because that term vanishes.
- I = top: the quotient is the zero ring, so H₁ vanishes and top ∩ G = top * G = G.
- I = bottom: both sides are zero; the H₁ hypothesis is retained as in the source.
- The zero ring: no excluded case and every ideal equality holds.
- No properness of G is necessary (a unit among the generators is allowed).
- The hypothesis is substantive: for A = Z, I = (2), r = 1, g = 2,
  it fails, as H₁ of the zero singleton over Z/2 is nonzero; also (2) ∩ (2)
  differs from (2)(2). Thus it cannot be silently dropped.

Searches for an existing exact statement (2026-10-24):

- msearch leanfinder, "If a finite sequence is H1 Koszul regular modulo an ideal I,
  its generator ideal G satisfies I intersection G equals I times G": eight hits,
  all ordinary regular-sequence results; none states this H₁ hypothesis.
- msearch loogle, `Ideal, "inf", "mul"`: twelve hits, including
  `Ideal.mul_le_inf` and coprime-ideal equalities; none has this hypothesis.
- msearch grep, `H1Regular|[Kk]oszul.*[Ii]ntersect|inf_span.*mul`, subdirectory
  `RingTheory`: zero Mathlib hits.
- msearch leansearch, "H1 regular sequence modulo an ideal implies intersection
  of its generated ideal equals ideal product": eight hits, including coprime
  and Dedekind identities and ordinary regularity; no match.
- rg of `lean/WeilConjectures` and `lean/Sheaf` for H1Regular, regular quotient,
  and inf_ofList found the required H₁ definition and
  `Ideal.inf_ofList_eq_mul_of_regular_quotient` and its auxiliary inclusion.
  Their complete source signatures require `RingTheory.Sequence.IsRegular`,
  strictly stronger than H₁-regularity over an arbitrary ring; neither is a match.
- rg for this node id in `lean/WeilConjectures` found no declaration; rg for the
  proposed declaration name in both project trees, Mathlib and
  `dag/lean_names_upstream.json` found no collision.

No STATEMENT-DISPUTED flag or node fault. All work is confined to the assigned sandbox.
The initial server compilation passed cleanly; the final import-complete module
is checked again by scompile and the delivery dry run.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
