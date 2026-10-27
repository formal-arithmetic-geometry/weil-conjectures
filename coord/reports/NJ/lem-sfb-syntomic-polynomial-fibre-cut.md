## Worker report

The module `Sheaf.RingTheory.SyntomicPolynomialFibreCut` states
`Algebra.exists_syntomic_localization_of_polynomial_reduction`, with its sole proof
`sorry`. It formalizes lem-sfb-syntomic-polynomial-fibre-cut without changing the
natural-language statement or its dependencies. Source read: Stacks Project,
`smoothing.tex`, Tag 07M8, proof of assertion (1), from “Choose f_1,...,f_n in D”
through the proof of the final claim. The docstring includes all seven DAG proof
steps and identifies their ingredients. No new nodes or dependency repairs are needed.

Clause-by-clause correspondence:

- `R : Type u`, `D : Type v`, their `CommRing` instances and `[Algebra R D]`
  supply the arbitrary commutative base ring and the ring map R → D. `I : Ideal R`
  is an arbitrary ideal, with no nilpotence or finiteness restriction.
- `[Module.Flat R D]` and `[FinitePresentation R D]` give the first two syntomic
  conditions. `hciD` supplies local complete intersection fibres for EVERY
  `p : PrimeSpectrum R`. `p.asIdeal.Fiber D` is Mathlib's κ(p) ⊗[R] D,
  canonically the same commutative fibre algebra as D ⊗[R] κ(p).
- `A₀ : Type w` has `[CommRing A₀] [Algebra (R ⧸ I) A₀]`, the required
  quotient-base algebra, with its own independent universe. The two instances
  `[Module.Flat (R ⧸ I) A₀] [FinitePresentation (R ⧸ I) A₀]` and `hci₀`
  give exactly its three syntomic conditions, with fibres at all quotient-base primes.
- `r : ℕ` indexes the polynomial variables by `Fin r`. `θ` is a ring equivalence
  from `D ⧸ I.map (algebraMap R D)` to `MvPolynomial (Fin r) A₀`.
  `hθ` is its scalar compatibility: the image of any scalar represented by x ∈ R
  is the constant polynomial of its image in A₀. Since R → R/I is surjective,
  this is precisely the R/I-algebra-isomorphism requirement. The pair θ,hθ
  encodes that isomorphism without introducing a separate quotient algebra instance
  or asking for any extra structure or hypothesis.
- `t : Fin r → D` and `ht` give the chosen lifts, with θ(tᵢ mod ID) = Xᵢ.
  Every occurrence of A is the literal quotient `D ⧸ Ideal.span (Set.range t)`;
  A is therefore exactly D/(t₁,...,tᵣ), rather than an arbitrary algebra or map.
- The existential element `a` belongs to precisely this quotient A. Its equation
  `Ideal.Quotient.mk (I.map (algebraMap R A)) a = 1` says a reduces to 1 in A/IA.
  The induced ring isomorphism A/IA ≅ A₀ preserves and reflects 1, so this is
  exactly the stipulated image under that induced isomorphism. It does not require
  a choice of an unrelated comparison isomorphism.
- The existential proof of `FinitePresentation R (Localization.Away a)`, the
  following `Module.Flat R (Localization.Away a)` and the local complete
  intersection assertion at EVERY prime of R give exactly syntomicity of R → Aₐ.
  Finite presentation is bound before the last clause so its implied finite-type
  instance can be used in the definition of local complete intersection.

Dependency declarations read and used:

- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, `RingHom.flat_algebraMap_iff`,
  and `Module.Flat`. For an algebra map, the latter is exactly ring-map flatness.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation` and its
  finite-type consequence. `Mathlib.RingTheory.FiniteStability` supplies
  `Algebra.FiniteType.baseChange` for the fibre types; it adds no hypothesis.
- `WeilConjectures.RingTheory.CompleteIntersectionOverField`:
  `Algebra.IsGlobalCompleteIntersection` and `Algebra.IsLocalCompleteIntersection`.
  The latter is used unchanged, including its finite-type parameter and principal cover.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap` read for the recorded residue-field dependency.
  Ring fibres use the algebraic specialization `Ideal.ResidueField` and
  `Ideal.Fiber`, supplied by `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`;
  this is the residue field of the prime localization, not a replacement notion.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`, `MvPolynomial.C`,
  `MvPolynomial.X`, and its algebra-map/extensionality interface. `MvPolynomial.aeval`
  in the recorded evaluation module was also read; no new polynomial notion is made.
- `Mathlib.GroupTheory.MonoidLocalization.Away`: `Localization.Away`; ring and
  algebra instances are imported through `Mathlib.RingTheory.Localization.Away.Basic`.

Recorded proof modules are imported without `public`: syntomic-at-prime-relative-
global-complete-intersection, relative-global-complete-intersection-base-change,
global-complete-intersection-equidimensional, dimension-at-point-open-subspace,
equation-count-localize-relative-global-complete-intersection, and relative-global-
complete-intersection-principal-localization. Mathlib proof dependencies are available
through the flat, fibre, prime-topology and localization-base-change modules. The two
proof-only DAG nodes `lem-sfb-polynomial-zero-section-dimension` and
`lem-trf-relative-ci-principal-cover-syntomic-gluing` have no recorded Lean declaration
in the read clone and are not needed to TYPE this statement; no duplicate statements
for those independent lemmas are introduced. Their future imports belong to the
maintainer when those lemmas are stated.

Edge cases checked before writing:

- r = 0: `Fin 0` is empty, the lift condition is vacuous, its span is the zero
  ideal, and A = D. Localizing at 1 gives D. No positive-r assumption appears.
- A₀ = 0: the polynomial reduction is zero, so ID = D, hence IA = A. The choice
  a = 0 has residue 1 = 0 and its zero localization is allowed. Complete
  intersection uses the recorded convention admitting the zero ring.
- I = top: R/I and A₀ are zero, giving the same permitted zero-localization case.
- I = bot: the congruence requires a = 1. Cutting the polynomial variables gives
  A ≅ A₀, which is syntomic by hypothesis; the conclusion has the correct strength.
- R = 0 or D = 0: empty prime spectra make the relevant fibre condition vacuous,
  consistently with syntomicity of the zero algebra; no `Nontrivial` instance is imposed.
- No Noetherian, reducedness, nilpotence, nonempty cover, or universe equality is imposed.

Searches for existing declarations (2026-10-24):

- `msearch.py`, leanfinder: “Quotient a syntomic algebra by lifts of polynomial
  coordinates in its closed reduction, then localize by an element congruent to
  one to obtain a syntomic algebra”. Eight hits, principally StandardEtalePresentation,
  StandardEtalePair and Algebra.IsStandardSmooth. No syntomic coordinate-cutting result.
- `msearch.py`, loogle: `Module.Flat, MvPolynomial`. Zero hits.
- `msearch.py`, grep in RingTheory: `[Ss]yntomic|polynomial.*fibre.*cut`. Zero hits.
- `msearch.py`, leansearch: “A syntomic algebra with polynomial reduction over a
  quotient ring admits a syntomic localization after killing lifts of the polynomial
  variables”. Eight hits, including `IsLocalization.Away.mvPolynomialQuotientEquiv`,
  formally etale localizations, polynomial localizations and quasi-finite localization.
  None has the node's hypotheses and syntomic conclusion.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf`: `syntomic|Syntomic`,
  `syntomic-polynomial-fibre-cut`, and polynomial/cut name patterns. Existing results
  treat local syntomic charts, presentation kernels, descent and the larger
  surjection-lifting theorem. The latter's docstring cites this missing lemma;
  it does not state this lemma. No duplicate declaration was found.

No STATEMENT-DISPUTED issue or source correction was found. The first compile
identified a missing finite-type base-change import. Adding the existing Mathlib
`FiniteStability` instance module repairs all three fibre elaboration points without
altering any hypotheses or conclusions. All universes and variables are explicit,
with `set_option autoImplicit false` in the delivered file.

Validation: `scompile.py NJ lem-sfb-syntomic-polynomial-fibre-cut` compiled the
single delivered file successfully against current server sources (2.7 seconds,
60-second limit, two threads). The wrapper's initial private compile area ran out
of space; its prescribed server confirmation succeeded with no Lean errors or
unexpected warnings. No tool or shared build was modified.

## Second reading by NJ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
