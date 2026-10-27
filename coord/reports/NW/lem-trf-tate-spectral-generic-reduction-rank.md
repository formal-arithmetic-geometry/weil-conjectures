## Worker report

The module `Sheaf.RingTheory.TateSpectralGenericReductionRank` states
`RestrictedSeries.tate_spectral_generic_reduction_rank`, with its sole proof `sorry`.
No definition or theorem is copied from an existing dependency, and there are no new
nodes, dependency repairs, or statement changes.

Hypothesis and clause correspondence (the node and the complete Lean file were read):

- The algebraically closed complete, nontrivially valued nonarchimedean field is
  `(K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K] [IsAlgClosed K]`. A multiplicative real absolute value is its norm.
- The valuation ring V is `(V : ValuationSubring K)` with `hV` specifying exactly
  membership by norm at most one. Its maximal ideal and residue field are Mathlib's
  `IsLocalRing.maximalIdeal V` and `IsLocalRing.ResidueField V`. The former consists
  of norm-less-than-one elements by the valuation-subring local-ring interface and hV.
  There is no assumption about a choice of uniformizer or discreteness.
- `d : ℕ` includes d = 0. T is literally
  `MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin d ↦ (1 : ℝ))`, not an
  abstract series ring. Its coefficients tend to zero in the cofinite filter.
  `MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin d ↦ 1)` is G.
- C has `[CommRing C] [IsDomain C] [Algebra K C]`; in particular it is nonzero.
  `haff` is a surjection from a finite-variable restricted-series ring commuting
  with the existing `RestrictedSeries.constants`. This is precisely the node's
  algebraic affinoid presentation. No Banach norm on C, quotient-norm hypothesis,
  or extra continuity hypothesis is imposed. The stronger normed predicate
  `RestrictedSeries.IsAffinoidQuotient` is deliberately not an assumption.
- The T-algebra structure has structure map j = `algebraMap T C`.
  `hinj` makes this injective, `hscalar` makes it K-linear, and
  `[Module.Finite T C]` is exactly the stipulated finite T-module condition.
- `ρ : C → ℝ` is completely specified by `hρ`: the supremum of the values of c
  in `C ⧸ m.asIdeal`, for actual `m : MaximalSpectrum C`, under absolute values
  extending the norm on K. The extension condition uses the quotient of the
  original scalar map. Taking all extensions avoids a choice of norms; the
  affinoid residue fields are finite over complete K and the extensions are unique,
  so it is exactly the source's supremum. No boundedness or multiplicativity of ρ
  is assumed; those are consequences of its explicit formula.
- The first conjunction is `∀ t c, ρ (algebraMap _ C t * c) = G t.val * ρ c`.
  It includes both zero factors without a side condition.
- The existential subring U has carrier exactly `G ≤ 1`. The ring homomorphism
  `red : U →+* MvPolynomial (Fin d) (IsLocalRing.ResidueField V)` is surjective,
  with `red t = 0 ↔ G t.val.val < 1`. Thus it identifies the reduction of T
  with R by the quotient-by-kernel isomorphism. The next clause specifies each
  coefficient by an actual `a : V` lifting the original coefficient, and
  `MvPolynomial.coeff m (red t) = IsLocalRing.residue V a`. This makes red the
  coefficient-reduction map, also on constants; it is not an unspecified isomorphism.
- The subring P has exactly carrier `ρ ≤ 1` and its ideal I exactly `ρ < 1`.
  Thus `P ⧸ I` is exactly S. Existence is asserted, so no ring or ideal closure
  property is hidden among the assumptions.
- `IsReduced (P ⧸ I)` states reducedness. S is not asserted to be a domain.
- `jU : U →+* P` has `(jU t).val = algebraMap _ C t.val`. The map
  `jbar : R →+* P ⧸ I` is injective and satisfies
  `jbar (red t) = Ideal.Quotient.mk I (jU t)` for every representative t.
  Surjectivity of red fixes jbar uniquely, so this is exactly the induced map.
- The final clause quantifies an R-algebra structure A with structure map equal
  to jbar. This expresses the canonical R-action without introducing a second
  definition or using a local instance. Such a structure always exists as
  `jbar.toAlgebra`, and any compatible one has the same action.
  Torsion-freeness is explicitly `r ≠ 0 → r • s = 0 → s = 0`.
- Q is `FractionRing R`. Scalar extension is `Q ⊗[R] S`, the symmetric tensor
  order used by the recorded base-change interface. Its standard Q-algebra and
  Q-module structures are Mathlib's left tensor-factor structures.
  `FiniteDimensional Q (Q ⊗[R] S)` and the subsequent `Module.finrank` inequality
  state the finite dimension and the bound. F and E are literally `FractionRing T`
  and `FractionRing C`; their scalar action in the right-hand finrank is obtained
  from `IsFractionRing.map hinj`, not an arbitrary field-extension structure.
- No claim of integrality or finite generation of S over R is made.

Recorded statement-dependency declarations used and read in full with docstrings:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs (through NormedField).
- `def-trf-restricted-series-presentation`:
  `RestrictedSeries.constants`, Sheaf.RingTheory.RestrictedSeriesPresentation;
  the same module imports Mathlib's `MvPowerSeries.IsRestricted.subring` and
  `MvPowerSeries.gaussNorm`, whose definitions were also read. Its normed-affinoid
  predicate is stronger than the algebraic notion explicitly used in this node;
  the latter is written as the displayed surjective presentation, not substituted.
- `def-weil-module-base-change`: `TensorProduct` and its left scalar action,
  Mathlib.LinearAlgebra.TensorProduct.Tower. The recorded `LinearMap.baseChange`
  signature and docstring were read; a linear map is not needed in this statement.
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional`,
  Mathlib.LinearAlgebra.FiniteDimensional.Defs.
- `def-weil-vector-space-dimension`: `Module.finrank`,
  Mathlib.LinearAlgebra.Dimension.Finrank.
- `def-weil-pbc-mv-polynomial-ring`: `MvPolynomial`,
  Mathlib.Algebra.MvPolynomial.Basic, imported by RestrictedSeriesPresentation.
- `def-weil-pbc-algebra-hom-quotient`: `Algebra`, `AlgHom` (the scalar-compatibility
  characterization), `Ideal.Quotient.algebra` and `Ideal.Quotient.mkₐ`,
  Mathlib.Algebra.Algebra.Hom and Mathlib.RingTheory.Ideal.Quotient.Operations.
  The statement uses their ring-hom versions where no coefficient algebra is needed.

The proof-dependency records were inspected. The four analytic theorem nodes
`lem-trf-affinoid-supremum-seminorm-calculus`,
`lem-trf-tate-fraction-orthogonal-spectral-norm`, `lem-trf-tate-gauss-multiplicative`,
and `lem-trf-tate-unit-ball-polynomial-reduction` have no Lean module yet, so none
can be imported now. They are named in the seven-step proof docstring. The stated
Mathlib proof dependencies are imported as plain imports:
Mathlib.RingTheory.Localization.BaseChange (`IsLocalization.tensor`) and
Mathlib.LinearAlgebra.Dimension.Finite (`LinearIndependent.fintype_card_le_finrank`).
The remaining proof dependencies are already public statement imports.

Edge cases: d = 0 (Fin 0 has its zero monomial, so constants and coefficient
reduction remain present); t = 0 and c = 0; arbitrary characteristic; inseparable
E/F; no discretely valued or spherical-completeness hypothesis; S may have zero
divisors, which does not contradict reducedness or torsion-freeness; r = 0 is
excluded only in the torsion-freeness clause as required. The zero affinoid C is
excluded by IsDomain exactly as the source requires. K and C have independent
universes u and v; the quotient and tensor sizes follow those of the actual rings.

Searches performed using the prescribed msearch wrapper:

- LeanFinder: “For a finite injective Tate algebra map to an affinoid domain the
  spectral norm is Gauss homogeneous and the reduction is torsion free with bounded
  generic rank”. Eight hits, including `spectralNorm_smul`, `spectralAlgNorm_def`,
  and field-extension spectral-norm power formulae. They are about a field extension
  with its minimal-polynomial norm; none states the affinoid reduction/rank result.
- Loogle: `spectralNorm, finrank`: zero hits (unknown identifier `finrank`).
  This was a search failure, not evidence for a match. Repeated with
  `"spectralNorm", "Module.finrank"`: successful query, zero hits.
- Mathlib grep: `TateAlgebra|spectralNorm_smul|spectralReduction`: two hits, both
  for `spectralNorm_smul` in Analysis.Normed.Unbundled.SpectralNorm; not this result.
- Direct rg of the same concepts and `restrictedSeries|RestrictedSeries|spectralValue|
  affinoid.*[Ss]up|spectral.*[Rr]eduction` in lean/Sheaf and lean/WeilConjectures
  found the existing restricted-series presentation, Grauert--Remmert, and closed-point
  comparison modules, but no matching theorem or canonical affinoid spectral reduction.
- Exact id grep in lean/WeilConjectures and exact declaration-name rg in that tree,
  lean/Sheaf, and dag/lean_names_upstream.json found no existing declaration.

Source check: opened the primary Bosch PDF at
https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf, and read printed
pp. 8--9 and 24--27 from its text. Section 1.2 gives precisely the Gauss norm and
coefficient reduction with kernel the open unit ball; Section 1.4 Lemma 12 gives
the minimal-polynomial spectral formula. The generic-rank argument is the node's
explicit agent reconstruction, retained in full in the docstring. No statement
fault or dispute was found.

## Second reading by NW

Author's second pass; no independent worker was started, in accordance with the
explicit dispatcher instruction. The maintainer provides the independent review.
I reopened the node and the full signature and compared each clause as above.
In particular I checked that haff is an algebraic quotient rather than the stronger
normed `IsAffinoidQuotient`, that hscalar fixes the original K-structure, that
coefficient reduction includes a kernel and every coefficient, that P and I have
exact rather than merely contained carriers, that jbar is forced by representatives,
and that the fraction-field action comes from hinj. No additional algebraic closure,
finite generation of S over R, domain condition on S, or separability was inserted.
The final compatible-algebra quantifier is not a finiteness assumption: instantiate
it with jbar.toAlgebra to recover the claimed scalar-extension conclusion.

Validation: the prescribed scompile.py compiled the single delivered module in
sandbox mode and library mode on the live server, exit 0, without errors or
unexpected warnings. The sandbox line includes server slot waiting (351.6 s);
the subsequent library pass took 2.3 s. No global or local build was run.
