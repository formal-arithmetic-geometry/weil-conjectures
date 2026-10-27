## Worker report

The new module `Sheaf.RingTheory.ProjectiveOrderLeadingSyzygies` states
`Hironaka.projective_order_leading_syzygies`, with its sole proof `sorry`.
No definitions or additional theorems are introduced. The node's mathematical
statement, proof and proof dependencies are unchanged. Besides `lean`, the only
node change is adding the already landed definition dependency
`def-trf-permissible-basis-chart-data`, which owns `Hironaka.InOrderSpace`.

Source read: Hironaka, *Certain numerical characters of singularities*,
J. Math. Kyoto Univ. 10 (1970), Lemma 17, printed pp.172–173, including
(16.1)–(16.2), at
https://scispace.com/pdf/certain-numerical-characters-of-singularities-18d51ii5bz.pdf
(PDF pages 22–23). This is the accepted node's finite-jet consequence, retaining
local-ring representatives of its completed coefficients. In particular, the
proof must descend coefficients using the residue-induced embedding, without
assuming the completed coefficient field contains the original copy of k.
The cited local ILO PDF is motivation, not the source of this lemma. I also
read the current blueprint/latest `lem-trf-local-term-locality` statement and
proof: it now follows the contracting-correspondence route. This algebra lemma
belongs to the imported historical branch as the accepted split_report explains;
no blueprint unit statement or proof route is changed.

Hypothesis-by-hypothesis correspondence:

- k is an arbitrary field: `{k : Type u} [Field k]`, with `universe u`
  explicitly declared. There is no characteristic, rationality, perfectness or
  separability hypothesis.
- r>=0, b>=0, e>=1: `(r b e : ℕ)` and `(he : 1 ≤ e)`.
- B=k[X_0,...,X_r]: `MvPolynomial (Fin (r + 1)) k`. Total-degree homogeneity
  comes from `MvPolynomial.IsHomogeneous`, through `InOrderSpace`; the labels
  1,...,r of the affine variables are the subtype `{i : Fin (r+1) // i ≠ 0}`.
  This has exactly r elements, including no elements when r=0.
- A prime of the affine polynomial ring: `p : PrimeSpectrum (MvPolynomial
  {i : Fin (r + 1) // i ≠ 0} k)`. The bundled point supplies `p.asIdeal.IsPrime`.
- L is `Localization.AtPrime p.asIdeal`. N=pL is written
  `IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)`. The equality
  with pL is `IsLocalization.AtPrime.map_eq_maximalIdeal`, read in Mathlib's
  `RingTheory/Localization/AtPrime/Basic.lean:524`.
- delta is exactly `algebraMap _ (Localization.AtPrime p.asIdeal)
  (MvPolynomial.dehomogenizeX k 0 f)`. The existing algebra homomorphism
  sends X_0 to 1, all other variables to their labelled affine variables,
  and preserves k; the algebraMap then sends the polynomial to its fraction /1.
- U_v is the existing predicate `InOrderSpace r p v f`: its full definition
  is `f.IsHomogeneous v ∧ delta(f) ∈ N ^ v`. No copy is introduced.
- The finite input family is indexed by `Fin b`. `(d : Fin b → ℕ)` gives
  its degrees; `hd` is `∀ j, 1 ≤ d j ∧ d j ≤ e`, `hφ_ne` requires each
  form nonzero, and `hφ` is `∀ j, InOrderSpace r p (d j) (φ j)`.
- `β : Fin b → Localization.AtPrime p.asIdeal` gives the local coefficients.
  `hβ` says beta_j lies in `N ^ (e - d j)`. Because hd includes d_j<=e,
  these natural-number subtractions are precisely the stated integer differences.
- `hsum` says the sum `∑ j, β j * delta(φ j)` belongs to `N ^ (e+1)`.

Conclusion clause-by-clause:

- The finite set V is encoded by `∃ n : ℕ` and `Fin n`. Every finite family
  can be relabelled this way, and n=0 permits the empty set. No restriction on
  cardinality is imposed by this encoding, so no output universe is required.
- `h : Fin n → ℕ` and `(∀ v, 1 ≤ h v ∧ h v ≤ e)` give the integers h_v.
- `a : Fin n → Localization.AtPrime p.asIdeal` and the next conjunct give
  `a v ∈ N ^ (e - h v)`.
- `C : Fin n → Fin b → MvPolynomial (Fin (r+1)) k` gives all C_vj.
  The first implication in the third conjunct forces `C v j = 0` when
  `h v < d j`; the second requires `InOrderSpace r p (h v - d j) (C v j)`
  when `d j ≤ h v`. These two exhaustive cases express exactly the stated
  piecewise rule, including homogeneity. A zero in the first case is homogeneous
  in every component; no negative-degree component is replaced by constants.
- The fourth conjunct is `∀ v, (∑ j, C v j * φ j) = 0` in B itself.
- The final conjunct is `∀ j, β j - ∑ v, a v * delta(C v j)
  ∈ N ^ (e - d j + 1)` in L. The exponent is e-d_j+1, with the +1 after
  subtraction; the upper degree bound ensures its intended meaning.
- Zero homogeneous polynomials are allowed by IsHomogeneous/InOrderSpace;
  ideal exponent zero is top, and finite empty sums are zero in Lean.

Recorded dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field's mathlib_match), a
  commutative division ring, with nontriviality inherited from DivisionRing.
- `Mathlib.Algebra.MvPolynomial.Basic`: `MvPolynomial`; its recorded universal
  property declarations `MvPolynomial.aeval` (in Eval) and `algHom_ext` were
  read. Evaluation is used via the existing dehomogenization construction.
- `WeilConjectures.RingTheory.GradedAlgebra.Standard`:
  `GradedAlgebra.IsStandard`, read with its grading parameters and docstring.
  This module is publicly imported as the recorded standard-grading dependency;
  no abstract standard algebra is substituted for the concrete polynomial ring.
  The actual homogeneous components use Mathlib's total-degree grading.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`
  and `IsLocalization.AtPrime.map_eq_maximalIdeal`. The dependency also records
  residue-field and fiber constructions; those clauses are not needed here.
- `Sheaf.RingTheory.PermissibleBasisChartData`: `Hironaka.InOrderSpace`,
  publicly imported, and its publicly imported existing
  `WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous`:
  `MvPolynomial.dehomogenizeX`. These definitions were read in full.
- The two proof dependencies are imported without `public`:
  `Sheaf.RingTheory.ProjectiveOrderTriangularCoordinates`
  (`Hironaka.projective_order_triangular_coordinates`) and
  `Sheaf.RingTheory.ProjectiveOrderCompletedNormalForm`
  (`Hironaka.projective_order_completed_normal_form`). Their source signatures
  and proof docstrings were read. The latter's suffix-ring indexing differs
  internally but imposes no hypothesis on this statement. The third proof
  dependency is the already publicly available multivariate polynomial ring.

Edge cases checked before writing:

- b=0: all input conditions indexed by Fin 0 are vacuous; take n=0. The
  assumed sum is zero, as are every output sum and every polynomial identity.
- Empty output n=0 is permitted also for nonempty inputs when all beta_j
  already lie in the next required power.
- r=0 or p=(0): N=0. A nonzero positive-degree form cannot belong to U_d
  (dehomogenization is injective on a fixed homogeneous component). Thus b>0
  cannot satisfy the hypotheses in these cases, while b=0 remains included.
- e=1 and d_j=e: input coefficient power is zero, hence imposes no extra
  restriction; h_v=1 and the allowed C_vj have degree zero. The error power
  is one. For r=1, p=(t), repeated forms phi_1=phi_2=X_1 and beta=(1,-1),
  the single syzygy C=(1,-1), h=1, a=1 satisfies all output clauses.
- h_v=d_j permits constants in U_0; h_v<d_j forces zero. C=0 is allowed
  in either case. Zero beta_j and zero a_v are also allowed.
- No restriction excludes positive characteristic or inseparable primes,
  such as k=F_p(a), prime (t^p-a), and the degree-p form X_1^p-a X_0^p.
  The coefficient-field subtlety of (16.1) affects the future proof only.

Searches for an existing statement (all on 2026-10-24):

- `msearch.py Q77 lem-trf-projective-order-leading-syzygies leanfinder`
  query: "Leading relations among dehomogenized homogeneous maximal order
  forms lift to homogeneous polynomial syzygies". Eight hits, including
  `HomogeneousLocalization.Away.span_mk_prod_pow_eq_top`,
  `HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top`,
  `Ideal.mem_span_pow_iff_exists_isHomogeneous`, and polynomial homogenization.
  Their reported signatures concern generating ideals, localization, or
  ordinary homogenization, not this finite-jet syzygy statement.
- `msearch.py ... loogle '"MvPolynomial", "IsHomogeneous", "LinearMap.ker"'`:
  successful search, zero hits.
- `msearch.py ... grep
  'syzyg|dehomogen|homogeneous.*relation|relation.*homogeneous' RingTheory`:
  one hit, Mathlib/RingTheory/Smooth/NoetherianDescent.lean:186, read in context.
  It is a descent calculation for a homogeneous presentation, not this result.
- `msearch.py ... leansearch` query: "Relations among initial forms of
  dehomogenized maximal order homogeneous polynomials lift to homogeneous
  syzygies with higher order remainder". Eight hits, including
  `Polynomial.homogenize`, `MvPolynomial.homogeneousComponent`, and power-series
  order results. None gives a family of homogeneous syzygies with the stated
  coefficient congruences.
- `rg -n 'projectiveOrder|projective_order|dehomogen|LeadingSyzyg|leading_syzyg'`
  in the project's `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, followed by the exact item id and declaration
  name: no existing theorem matches. Hits locate dehomogenizeX and InOrderSpace,
  which are reused. The sibling filtered-syzygy-lifting theorem concludes an
  exact completed relation, and homogeneous-approximation concludes existence
  of complementary-degree coefficients; neither states this node's result.

No STATEMENT-DISPUTED issue was found. There are no new nodes, dependency repairs
or statement corrections. All writes are in the assigned sandbox. Compilation
uses only the prescribed scompile.py wrapper; delivery uses only deliver2.py.

## Second reading by Q77

A second pass by this assigned worker reopened the node and the complete Lean
module. No separate agent was started, as the dispatcher brief expressly
prohibits it; this is a self-review, with the maintainer's independent review
still to follow.

I checked the field, r/b/e bounds, prime localization, exact order-space
predicate, nonzero forms, both degree bounds, every coefficient-power hypothesis,
and the leading sum. I then checked the existential finite indexing, both h
bounds, each a power, both mutually exhaustive coefficient-degree cases, the
polynomial identities, and each local-ring congruence. In particular the zero
branch is present explicitly; it does not silently treat negative degrees as
zero-degree polynomials. All maps use the same k and the same prime. The residue
field and completed local ring occur only in the proof docstring, not as stronger
assumptions or weaker replacement conclusions. All universes/variables are
explicitly bound; every theorem proof is exactly sorry. The source's empty and
zero cases are preserved. The imported InOrderSpace is owned by the added landed
definition dependency. No mathematical mismatch or change was found on this pass.
