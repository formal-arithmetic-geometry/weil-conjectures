## Worker report

The module `Sheaf.RingTheory.HomogeneousCoordinateLiftingCriterion` states
`MvPolynomial.homogeneous_coordinate_lifting_criterion`. Its sole proof is `sorry`.
There are no new definitions, dependency repairs, or statement corrections; only the
item's `lean` record changes.

Hypothesis and conclusion correspondence:

- `A : Type u` and `[CommRing A]` give an arbitrary commutative coefficient ring;
  `n ℓ : ℕ` and `hℓ : 0 < ℓ` give the number of variables and positive degree.
- The polynomial ring is `MvPolynomial (Fin n) A`: index `j` represents the paper's
  variable `Y_{j+1}`. No nontriviality or positivity assumption on `n` is imposed.
- `homogeneousSubmodule (Fin n) A ℓ` is exactly `V_ℓ`: its carrier is
  `IsHomogeneous ℓ`, defined by the degree of each nonzero monomial, rather than by
  a possibly incorrect equality of total degrees for the zero polynomial.
- `S : Submodule A (MvPolynomial (Fin n) A)` and `hS : S ≤ homogeneousSubmodule ... ℓ`
  render the submodule and its containment in `V_ℓ`.
- Every coordinate restriction is written using the dependency's actual canonical
  map, `aeval (fun i : Fin n ↦ if i.val < r then 0 else X i)`. It fixes coefficients,
  kills exactly the first `r` variables, and introduces no arbitrary map.
- `r : Fin n` means exactly `0 ≤ r < n`. Tail-ring membership is
  `P ∈ supported A {i : Fin n | r.val ≤ i.val}`. Mathlib's `supported_eq_range_rename`
  and `supportedEquivMvPolynomial` identify this with the polynomial ring on those
  variables. Together with `P ∈ homogeneousSubmodule ... ℓ` and `X r ∣ P`, these
  are exactly the three qualifications on `P` in the lifting hypothesis.
- `hLift` concludes `∃ Q ∈ S, aeval ... Q = P`, with no support restriction on `Q`.
  The first conclusion repeats precisely the qualifications on `r,P` and concludes
  `P ∈ S`. The second conclusion is the literal submodule equality `S = V_ℓ`.
- For each homogeneous `T`, every displayed difference is exactly
  `ρ_j(T) - ρ_{j+1}(T)` for `j : Fin n`, that is, the paper's `T_{j+1}`. The
  three conjuncts assert membership in `S`, membership in the tail subalgebra,
  and divisibility by `X j`. The final equality is `T = ∑ j : Fin n, ...`, using
  those same differences. This is the paper's entire sum from 1 through n.

Dependency declarations read and used: `def-weil-pbc-mv-polynomial-ring` records
`MvPolynomial` and `MvPolynomial.algHom_ext` in `Mathlib.Algebra.MvPolynomial.Basic`,
and evaluation `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval`.
The statement directly uses `MvPolynomial` and `aeval`, and explicitly imports Basic.
Additional existing Mathlib notions are `MvPolynomial.supported` in
`Mathlib.Algebra.MvPolynomial.Supported` and `MvPolynomial.homogeneousSubmodule`
in `Mathlib.RingTheory.MvPolynomial.Homogeneous`. All their definitions and the
recorded universal-property signatures/docstrings were read. There are no other
statement dependencies or proof-only modules to import.

Source: read the current blueprint ancestor `lem-trf-local-term-locality` and its
proof under `literature/blueprint/latest/`; this algebraic node belongs to its
historical local-invariant branch. Read Bierstone--Milman, Invent. Math. 128 (1997),
printed p.275, Lemma 8.5 and the following end of the proof of Theorem 8.1, in the
[journal PDF](https://mahalex.net/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf).
The item isolates the arbitrary-submodule version of that argument. The theorem's
docstring carries all four DAG proof steps, including subtraction of the earlier
restriction differences in the triangular induction. The source PDF is absent
locally but was available online; no source-based correction was necessary.

Edge cases checked mathematically before writing: for `n=0` the positive homogeneous
component is zero, the face quantifier is empty, and the final sum is empty. Over the
zero ring the whole polynomial ring is zero, and all displayed divisibilities and
membership claims hold. For `n=1`, the lifting hypothesis at `r=0` directly yields
membership and the difference is `T-0`. For `n=2, ℓ=1`, write `T=aX₀+bX₁`; its
pieces are `aX₀,bX₁`. The strong induction requires no restriction-stability of S
and works over rings with zero divisors, e.g. ℤ/4ℤ, without coefficient cancellation.
The excluded degree-zero case really needs exclusion: `S=0`, `A=ℤ`, `ℓ=0` satisfies
the lifting premise but is not the constant homogeneous component. No node fault or
STATEMENT-DISPUTED finding remains.

Searches actually run, before writing:

- `msearch.py ... leanfinder`: “A submodule of positive degree homogeneous multivariate
  polynomials equals the full homogeneous component if every polynomial divisible by
  the next variable on each successive coordinate face lifts from the submodule”.
  Eight hits: homogeneous-component definitions/lemmas and homogeneous localization;
  none is the triangular lifting criterion.
- `msearch.py ... loogle`: `MvPolynomial.homogeneousSubmodule, MvPolynomial.aeval,
  MvPolynomial.supported` returned zero hits for the combined query. The follow-up
  `MvPolynomial.homogeneousSubmodule` returned its definition and related graded
  lemmas, not the criterion.
- `msearch.py ... leansearch`: “A submodule of homogeneous polynomials is full if it
  lifts every polynomial divisible by the next variable on every successive coordinate
  face” returned eight hits, including the homogeneous submodule and component,
  homogeneous submodules generally, and homogeneous localization; no criterion.
- `msearch.py ... grep`: `homogeneous.*lift|coordinate.*restrict|telescop` in
  `RingTheory/MvPolynomial` returned zero hits.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for homogeneous lifts, coordinate
  restrictions/lifts, and telescoping found other coordinate constructions and
  homological telescopes; narrower reads of the ring-theory candidates found no
  match. `grep -rn` of the exact node id in `lean/WeilConjectures` returned none.
- The proposed theorem name was absent from Mathlib, both project source roots,
  and `dag/lean_names_upstream.json`. Direct Mathlib searches located and read the
  canonical `aeval`, `supported`, and `homogeneousSubmodule` definitions above.

Validation: per-file server compile through the prescribed `scompile.py`; the first
elaboration requested an explicit coefficient type on the divisibility conclusion.
The repaired statement annotates `(X j : MvPolynomial (Fin n) A)` and explicitly
binds the type of `T`. No hypothesis was changed in making that annotation.

## Second reading by Q67

A second author reading compared the node and final file clause by clause; no
independent sub-agent was started, as required by the dispatcher brief. The
independent mathematical review is the maintainer's delivery review.

The index offset was checked at both endpoints: `j=0` subtracts the first-variable
restriction from the unrestricted polynomial, and `j=n-1` subtracts the restriction
at all variables zero. Tail membership uses `≤`, retaining the current variable;
restriction uses `<`, killing just the earlier variables. The lift quantifies over
all and only eligible homogeneous tail polynomials and permits arbitrary homogeneous
lifts from S. All three main conclusions are present, including the specified
pieces and their equality to T, with no extra invariant-submodule assumption.
The coefficient annotation and explicit T binder repair elaboration only. No
mathematical discrepancy or statement change was found. All universes and variables
are bound; the module uses no private notation, helper definitions, or hidden choices.
