## Worker report

The module `Sheaf.Analysis.Complex.HolomorphicCoordinateDivision` states
`Complex.exists_holomorphic_coordinate_division`. Its sole proof is `sorry`, as
required for stage 2. No definition, helper node, dependency repair, or statement
correction is needed. The item's original statement and every other field outside
`lean` are unchanged.

Clause-by-clause correspondence:

| Node | Lean |
| --- | --- |
| The usual complex field | `ℂ`, with Mathlib's `Complex.instField` and its usual norm and topology. |
| Integers `r,d ≥ 0` | `(r d : ℕ)`, without positivity hypotheses. |
| Normal and parameter coordinates | `(Fin r → ℂ) × (Fin d → ℂ)`, with the standard finite supremum norms and product topology. |
| A germ at `(0,0)` | `H : Filter.Germ (𝓝 (0 : (Fin r → ℂ) × (Fin d → ℂ))) ℂ`. |
| Equivalence of neighbourhood representatives | `Filter.Germ` is the quotient by eventual equality in `𝓝 0`: agreement on a smaller neighbourhood. A local complex-valued representative extends arbitrarily, for example by zero, outside its neighbourhood, so using global representative functions does not restrict the germs. |
| Holomorphic means locally convergent complex power series | `hH : ∃ f, AnalyticAt ℂ f 0 ∧ Filter.Germ.ofFun f = H`. Mathlib's `AnalyticAt` means a positive-radius convergent continuous multilinear power series; on these finite complex coordinate spaces this is precisely a convergent complex power series after grouping by total degree. Analyticity at the origin gives analyticity on a smaller open neighbourhood, so it gives the stated holomorphic representatives, not merely differentiability at one point. |
| There exist `H₁,…,Hᵣ` | `∃ Hs : Fin r → Filter.Germ (𝓝 0) ℂ`. |
| Every coefficient is a holomorphic germ in both sets of variables | `∀ j, ∃ f : ((Fin r → ℂ) × (Fin d → ℂ)) → ℂ, AnalyticAt ℂ f 0 ∧ Filter.Germ.ofFun f = Hs j`. |
| Restriction `H(0,t)`, pulled back to `(z,t)` | `H.compTendsto (fun p ↦ (0, p.2)) ((continuous_const.prodMk continuous_snd).tendsto 0)`. This composes with the canonical continuous slice retraction, which fixes the origin; no chosen representative or arbitrary map is used. |
| `H(z,t) - H(0,t) = ∑ zⱼHⱼ(z,t)` | The final equality in the germ ring, with subtraction, the finite sum `∑ j : Fin r`, and the coordinate germ `Filter.Germ.ofFun (fun p ↦ p.1 j)` multiplied by `Hs j`. Mathlib's germ ring operations are induced pointwise. |
| Empty normal or parameter dimension | Neither dimension is assumed positive or nonempty. `Fin 0 → ℂ` is the singleton zero vector space. |

Dependency and API declarations read:

- `def-weil-field` is a Mathlib leaf with `mathlib_match = ["Field"]`.
  Its full signature and docstring are in `Mathlib.Algebra.Field.Defs`:
  `class Field (K : Type u) extends CommRing K, DivisionRing K`.
  The usual complex instance is `Complex.instField` in `Mathlib.Data.Complex.Basic`;
  the public import `Mathlib.Analysis.Complex.Basic` supplies that field together
  with the required complex normed-space structures.
- `Mathlib.Order.Filter.Germ.Basic`: `Filter.Germ`, `Filter.germSetoid`,
  `Filter.Germ.ofFun`, `Filter.Germ.compTendsto` and its representative formula
  `Filter.Germ.coe_compTendsto`, plus the induced commutative-ring operations.
  In particular `compTendsto` needs an actual `Filter.Tendsto` proof; the statement
  supplies it from continuity of the canonical retraction.
- `Mathlib.Analysis.Analytic.Basic`: `AnalyticAt`, `HasFPowerSeriesAt`,
  `HasFPowerSeriesOnBall`, read with their definitions and docstrings.
  Also inspected `AnalyticAt.eventually_analyticAt` and
  `AnalyticAt.exists_mem_nhds_analyticOnNhd` in
  `Mathlib.Analysis.Analytic.ChangeOrigin` to check the representative semantics.
- `Continuous.prodMk`, `continuous_const`, `continuous_snd`, and
  `Continuous.tendsto` supply the explicit retraction continuity proof.
- There are no proof dependencies to import.

Edge cases checked mathematically before writing:

- `r=0`: every normal vector equals zero, so the slice retraction is the identity;
  the finite sum is empty, and both sides are the zero germ. Coefficient
  holomorphicity is vacuous.
- `d=0`: parameter space is a singleton; restriction is the constant germ `H(0)`.
  The conclusion is the ordinary multivariable analytic Hadamard lemma.
- `r=d=0`: a singleton domain; again `H-H=0` and an empty sum.
- A parameter-only `H(z,t)=a(t)` allows all coefficients zero.
- `H(z,t)=z₁z₂+t` with `r=2,d=1` allows `Hs₁=z₂`, `Hs₂=0`.
  `H(z,t)=z₂² exp(t)` allows `Hs₂=z₂ exp(t)` and the other coefficient zero;
  these examples check the parameter pullback and joint holomorphicity.
- Changing a representative away from an origin neighbourhood does not change
  `H`, the coordinate products, or the pulled-back germ: continuity makes the
  preimage of that neighbourhood an origin neighbourhood.

Searches (all run for this item with `msearch.py Q21
lem-sfb-holomorphic-coordinate-division` where applicable):

- `leanfinder`: "A holomorphic germ on complex coordinate space with parameters
  minus its restriction to z=0 is a sum of coordinate functions times holomorphic
  germs". Eight hits: `toMeromorphicNFAt`, `MeromorphicNFAt`, `toMeromorphicNFOn`,
  `MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt`, `MeromorphicAt`, two modular
  q-expansion declarations and a one-variable rational-function power series.
  None states joint coordinate division.
- `loogle`: `AnalyticAt, Filter.Germ`. Zero hits.
- `grep` in `Analysis/Analytic`:
  `AnalyticAt.*(div|factor)|Germ.*[Aa]nalytic|[Hh]adamard`. Three hits:
  `RadiusLiminf.lean:64` (Cauchy-Hadamard radius), and
  `Constructions.lean:244,1115` (`AnalyticAt.div_const`, `AnalyticAt.div`).
  These do not give division by a coordinate vanishing at the origin.
- `leansearch`: "An analytic function in several complex variables is the sum
  of its restriction to a coordinate slice and coordinate functions times analytic
  functions". Eight hits concerning componentwise analyticity, `along_fst`,
  finite sums, composition and `AnalyticOn`. None states the target factorization.
- `rg` in the read-only `lean/WeilConjectures` and `lean/Sheaf` for
  `coordinate.*division|coordinateDivision|holomorphic.*[Gg]erm|[Hh]adamard|Germ.*[Aa]nalytic`
  found only unrelated Groebner/specialization text and downstream proof-plan
  mentions in `AnalyticLocalCompletionComparison.lean` and
  `AnalyticClosedIdealLocalQuotient.lean`. The required
  `grep -rn 'lem-sfb-holomorphic-coordinate-division' lean/WeilConjectures`
  had no hits. No existing declaration states this lemma.
- Inspected the DAG's holomorphic-germ Taylor-jets node and the recorded consumer
  `AnalyticClosedIdealLocalQuotient`: the former uses coordinate division as an
  input and the latter needs exactly the jointly holomorphic factorization here.

Source: the node explicitly marks Serre GAGA §1 no.1, printed p.3 as WANTED
locally and the supporting Hadamard proof as agent-formulated; the theorem
docstring preserves this distinction. I read the current blueprint unit
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`.
This delivery makes no new attribution to Serre. The docstring carries all four
steps of the accepted node proof, including the coefficient-division convergence
estimate and both dimension-zero cases. No statement dispute or node fault found.

Validation: the prescribed `scompile.py` compiled both the sandbox module and
the actual library module name cleanly (15.6 s and 14.4 s). Every variable is
explicitly bound; `autoImplicit` and `relaxedAutoImplicit` are disabled. The
node's `lean.statement` is extracted verbatim from the theorem signature.
The worker delivers directly; the maintainer supplies the independent review.

## Second reading by Q21

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
