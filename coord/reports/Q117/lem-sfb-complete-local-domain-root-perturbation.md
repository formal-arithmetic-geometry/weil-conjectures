## Worker report

The module `Sheaf.RingTheory.CompleteLocalDomainRootPerturbation` states
`Polynomial.exists_root_add_of_isAdicComplete`, with proof `sorry` and the full six-step
Newton proof in its docstring. No definitions or other theorem statements are introduced.
The node is unchanged except for `lean`.

Hypothesis and conclusion correspondence:

| Node clause | Lean rendering |
| --- | --- |
| Commutative ring R | `(R : Type u) [CommRing R]`, with `universe u` explicit |
| Noetherian | `[IsNoetherianRing R]` |
| Local with unique maximal ideal m | `[IsLocalRing R]`, with m represented by `IsLocalRing.maximalIdeal R` |
| Nonzero domain with no zero divisors | `[IsDomain R]`, which includes `Nontrivial R` and multiplication cancellation away from zero |
| Dimension exactly one | `(hdim : ringKrullDim R = 1)` |
| m-adically complete, including separatedness | `[IsAdicComplete (IsLocalRing.maximalIdeal R) R]` |
| Chosen nonzero parameter in m | `(t : R) (ht_ne : t ≠ 0) (ht_mem : t ∈ IsLocalRing.maximalIdeal R)` |
| Polynomial P and element a | `(P : Polynomial R) (a : R)` |
| P(a) = 0 | `(ha : P.eval a = 0)` |
| Formal derivative nonzero at a | `(hderiv : P.derivative.eval a ≠ 0)` |
| Every integer c ≥ 0 | `∀ c : ℕ` |
| Some integer n ≥ 1, independent of Q | `∃ n : ℕ, 1 ≤ n ∧` before `∀ Q` |
| Every polynomial Q, without a degree bound | `∀ Q : Polynomial R` |
| All coefficients in t^n R | `(∀ i : ℕ, t ^ n ∣ Q.coeff i)` |
| Some b in R | `∃ b : R` |
| (P+Q)(b) = 0 | `(P + Q).eval b = 0` |
| b-a in t^c R | `t ^ c ∣ b - a` |
| No unit derivative, monicity, or degree hypotheses | There are no such binders or restrictions |

Divisibility is exactly membership in a principal ideal, by
`Ideal.mem_span_singleton : x ∈ Ideal.span {y} ↔ y ∣ x`; commutativity identifies this
ideal with yR. Natural numbers encode precisely the stated nonnegative integers, and
`1 ≤ n` preserves the required positivity. The arbitrary universe u excludes no ring.
`IsLocalRing.eq_maximalIdeal` identifies every maximal ideal with the one used here.
`AdicCompletion.of_bijective_iff` identifies the recorded completeness class with the
canonical inverse-limit map being bijective, including separatedness.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (and its finite-generation characterization).
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim : WithBot ℕ∞`, the dimension of the prime spectrum ordered by inclusion.
- `def-weil-pbc-adically-complete-ring`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `IsAdicComplete`; its Hausdorff and precomplete fields and `AdicCompletion.of_bijective_iff`
  were read to check the canonical inverse-limit formulation.
- `def-weil-polynomial-ring`: `Mathlib.Algebra.Polynomial.Basic`, `Polynomial` and
  `Polynomial.coeff`; `Polynomial.eval` and `Polynomial.derivative` supply evaluation and
  formal differentiation, with `Mathlib.Algebra.Polynomial.Derivative` publicly imported.

All four statement-dependency modules are public imports. The local-ring maximal-ideal
module is publicly imported for the local ring and its canonical maximal ideal. The two
other proof-dependency modules are plain imports, as required:
`WeilConjectures.RingTheory.LocalDomainDimOnePrincipalLocalization` (declaration
`IsLocalRing.bijective_away_lift_fractionRing_of_ringKrullDim_eq_one`, read with its complete
signature and docstring), and `Mathlib.GroupTheory.MonoidLocalization.Away`
(`Localization.Away`). The other two proof dependencies are already public statement
imports. No import cycle was encountered, and no dependency repair is needed.

Source reading: read Stacks `more-algebra.tex`, Tag 09EI, `lemma-krasner`, including its
full proof and the adjacent invocation by Tag 09EJ. Its proof constructs precision in
powers of the chosen parameter, as the node specifies. The DAG's corrected induction
starts at C = max(c, M+1); the docstring preserves this starting index and the divided
iterates argument that gives principal-ideal precision from m-adic completeness.
Read the current `literature/blueprint/latest/` direct-image stability proof (3): this
algebra lemma is a historical auxiliary input rather than the current unit's statement,
as the node's blueprint record already explains. No source or statement correction is
needed.

Edge cases checked before writing:

- c = 0: `t ^ 0 = 1`, so the proximity condition is unrestricted; no positive-precision
  assumption was silently imposed.
- Q = 0: all coefficients satisfy the hypothesis and the existing root a is permissible.
- P = 0 and constant polynomials: the derivative hypothesis excludes these, exactly as
  the node does.
- Unit derivative: included; a nonunit nonzero derivative is also included. For example,
  in k[[s]], P = sX at a = 0 has derivative s, and small perturbations have roots near zero.
- No normality, DVR structure, or characteristic-zero assumption is added. The
  one-dimensional singular complete domain k[[s²,s³]] remains in scope; a parameter s²
  and a derivative s³ need not generate the maximal ideal or be units.
- Arbitrarily large degrees of Q: all natural coefficient indices are quantified, with
  no restriction on support or degree. n is chosen before Q.
- Zero ring and fields are excluded by the original domain/dimension/parameter
  hypotheses, with no additional Lean restriction.

Searches for an existing statement (all on 2026-10-24):

- `msearch.py leansearch`, query: "Complete local domain dimension one polynomial
  nonzero derivative root small coefficient perturbation". Eight hits, primarily
  `HenselianLocalRing.is_henselian` and derivative/root multiplicity facts; no match.
- `msearch.py leanfinder`, query: "Over a complete one dimensional Noetherian local
  domain a polynomial with a root with nonzero derivative has nearby roots after
  sufficiently small coefficient perturbations". Eight hits: Henselian lifting,
  p-adic `hensels_lemma`, covering maps and nilpotent Newton lifting; no exact match.
  Read `HenselianLocalRing.is_henselian` in Mathlib: its monicity and unit derivative
  hypotheses do not state this result. Normed-field Krasner results also have different
  objects and conclusions.
- `msearch.py loogle`, query: "IsAdicComplete, Polynomial.derivative, Polynomial.eval".
  Zero hits.
- `msearch.py grep`, query: `krasner|perturb|exists.*root`, subdirectory `RingTheory`.
  Twenty-five hits, including Henselian root-lifting documentation and unrelated root
  existence results; no perturbation theorem over complete local domains.
- `rg -n 'krasner|root_perturb|rootPerturb|lem-sfb-complete-local-domain-root-perturbation'`
  in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` found only
  normed/p-adic Krasner material (`NumberTheory/Padics/Extension.lean` and the
  `RationalAlgebraicGenerator` docstring), with no duplicate statement.
- `rg` in Mathlib's `Analysis/Normed/Field` and `Dynamics/Newton.lean` found the
  normed-field Krasner declarations; these do not state this local-domain result.
- Exact-name search for `exists_root_add_of_isAdicComplete` across Mathlib, both project
  source roots, and `dag/lean_names_upstream.json`: no existing declaration.

Validation: `scompile.py Q117 lem-sfb-complete-local-domain-root-perturbation` compiled
both its sandbox form and `Sheaf.RingTheory.CompleteLocalDomainRootPerturbation` on the
server cleanly (1.3 seconds and 1.1 seconds respectively). No warnings or errors.
No STATEMENT-DISPUTED issue, node fault, new node, or dependency module.

## Second reading by Q117

Performed a separate self-review with the original node and completed module open;
no second agent was started, as the dispatcher brief prohibits that. The maintainer's
independent review remains the independent reading of the delivery.

Rechecked every row of the correspondence table against the final signature: commutative,
Noetherian, local and domain classes; exact dimension one; completeness for the canonical
maximal ideal; t nonzero and in that ideal; P and a in their original ring; root equality
and only a nonzero derivative; all c ≥ 0; positive n chosen before every Q; every
coefficient divisible by t^n; and a root b with difference divisible by t^c. In particular,
there is no accidental unit-derivative or monicity assumption and no replacement of the
principal precision by maximal-ideal precision. All variables and the sole universe are
explicitly bound. The proof docstring includes all six node proof steps, with the
C-index base case and the divided-iterate construction. No mismatch was found and no
statement change was made.
