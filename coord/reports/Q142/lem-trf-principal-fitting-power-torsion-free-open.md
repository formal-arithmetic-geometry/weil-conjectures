## Worker report

The module `Sheaf.RingTheory.PrincipalFittingPowerTorsionFreeOpen` states
`LinearMap.exists_free_open_quotient_powTorsion_of_principal_fitting` with one `sorry`.
It introduces no definitions and changes only the item's `lean` field. Q26's accepted
stage-1 split, source, statement and dependency lists are retained verbatim.
The earlier worker ending concerns a duplicate stage-1 split. The current stage-2
brief §0 expressly permits stating this accepted split; the live node has no Lean
record and there is no repair note for this item.

Hypothesis and conclusion correspondence:

- A commutative ring: `{A : Type u} [CommRing A]`.
- A finitely generated A-module P: `{P : Type v} [AddCommGroup P] [Module A P]
  [Module.Finite A P]`. Ring and module universes are independent.
- Nonnegative rank r: `(r : ℕ)`, including zero.
- Elements a, h, c and a = hc: `(a h c : A) (hac : a = h * c)`.
- A prime ideal q: `(q : Ideal A) [q.IsPrime]`. Using a prime ideal directly
  gives exactly the underlying point of the recorded affine spectrum; no choice
  of scheme structure or additional prime hypothesis is introduced.
- Injectivity of multiplication by a on A: `(ha : Function.Injective
  (fun x : A ↦ a * x))`.
- Fit_r(P_q) = c A_q: `hfit` asserts existence of a surjective map from
  `Fin n → Localization.AtPrime q` to `LocalizedModule q.primeCompl P` whose
  `presentationFittingIdeal r` is
  `Ideal.span ({algebraMap A (Localization.AtPrime q) c} : Set (Localization.AtPrime q))`.
  This is the exact recorded Fitting notion, not a new ideal definition. Every
  localization of a finite module has a finite generating surjection; the recorded
  independence theorem makes the existential choice immaterial. No finite
  presentation hypothesis on P or the kernel is used.
- If r > 0, Fit_(r-1)(P_a) = 0: `hlower : 0 < r → ∃ (n : ℕ) (π : ...),
  Function.Surjective π ∧ π.presentationFittingIdeal (r - 1) = ⊥` with the
  displayed map over `Localization.Away a` and codomain `LocalizedModule.Away a P`.
  At r = 0 this imposes no condition; natural subtraction is used only under r > 0.
- Γ_(a)(P) and Q: `Submodule.powTorsion A P a` and
  `P ⧸ Submodule.powTorsion A P a`. The upstream membership theorem says exactly
  `∃ n : ℕ, a ^ n • x = 0`, including exponent zero.
- A principal open avoiding q: `∃ g : A, g ∉ q ∧ ...`.
- Q_g is A_g-free of rank exactly r: `Nonempty
  (LocalizedModule.Away g (P ⧸ Submodule.powTorsion A P a) ≃ₗ[Localization.Away g]
  (Fin r → Localization.Away g))`. A finite product of r copies is canonically
  the finite direct sum of r copies. This specifies the rank, not just freeness.

Recorded dependency declarations read and used:

- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, the FG-top class.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, with underlying
  points the prime ideals; this statement writes the prime ideal as `Ideal A`
  with `[q.IsPrime]`. The dependency module is imported.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`, its fraction
  criterion and module structure over the ring localization. This is available
  through the public imports of the torsion module and Fitting module.
- `Sheaf.RingTheory.PresentationFittingIdeal`:
  `LinearMap.presentationFittingIdeal` and
  `LinearMap.presentationFittingIdeal_independence_baseChange`; the latter's full
  signature gives independence for arbitrary surjections, arbitrary algebra base
  change and localization, without finite presentation.
- `WeilConjectures.Mathlib.Algebra.Module.Torsion`: `Submodule.powTorsion` and its
  membership description; the definition is real data, `torsion' R M (powers a)`.
- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free` (a basis exists);
  imported through the Fitting module. The conclusion uses the stronger explicit
  rank-r linear equivalence called for by this node's conclusion.
- Proof dependency `def-weil-pbc-localization-at-prime` uses
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
- Proof dependency `lem-trf-affine-principal-fitting-generators` uses
  `Sheaf.RingTheory.AffinePrincipalFittingGenerators`,
  `LinearMap.exists_fin_generators_quotient_fittingTorsion` (imported non-publicly).
  Its full existential presentation hypothesis matches the local use in the proof.

Source checked: `literature/stacks-project/flat.tex`, Tag 0810,
`lemma-helper-blowup-affine-space`, especially its final two proof paragraphs
(lines 8750–8804 in the read clone). Its principal-Fitting generator argument
and relation-coordinate cancellation are the abstracted argument of this node.
The declaration docstring records all six accepted proof steps, including
clearing denominators, the r = 0 branch, and regularity after localization.

Edge cases checked before writing:

- r = 0: the lower condition is vacuous and the conclusion is the zero module;
  spreading an empty generating family gives the required open.
- Empty generating families / P = 0: Fin 0 and finite products include them;
  Fitting ideals retain the dependency's convention n ≤ k gives the unit ideal.
- a belongs to q: allowed. No invertibility of a at q is assumed; quotienting
  by its power torsion and spreading generators are still the accepted argument.
- a = 0: injectivity forces A to be the zero ring, which has no prime q; there
  is no spurious nontrivial case. The zero ring is not excluded by a new binder.
- c = 0, h = 0: similarly impossible with a prime q and regular a.
  No domain, reducedness, Noetherianity or finite presentation is assumed.
- a a unit: power torsion is zero and the statement reduces to its specified
  local Fitting freeness criterion.
- Torsion summands such as A^r plus an a-power-torsion module are removed in Q;
  P = A/(c) with a = hc gives rank-zero quotient, as expected.
- No characteristic restriction and no universe equality is introduced.

Searches for an existing statement (2026-10-23):

- msearch.py leanfinder: "A finite module with principal rth Fitting ideal at a
  prime and vanishing lower Fitting ideal after inverting a regular element
  becomes free of rank r on a principal open after removing power torsion".
  Eight hits: finite-presentation free localization, free locus, zero localization,
  PID torsion decompositions, regular-sequence tools. No exact match.
- msearch.py leansearch: "Principal Fitting ideal at a prime gives a free open
  after quotienting a finite module by power torsion". Eight hits: free locus,
  finite-presentation localization, PID torsion. No exact match.
- msearch.py loogle: `"Fitting"`. Twelve Lie-module Fitting decomposition hits,
  unrelated to Fitting ideals of a finite module.
- msearch.py grep, RingTheory: `fittingIdeal|fitting_ideal|powTorsion|
  exists_free_localizedModule_powers`. Four finite-presentation localization hits.
  Read `Module.FinitePresentation.exists_free_localizedModule_powers` in
  Mathlib/RingTheory/Localization/Free.lean: it assumes finite presentation and
  already-free localization, unlike this finite-module Fitting criterion.
- rg in live `lean/WeilConjectures` and `lean/Sheaf`:
  `principal.*[Ff]itting|fitting.*[Tt]orsion|powTorsion|presentationFittingIdeal`.
  Found the dependency modules above and strict-transform/torsion constructions,
  not this theorem. The item-id search in both source trees returned no match.
  `dag/lean_names_upstream.json` has no matching theorem name or Fitting statement.
  The proposed declaration name has no existing source occurrence.

No new nodes, dependency repairs, statement corrections or disputes.
The first prescribed scompile.py run compiled both sandbox and library contexts
cleanly (4.5 s and 5.1 s). Only the citation's chapter title was subsequently
corrected from Divisors to More on Flatness; the Lean signature was unchanged.

## Second reading by Q142

This is a second pass by the same worker, not a claim of another agent's review:
the dispatcher brief explicitly prohibits starting other agents, and the
maintainer performs the independent review after delivery.

Re-read the node alongside the complete source file. A, P and finite generation
match the first clause; r, a, h, c, a = hc, prime q and injective multiplication
match the explicit hypotheses. `hfit` computes the local Fitting ideal on a
surjection exactly as the recorded dependency permits. `hlower` remains
conditional on 0 < r, preserving the zero-rank edge case. The quotient uses the
recorded upstream power-torsion definition, and the conclusion asserts g outside
q and an actual rank-r linear equivalence over A_g. All universes and variables
are explicitly bound, and the only theorem proof is `sorry`. All statement and
available proof dependency modules are imported, using the upstream torsion
module rather than a private copy. No mathematical mismatch was found. The
source chapter title in both docstrings was corrected to More on Flatness.
The item's accepted split and every field other than `lean` remain unchanged.
