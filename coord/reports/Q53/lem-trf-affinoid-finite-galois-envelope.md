## Worker report

The module `Sheaf.RingTheory.AffinoidFiniteGaloisEnvelope` states
`RestrictedSeries.affinoid_finite_galois_envelope`. Its only proof is `sorry`.
No definitions, dependency repairs, new nodes, or statement corrections are needed.

Hypothesis and clause correspondence:

- The field is `K : Type u` with `NormedField K`, `IsAlgClosed K`,
  `IsUltrametricDist K`, and `CompleteSpace K`. The hypothesis `hK` says
  some nonzero scalar has norm different from one, exactly nontriviality of
  the real-valued nonarchimedean absolute value.
- The given algebra is `C : Type v`, with `NormedCommRing C`, `Nontrivial C`,
  and `IsReduced C`. Its scalar map is `scalar : K →+* C`.
  `hC : RestrictedSeries.IsAffinoidQuotient K C scalar` is the recorded
  dependency's complete quotient-Gauss-norm presentation, not an unrelated norm.
- The conclusion chooses `s : ℕ` with `1 ≤ s` and a family `B : Fin s → Type (max u v)`.
  Each component has an existential `NormedCommRing` structure, together with its
  `IsAffinoidQuotient` presentation using exactly `(j i).comp scalar`.
  Thus the asserted Banach norm is part of the chosen component, with no extra
  norm or completeness assumption in the hypotheses.
- `j : ∀ i : Fin s, C →+* B i` are the required component maps.
  `Function.Injective (fun c : C ↦ fun i ↦ j i c)` says their product is injective.
  Individual component maps need not be injective.
- `d : Fin s → ℕ` allows every nonnegative normalization dimension. The domain
  of `t i` is the actual Mathlib restricted-series subring in `Fin (d i)` variables
  at polyradius one. `Function.Injective (t i)` states the Tate inclusion.
- `(j i).Finite` and `(t i).Finite` use Mathlib `RingHom.Finite`, which is precisely
  finite generation as a module via that particular map's `toAlgebra` structure.
- `(t i).comp (constants K (d i)) = (j i).comp scalar` makes both maps unital
  K-algebra maps with the same scalar action, as in the source's affinoid algebras.
- `IsDomain (B i)` includes nonzeroness. `IsIntegrallyClosed (B i)` is integral
  closedness in its fraction field, precisely the node's normal-domain convention.
  The analogous `IsDomain` and `IsIntegrallyClosed` assertions are made for each
  actual Tate algebra, without assuming them.
- An existential fraction-field `Algebra` structure is constrained by the equation
  between the composite through `Frac(T_i)` and the composite through `B_i`.
  This uniquely specifies the field map induced by the actual `t i`; an arbitrary
  unrelated field embedding is not permitted. `FiniteDimensional` gives finiteness,
  and `IsGalois` gives separability and normality over this very map.
- The final existentials choose positive real `D,E`. The two inequalities are
  `‖j i c‖ ≤ D * ‖c‖` for every c and `‖t i a‖ ≤ E * gaussNorm ... a.val`
  for every restricted series a, using the original Gauss norm and the chosen
  component's quotient norm.

Dependencies read and used:

- `def-weil-field`: Mathlib `Field` (from `Mathlib.Algebra.Field.Defs`), supplied
  by the stronger normed-field structure.
- `def-trf-restricted-series-presentation`:
  `Sheaf.RingTheory.RestrictedSeriesPresentation`, specifically
  `RestrictedSeries.IsAffinoidQuotient` and `RestrictedSeries.constants`.
  Their full definitions and source docstrings were read. The restricted subring
  and Gauss norm are Mathlib's `MvPowerSeries.IsRestricted.subring` and
  `MvPowerSeries.gaussNorm`, used through that module's public imports.
- Mathlib `RingHom.Finite` (`Mathlib.RingTheory.Finiteness.Defs`),
  `IsIntegrallyClosed` (`Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`),
  `FractionRing`, `FiniteDimensional`, and `IsGalois`
  (`Mathlib.FieldTheory.Galois.Basic`) express the remaining ordinary notions.

Proof dependencies with recorded modules are imported privately:
`Sheaf.RingTheory.AffinoidPolynomialClosedPointComparison` and
`WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions`;
the Mathlib modules for integral closure, minimal primes in a Noetherian ring,
finite fraction-field degree, integral finite algebras, finite algebras being
Noetherian, fraction fields of integral closures, and finiteness of separable
integral closures. Their recorded interfaces were checked. The five analytic
proof dependencies without a Lean record are mentioned by id in the proof
docstring but have no available module to import:
`lem-trf-affinoid-homomorphism-bounded`,
`lem-trf-finite-algebra-affinoid-presentation`,
`lem-trf-tate-integrally-closed`, `lem-trf-tate-normalization-lift`, and
`lem-trf-tate-variable-roots-separable-compositum`.
These are proof dependencies only; none is needed to type the statement.

Edge cases checked: C = 0 is excluded exactly as the node requires; a reduced
product can have noninjective individual maps j_i, which are allowed; the output
index set is nonempty by `1 ≤ s`; d_i = 0 remains allowed and the Tate ring then
has only constant series; characteristic zero and positive characteristic are
both allowed (no perfectness assumption on the Tate fraction field); trivial
absolute values are excluded by hK. Separate universes u,v are retained, and
components are chosen in max u v, which can contain the finite algebraic
constructions over both K and C. No test-object quantifier has a smaller universe.

Searches (2026-10-24), using the prescribed `msearch.py` wrapper:

- LeanFinder: "A reduced affinoid algebra embeds finitely into a product of normal
  affinoid domains with finite Galois fraction fields over Tate algebras". Eight
  hits included `Ring.instFiniteNormalClosure_1` and polynomial Noether normalization.
  Neither is this analytic envelope theorem; the polynomial theorem uses a different
  ring and the normal-closure result does not give these analytic presentations.
- Loogle: `IsGalois, FractionRing`. Three hits included
  `Ring.instIsGaloisFractionRingNormalClosure` and integral norm identities.
  No complete envelope assertion; that normal-closure instance also presupposes
  separability over the Tate fraction field.
- Mathlib grep: `affinoid|TateAlgebra`. Zero matches.
- LeanSearch: "A reduced affinoid algebra admits finite normal affinoid envelopes
  with Galois fraction fields over Tate algebras". Eight hits, including the
  algebraic normal-closure instance and reducedness lemmas for schemes. No match.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`:
  `affinoid.*[Gg]alois|[Gg]alois.*[Ee]nvelope|finite_galois_envelope`.
  No matches. `grep -rn` for the node id in `lean/WeilConjectures` also found none.
  The proposed declaration name was additionally searched in both source roots
  and `dag/lean_names_upstream.json`; no collision.

The cited Kedlaya PDF p. 2 and Conrad Theorem 1.2.6 were opened. The existing
node already records the positive-characteristic variable-root preparation, so
no source correction is necessary. No STATEMENT-DISPUTED issue found.

## Second reading by Q53

Written by the maintainer's second reader (cc review service), replacing a section
that stated no independent reading was performed. Lean read against the node
statement, the recorded dependency module `Sheaf.RingTheory.RestrictedSeriesPresentation`
(`constants`, `IsAffinoidQuotient`) and Mathlib `MvPowerSeries.gaussNorm`.

Node list and Lean rendering:

1. K algebraically closed field, complete, nontrivial real nonarchimedean absolute value:
   `NormedField K` (multiplicative norm = absolute value), `IsUltrametricDist K`,
   `CompleteSpace K`, `IsAlgClosed K`, `hK : ∃ a ≠ 0, ‖a‖ ≠ 1`. Correct, no extra assumption.
2. C ≠ 0 reduced quotient of a restricted-series ring with Tate quotient Banach norm:
   `NormedCommRing C`, `Nontrivial C`, `IsReduced C`, `scalar`, `hC : IsAffinoidQuotient K C scalar`
   (completeness + surjection from K<X_1..X_n> over `scalar` + norm equal to the quotient Gauss norm).
   Correct; the given norm is pinned to the quotient norm.
3. s ≥ 1, B_1..B_s: `∃ s, 1 ≤ s ∧ ∃ B : Fin s → Type (max u v)`, with the ring and norm
   jointly in the existential `NormedCommRing (B i)`. Correct (larger universe only weakens
   the existential harmlessly; the construction lives in Type u ⊆ max u v).
4. maps j_i, injective T_i = K<U_1..U_{d_i}> → B_i, d_i ≥ 0: `j i : C →+* B i`, `d : Fin s → ℕ`,
   `t i` on Mathlib's restricted subring at polyradius 1, `Function.Injective (t i)`;
   K-linearity via `(t i).comp (constants K (d i)) = (j i).comp scalar`. Correct.
5. B_i finite over C through j_i and over T_i: `(j i).Finite`, `(t i).Finite` (RingHom.Finite). Correct.
6. j = (j_i) injective: `Function.Injective (fun c ↦ fun i ↦ j i c)`; individual j_i not
   required injective. Correct.
7. B_i nonzero normal domain: `∃ _ : IsDomain (B i), IsIntegrallyClosed (B i)`. Correct.
8. T_i integrally closed domain: existential `IsDomain`, `IsIntegrallyClosed` on the Tate ring
   (as conclusions, not assumptions). Correct.
9. Frac(B_i)/Frac(T_i) finite Galois: existential `Algebra` on the fraction rings pinned by
   the compatibility with `t i` (determines it uniquely since t i is injective, by the
   localization universal property; smul is fixed by `smul_def`), then `FiniteDimensional`
   and `IsGalois`. Correct, no arbitrary embedding.
10. Tate quotient Banach norm on B_i with bounded structure maps:
    `IsAffinoidQuotient K (B i) ((j i).comp scalar)` and `∃ D E > 0`,
    `‖j i c‖ ≤ D‖c‖`, `‖t i a‖ ≤ E · gaussNorm a`. Correct; Gauss norm with `norm` and radius 1
    as in the dependency.

Edge cases: C = 0 excluded by `Nontrivial C`; s ≥ 1; d_i = 0 allowed (constants only);
characteristic 0 and p both allowed, no perfectness of Frac(T_i) assumed (the inseparable
part is absorbed in the node's proof by root variables); trivial absolute value excluded.
Truth: affinoid finite-over-affinoid presentations and automatic boundedness (Conrad 1.2.6(2),(3))
give the analytic clauses; the algebraic clauses follow the node's steps 1–6.

Records: `lean.statement` is verbatim the file signature; stmt_deps (def-weil-field,
def-trf-restricted-series-presentation) cover the project notions used; everything else is
Mathlib. Docstrings carry source and `(blueprint: ...)`, the proof docstring follows the seven
node steps; proof is `sorry`; no definitions; no pro-étale content.
Searches: grep of Mathlib, lean/Sheaf and lean/WeilConjectures for affinoid/Tate envelope
declarations: none besides the dependency module. No change to the Lean.
