## Worker report

The delivery states `RingTheory.isRegularRing_transverseLocalRootFamily` in
`Sheaf.RingTheory.TransverseLocalRootFamilyRegular`. Its only theorem has proof
`sorry`. Four concrete presentation helpers, all recorded in `lean.declarations`,
name the coefficient quotient, relation ideal, partial-root quotient, and actual
monomial classes already introduced by the item's statement. They are helpers for
this same notion, as permitted by the launcher instructions; there is no extra
independent mathematical notion, new DAG node, or dependency repair. In particular,
the quotient ring, algebra structure and monomials are real data, never choices
from existence theorems. Only the item's `lean` field changes.

The previous worker's stale-dispatch concern was about stage 1. The live node has
Q158's passing **split** review, but no `lean` or `reviewed_lean` record. This
stage-2 delivery uses that reviewed seven-step proof without re-splitting it.
There is no repair note for this item. No stage-1 statement, proof, dependency,
review, or blueprint field is changed.

The following matches every hypothesis and clause of the node.

| Node | Lean |
| --- | --- |
| Commutative regular local ring `(R,m)` | `R : Type u`, `[CommRing R]`, `[IsRegularLocalRing R]`; its maximal ideal is `IsLocalRing.maximalIdeal R`. The class includes localness and Noetherianity. |
| Finite index set and its parameters | `I : Type v`, `[Finite I]`, `t : I → R`. Both universes are explicit and independent. No enumeration or decidable equality of `I` is assumed. |
| `S = {i : t_i ∈ m}` | The predicate `t j ∈ IsLocalRing.maximalIdeal R`, used directly, so no additional arbitrary set or equality hypothesis is introduced. |
| Every `J ⊆ S` | `hstrata : ∀ J : Finset I, (∀ j ∈ J, t j ∈ IsLocalRing.maximalIdeal R) → ...`. Finsets represent all subsets of finite `I`. |
| `R_J = R/(t_j : j ∈ J)` | `transverseRootCoefficientRing t J` is the literal `R ⧸ Ideal.span (t '' (J : Set I))`. |
| Every `R_J` regular local | First conjunct of `hstrata`, `IsRegularLocalRing (transverseRootCoefficientRing t J)`. |
| `dim R_J + card J = dim R` | Second conjunct, `ringKrullDim (transverseRootCoefficientRing t J) + (J.card : WithBot ℕ∞) = ringKrullDim R`. This is extended Krull dimension, not finrank, embedding dimension, or a truncated dimension. |
| Integer `n ≥ 1` | `n : ℕ`, `hn : 0 < n`; precisely the nonnegative positive integers. |
| Image of `n` is a unit in `R` | `hnunit : IsUnit (n : R)`. |
| Every allowed pair `J,K` | Arbitrary `J K : Finset I`, `hJ : ∀ j ∈ J, t j ∈ IsLocalRing.maximalIdeal R` and `hK : Disjoint J K`. Disjointness is exactly `K ⊆ I ∖ J`. |
| Coefficient `bar t_i` | `Ideal.Quotient.mk (Ideal.span (t '' (J : Set I))) (t i)`, in the definition of `transverseRootRelationIdeal`. |
| `B_{J,K}=R_J[x_i:i ∈ K]/(x_i^n-bar t_i)` | `transverseRootAlgebra t n J K` is `MvPolynomial K (transverseRootCoefficientRing t J) ⧸ transverseRootRelationIdeal t n J K`. The ideal is the span of the range of precisely these polynomials. |
| Regular Noetherian, all prime localizations regular local | `IsRegularRing (transverseRootAlgebra t n J K)`. Mathlib's class extends `IsNoetherianRing` and asserts `IsRegularLocalRing (Localization.AtPrime p)` for every prime ideal `p`. |
| Finite free over `R_J` with the specified basis | `∃ b : Module.Basis (K → Fin n) (transverseRootCoefficientRing t J) (transverseRootAlgebra t n J K), ∀ a, b a = transverseRootMonomial t n J K a`. This is an actual basis, not just a spanning family or rank assertion. Its index type is finite, hence states finite freeness. |
| Monomial `product x_i^(a_i)` with `0 ≤ a_i < n` | `transverseRootMonomial` is the quotient map applied to `∏ i : K, MvPolynomial.X i ^ (a i).val`. The index `a : K → Fin n` covers every allowed exponent vector exactly once. |
| No henselianity, roots of unity, or all-parameters-in-maximal-ideal assumption | None is present. Parameters outside the maximal ideal remain allowed. |
| Empty `K`, basis `{1}` | The domain `K → Fin n` has one element when `K` is empty; the empty product in `transverseRootMonomial` is `1`. The empty relation span is zero and the no-variable polynomial ring is the coefficient ring. No nonempty binder excludes this case. |

The module imports the three recorded statement interfaces: the regular-scheme
node's `Sheaf.AlgebraicGeometry.IsRegularScheme` (its retained `mathlib_match`
provides `IsRegularLocalRing` and `IsRegularRing` for the ring clauses),
`Mathlib.RingTheory.KrullDimension.Basic` (`ringKrullDim`), and
`Mathlib.Algebra.MvPolynomial.Basic` (`MvPolynomial`). I opened the scheme
definition and the full ring-class signatures, Krull-dimension definition,
`MvPolynomial` definition, and the recorded `MvPolynomial.aeval` and
`MvPolynomial.algHom_ext` signatures/docstrings. The latter two express the
universal property of the polynomial notion; no second polynomial notion is
introduced. `Ideal.Quotient.algebra` in
`Mathlib.RingTheory.Ideal.Quotient.Operations` supplies the standard scalar
structure, composing `MvPolynomial.C` with the quotient map. `Module.Basis` in
`Mathlib.LinearAlgebra.Basis.Defs` supplies a linear coordinate equivalence, so
basis existence asserts uniqueness as well as existence of monomial expansions.

Every stated proof input is imported privately, and its recorded declaration
was opened with its signature/docstring:

- `Mathlib.RingTheory.AdjoinRoot`: `AdjoinRoot.powerBasis'` and the monic finite/free instances for `lem-weil-pbc-monic-quotient-free`.
- `Mathlib.RingTheory.Noetherian.Basic`: `IsNoetherianRing.of_finite` for `lem-weil-pbc-finite-algebra-noetherian`.
- `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`: the local-Noetherian `FiniteRingKrullDim` instance for `lem-weil-pbc-noetherian-local-finite-krull-dimension`.
- `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing.isDomain` for `lem-sc-regular-local-domain`.
- `WeilConjectures.RingTheory.RegularLocalLocalization`: `IsRegularLocalRing.localization_at_prime_and_isRegularRing` for `lem-weil-pbc-regular-local-localization`.
- `WeilConjectures.RingTheory.RootAlgebraRegularAtRoot`: `AdjoinRoot.isRegularLocalRing_atPrime_of_root_mem` for `lem-sbc-root-algebra-regular-at-root`.
- `WeilConjectures.RingTheory.LocalizationOfRegularRing`: `RingTheory.isRegularRing_of_localization` for `lem-weil-pbc-localization-of-regular-ring`.
- `Mathlib.RingTheory.RegularLocalRing.Polynomial`: `MvPolynomial.isRegularRing_of_isRegularRing` for `lem-trf-polynomial-ring-regular-base`.
- `WeilConjectures.RingTheory.HypersurfaceDerivationRegular`: `IsRegularRing.quotient_span_singleton_of_isUnit_derivation` for `lem-weil-pbc-hypersurface-derivation-regular`.

The theorem docstring carries all seven proof steps: iterated monic bases;
finite-dimensional dimension cancellation and nonzerodivisors; simultaneous
induction over every `J`; the prime-containing-root case and coefficient
quotient identification; the root-at-root lemma; the unit-derivative argument
after inverting the parameter; and prime localization/assembly. It does not
assert a domain structure on root algebras containing roots of units.

I read ILO IX Proposition 2.1 at printed p.133 (PDF page 139), including the
full simultaneous root algebra before taking invariants. The source uses a
strictly local situation for its covering-theoretic purpose; as the existing
reviewed node says, those extra covering hypotheses are not needed for this
algebra calculation. I also read Stacks `algebra.tex`,
`lemma-regular-mod-x` (00NU), and `more-algebra.tex`,
`lemma-quotient-regular` (07PF). No source-based correction is needed.

Edge cases checked before writing:

- Empty `I` forces empty `J,K`. The coefficient quotient, no-variable polynomial ring and empty relation quotient identify with `R`, and the basis consists of `1`.
- Empty `K` works for every allowed `J` and gives the coefficient stratum and basis `{1}`.
- `n = 1` gives one exponent vector, all exponents zero. The relations eliminate all variables and the basis is `{1}`.
- `J = S` leaves only unit parameters in `K`; the statement allows their root algebra to have several components. `IsRegularRing` imposes no unjustified domain conclusion.
- Over a field, the dimension requirement rules out any zero parameter: for singleton `J` the impossible equation would be `0 + 1 = 0`. Hence only unit parameters occur, and the assertion is consistent with a finite etale algebra.
- A repeated active parameter, for example `(s,s)` in a one-dimensional regular local ring, fails the dimension requirement for the two-element subset. The hypothesis excludes precisely this nontransverse example.
- The family `(s,1+s)` in `k[[s]]`, with positive `n` invertible, includes an active parameter and a unit. All hypotheses fit and no hidden assumption forces the second parameter into the maximal ideal.
- `[IsRegularLocalRing R]` excludes the zero coefficient ring as the original local-ring hypothesis does; no separate nontriviality assumption is added. Arbitrary `u,v` preserve all sizes of rings and finite index types.

Searches for an existing statement were run through the prescribed `msearch.py`:

- LeanFinder: `Adjoining roots of transverse parameters of a regular local ring gives a regular ring and a finite free module with monomial basis`. Eight hits about standard etale/smooth presentations, including `StandardEtalePair.Ring`; none states this ramified simultaneous family or its basis.
- Loogle: `IsRegularRing, MvPolynomial`. One hit, `MvPolynomial.isRegularRing_of_isRegularRing`, supplies polynomial regularity only.
- Mathlib grep: `MvAdjoinRoot|transverse.*[Rr]oot|[Rr]oot.*[Tt]ransverse`. One irrelevant root-system-homomorphism comment; no matching construction or theorem.
- LeanSearch: `A finite algebra adjoining nth roots of transverse regular parameters has a basis of monomials`. Eight hits, including `AdjoinRoot.powerBasisAux'`, `IsAdjoinRootMonic.basis`, and ordinary polynomial bases. These supply one-variable inputs, not this family theorem.
- Project `rg` searches for transverse roots, partial/simultaneous roots and root monomials in `lean/WeilConjectures` and `lean/Sheaf`, and the exact blueprint id in `lean/WeilConjectures`, found no matching theorem. The geometric `SNCFiniteRootRegularRing` and `SNCFiniteRootFaceRegular` modules have different geometric hypotheses and do not state the finite monomial basis; they are not equivalent existing declarations.
- Exact-name search for all five new names in Mathlib, `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` found none. Related pth-root field modules concern purely inseparable field extensions, not these quotients over coefficient strata.

There is no `STATEMENT-DISPUTED` issue or node fault. No upstream file or shared
node was edited; all authored files are in the assigned stage-2 sandbox.

Validation: `scompile.py Q153 lem-sfb-transverse-local-root-family-regular` compiled
the file both under its sandbox name and as
`Sheaf.RingTheory.TransverseLocalRootFamilyRegular`, with no errors or warnings
(6.9 s and 4.9 s respectively). The final file has `autoImplicit false`, explicit
universes, no probes, and one theorem with `sorry`. Definitions contain no `sorry`.

## Second reading by Q153

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
