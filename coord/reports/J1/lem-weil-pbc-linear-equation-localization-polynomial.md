## Worker report

The module `Sheaf.RingTheory.LinearEquationLocalizationPolynomial` states
`MvPolynomial.linearEquationLocalizationPolynomial`. Its only proof is `sorry`;
there are no new definitions, missing notions, dependency modules, or node corrections.
The four-step proof in the node is reproduced in the declaration docstring.

Source checked: [Stacks Tag 07EU](https://stacks.math.columbia.edu/tag/07EU),
Lemma 16.2.8, proof of `lemma-final-solve`. The local literature source was absent,
so the official online page was opened. The proof forms exactly the quotient ring
in this node and leaves smoothness over `A` localized at each coefficient as an
omitted detail. The node supplies the direct algebra isomorphism computation.
No hypotheses on the external maps `R → A → Λ` from the surrounding lemma are
needed for this standalone computation.

Hypotheses and clauses, individually matched:

- The arbitrary commutative ring is `(A : Type u) [CommRing A]`, with explicit universe `u`.
- The finite family of `r` coefficients is `(r : ℕ) (f : Fin r → A)`. The chosen
  index `(i : Fin r)` simultaneously encodes `r ≥ 1` and membership among the `r`
  variables. Indexing from zero instead of one is only relabeling; no case is lost.
- The original polynomial ring is `MvPolynomial (Fin r) A`, with variables `X j`
  and coefficient inclusion `C`. The ideal is exactly
  `Ideal.span {(∑ j : Fin r, C (f j) * X j) - 1}`. Parentheses ensure that `1`
  is subtracted once, after the sum. `B` is its quotient, and
  `q := Ideal.Quotient.mk I` is the quotient map; thus `q (X j)` is the class of `x_j`.
- `Af := Localization.Away (f i)` is the localization of `A` at the chosen coefficient.
- `Bf := Localization.Away (algebraMap A B (f i))` is the localization of `B`
  at the image of that same coefficient.
- The required `Af`-algebra structure is fixed inside the statement by
  `letI : Algebra Af Bf := (Localization.awayMap (algebraMap A B) (f i)).toAlgebra`.
  This is Mathlib's induced map on localizations, defined by the localization
  universal property, carrying `a/(f i)^n` to its image with the same denominator.
  It is not an arbitrary algebra structure supplied as a hypothesis.
- `x j := algebraMap B Bf (q (X j))` is exactly the localized class `bar x_j / 1`.
- The remaining-variable polynomial ring is
  `MvPolynomial {j : Fin r // j ≠ i} Af`. This subtype has exactly `r - 1` elements.
- The conclusion gives `∃ e : ... ≃ₐ[Af] Bf`, and the first conjunct specifies
  `e.toAlgHom = aeval (fun j ↦ x j.1)`. Thus the particular homomorphism in the
  node is an isomorphism, not merely an unspecified equivalence between the rings.
- The second conjunct, quantified over every remaining index, is
  `e.symm (x j.1) = X j`, exactly the inverse formula for `j ≠ i`.
- The third conjunct states the inverse formula for the eliminated variable:
  `e.symm (x i) = C (IsLocalization.Away.invSelf (S := Af) (f i)) *
  (1 - ∑ j : {j : Fin r // j ≠ i}, C (algebraMap A Af (f j.1)) * X j)`.
  `invSelf` is the inverse of the image of `f i` in `Af`; all other coefficients
  are explicitly mapped from `A` to `Af`.

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring` is a Mathlib leaf: `MvPolynomial` and
  `MvPolynomial.algHom_ext` in `Mathlib.Algebra.MvPolynomial.Basic`, and
  `MvPolynomial.aeval` in `Mathlib.Algebra.MvPolynomial.Eval`. Their complete
  signatures and docstrings were read. The imported Eval module supplies the
  polynomial algebra and the exact map in the first conjunct. The extensionality
  theorem is recorded in the natural-language proof, not applied in stage 2.
- `def-weil-ring-localization-away` is a Mathlib leaf: `Localization.Away`
  (the concrete powers localization) and `IsLocalization.Away` in
  `Mathlib.RingTheory.Localization.Away.Basic`. The latter's signature and
  characterization, as well as `invSelf`, were read. Concrete localizations are
  used directly, including `IsLocalization.Away.invSelf` for the inverse coefficient.
- `lem-weil-pbc-localization-away-universal-property` is a Mathlib leaf:
  `IsLocalization.Away.lift` and `lift_eq` in
  `Mathlib.RingTheory.Localization.Away.Basic`, and `IsLocalization.ringHom_ext`
  in `Mathlib.RingTheory.Localization.Defs`. Complete signatures and docstrings
  were read. The module uses `Localization.awayMap`, also read in full, whose
  implementation calls `IsLocalization.Away.map` and the localization universal
  property. Uniqueness is used in the docstring's intended proof.
- Quotients use `Ideal.Quotient.mk` and the canonical quotient algebra instance
  from `Mathlib.RingTheory.Ideal.Quotient.Operations`; this import is necessary
  for `Algebra A B` (the initial Basic-only import did not provide it).

Edge cases checked before writing:

- `r = 0`: there is no `i : Fin 0`, as there is no chosen index in the informal
  statement either. No nonempty index choice is silently assumed.
- `r = 1`: the remaining index subtype is empty and the sum is zero. The inverse
  sends the sole variable to `(f i)⁻¹`, and the polynomial ring with no variables
  is the coefficient ring. This agrees with the known one-variable result.
- `f i = 0` or nilpotent: both localizations are zero rings. No `Nontrivial`,
  regularity, field, or nonzero-coefficient hypotheses are imposed.
- The zero ring `A`, zero coefficients elsewhere, and every characteristic are
  allowed. Polynomial, quotient, localization, and algebra-equivalence definitions
  used here cover these cases.

Searches made (before writing; no exact existing declaration found):

- `msearch.py ... leanfinder`: query "A multivariate polynomial ring modulo a linear
  equation becomes a polynomial ring in one fewer variable after localizing at one
  coefficient". Eight hits: `IsLocalization.Away.mvPolynomialQuotientEquiv` and its
  apply lemma (only `Unit`-indexed `rX - 1`), `MvPolynomial.isLocalization`,
  `Algebra.Generators.localizationAway_σ`, and localization generator/evaluation
  lemmas, plus `MvPolynomial.toPolynomialAdjoinImageCompl`. None states this node.
  The full signature and docstring of the closest one-variable equivalence were read.
- `msearch.py ... loogle`: query
  `IsLocalization.Away.mvPolynomialQuotientEquiv, MvPolynomial.aeval`.
  One hit, `IsLocalization.Away.mvPolynomialQuotientEquiv_apply`, for the same
  one-variable equivalence; no exact match for an arbitrary finite family.
- `msearch.py ... leansearch`: query "localization quotient polynomial linear
  equation isomorphic polynomial ring". Service unavailable: Internal Server Error.
  This is recorded as unavailable, without a negative verdict.
- `msearch.py ... grep`: query
  `mvPolynomialQuotientEquiv|linear.*[Ee]quation|quotient.*[Aa]lgEquiv`, directory
  `RingTheory/MvPolynomial`. Three hits, all on the one-variable localization
  equivalence and its apply lemma in `Localization.lean`.
- `rg -n 'linear.*[Ee]quation|mvPolynomialQuotientEquiv'` in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and the project's `lean/Sheaf`:
  only unrelated general-linear-group Hopf-ideal equations upstream; no project hit.
- `grep -rn 'lem-weil-pbc-linear-equation-localization-polynomial'` in the source's
  `WeilConjectures`: no hit.
- Name collision search for `linearEquationLocalizationPolynomial` and
  `linear_equation_localization_polynomial` in Mathlib, the source library,
  `dag/lean_names_upstream.json`, and project Lean: no hit.

Validation: server `scompile.py` passed with exit code 0 in 1.5 seconds, no errors
and no warnings. Every variable and universe is explicitly bound. No proof was written.

## Second reading by J1

Independent verdict: the Lean says exactly what the node says. No mismatch was
found, and no Lean or node change was needed. Only this second-reading report
was added. There are no new definition nodes, dependency modules, or statement
corrections in this delivery.

I read the node and all three dependency nodes, the delivered module, and the
source declarations below. The local Stacks checkout is absent. I independently
opened the official Tag 07EU page and fetched the official `smoothing.tex` into
`scratchpad/smoothing-source.tex`, reading `lemma-final-solve`, lines 311–327.
The surrounding source assumes maps R → A → Λ, finite presentation over R,
and the singular-ideal condition. Those serve the smoothing conclusion; they
are not hypotheses of this standalone algebra computation. The node deliberately
isolates the polynomial presentation computation, valid over every commutative
ring. No source-specific hypothesis is missing.

The full object/hypothesis/conclusion checklist, with verdicts:

- A commutative ring: `(A : Type u) [CommRing A]`; exact, no field,
  Noetherian, domain, or nontriviality instance added.
- r ≥ 1, r coefficients, and a chosen index: `(r : ℕ) (f : Fin r → A)
  (i : Fin r)`; exact after relabeling indices 1,…,r as 0,…,r−1.
  Possessing i implies positivity; every positive r and every chosen index
  is represented. The order of the quantifiers is preserved.
- Original polynomial ring: `MvPolynomial (Fin r) A`, with `C` and `X`;
  exact. The dependency's finite-monomial construction and universal property
  are Mathlib's `MvPolynomial`, `aeval`, and `algHom_ext`.
- Principal ideal and quotient B: `I := Ideal.span {(∑ j : Fin r,
  C (f j) * X j) - 1}` and `B := MvPolynomial (Fin r) A ⧸ I`;
  exact. The subtraction is outside the sum. `q := Ideal.Quotient.mk I`
  is the quotient map and its variable images are the prescribed classes.
- A localized at f_i: `Af := Localization.Away (f i)`; exact powers
  localization, not a fraction field or localization requiring nonzero f_i.
- B localized at the same coefficient's image: `Bf := Localization.Away
  (algebraMap A B (f i))`; exact, using the canonical quotient algebra.
- Specified Af-algebra structure: the internal `letI : Algebra Af Bf :=
  (Localization.awayMap (algebraMap A B) (f i)).toAlgebra`; exact induced
  map on localizations, fixed by construction rather than extra arbitrary data.
- Localized variables: `x j := algebraMap B Bf (q (X j))`; exact x̄_j/1.
- Remaining-variable polynomial algebra: `MvPolynomial {j : Fin r // j ≠ i} Af`;
  exact complement of the chosen index, containing r−1 variables.
- The particular evaluation map is an isomorphism: `∃ e : ... ≃ₐ[Af] Bf`
  with `e.toAlgHom = aeval (fun j ↦ x j.1)`; exact. This equality fixes
  the forward map, so the conclusion is stronger than bare existence of an
  unrelated equivalence only in the way the node itself requires.
- Inverse on the remaining variables: `∀ j : {j : Fin r // j ≠ i},
  e.symm (x j.1) = X j`; exact, all remaining indices quantified.
- Inverse on the eliminated variable: `e.symm (x i) =
  C (IsLocalization.Away.invSelf (S := Af) (f i)) *
  (1 - ∑ j : {j : Fin r // j ≠ i},
  C (algebraMap A Af (f j.1)) * X j)`; exact coefficient inverse
  multiplying the whole parenthesis, and all other coefficients mapped to Af.

Dependency signature checks: `MvPolynomial.aeval` (Eval.lean:593) takes a
family in a commutative coefficient algebra, and `aeval_X` identifies its
variable images; `MvPolynomial.algHom_ext` (Basic.lean:436) gives precisely
uniqueness on variables. `IsLocalization.Away` (Away/Basic.lean:50) is
localization at the powers submonoid. `invSelf` (:58) is the fraction 1/f,
with `mul_invSelf`; `Away.lift` (:147) requires only invertibility of the
image and `lift_eq` (:155) fixes base-ring images. `ringHom_ext` (Defs.lean:543)
gives uniqueness. `Localization.awayMap` (:497) is `Away.map`, the induced
localization ring map. All three recorded Mathlib dependency matches are
usable as stated; no private notion or replacement dependency is needed.

Edge cases: r=0 has no i and is excluded by the informal r≥1 hypothesis;
r=1 leaves the empty variable subtype and zero sum, giving x_i ↦ f_i⁻¹.
A=0 and f_i=0 or nilpotent are allowed: both relevant localizations are
zero rings and the formula remains valid. Other coefficients may vanish;
all characteristics are allowed. `u` is bound and arbitrary; the finite
indices impose no universe restriction. Empty schemes are irrelevant to
this entirely ring-theoretic statement. Every variable and universe is
bound; no hidden test-object quantification or extra instances occur.

Independent searches (different terms from the first worker):

- LeanFinder via `msearch.py`: "Eliminating one indeterminate from a
  multivariate polynomial quotient after inverting its coefficient gives an
  algebra equivalence". Eight hits on polynomial rearrangements,
  algebraic-independence equivalences, and `finSuccEquiv`; no exact statement.
- Loogle via `msearch.py`: `MvPolynomial, AlgEquiv`. Twelve hits on
  rename/map, empty/single-variable, and Option polynomial equivalences;
  none has this localized linear quotient.
- LeanSearch via `msearch.py`: "invert a coefficient and eliminate a variable
  in a polynomial quotient by a single affine linear relation". Service
  unavailable (Internal Server Error); no negative verdict inferred.
- `rg` on Mathlib RingTheory/MvPolynomial, all upstream WeilConjectures,
  and project lean/Sheaf with `quotient.*[Ll]inear|[Ee]liminat|
  [Qq]uotient.*[Ee]quiv`: no exact match. I read the nearby
  `IsLocalization.Away.mvPolynomialQuotientEquiv` (Localization.lean:117)
  and its apply lemma: they are only the Unit-indexed rX−1 quotient itself,
  not this multivariable B localization. The upstream
  `MvPolynomial.quotientBasisEquiv` (QuotientBasis.lean:412) is a bijection
  between parameter maps and adapted ideals, not the claimed algebra isomorphism.
- Exact declaration-name `rg` across Mathlib, upstream, project Lean,
  and dag/lean_names_upstream.json: no collision.

H5/H6/H8/H9: no definitions with postponed data, no auxiliary proofs, and
only the named theorem has `by sorry`. Module and theorem docstrings name
07EU and the blueprint node; the four proof steps reproduce structure-map
construction, inverse factoring through the quotient and localization, and
both composite identities. Imports are used, namespace is `MvPolynomial`,
and lines respect 100 characters. The node's `lean.statement` matches the
file signature verbatim. Independent `scompile.py` passed, exit code 0,
compiled in 1.6 seconds, with no errors or warnings.
