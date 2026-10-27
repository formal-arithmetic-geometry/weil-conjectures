## Worker report

The module `Sheaf.RingTheory.LocalizedFibrePrimeFactor` states
`AdjoinRoot.exists_unique_localized_fibre_prime_factor`, with its proof `sorry`.
The statement and all pre-existing dependency fields of the node are unchanged.
The two real-data helpers `AdjoinRoot.localizedMap` and
`AdjoinRoot.localizedFactorIdeal` only compose the existing quotient map,
localization map and ideal-extension operations. They introduce no independent
notion or assumption and have source/blueprint docstrings. No new nodes or
dependency repairs are needed.

Source checked: Stacks Project, `literature/stacks-project/algebra.tex`,
Tag 00UF, `lemma-standard-etale-finite-flat-Zariski`, especially the paragraph
beginning “Let overline f denote the image of f”. It identifies the given prime
with an irreducible residue-field factor avoiding the reduced g. The node expands
this identification with canonical contraction, fraction membership and uniqueness.
The current blueprint unit `sec-trace-formula/sk-i-curve-zero/_section.md` was
also read; this item is a refinement below its local-term-locality input, not the
unit statement.

Hypotheses and objects, matched clause by clause:

- Commutative ring R: `{R : Type u} [CommRing R]`, with explicit universe `u`.
  There is no Noetherian, domain, local, characteristic or field hypothesis on R.
- The polynomials f and g: `(f g : Polynomial R)`; monicity is `(hf : f.Monic)`,
  which Mathlib defines as leading coefficient equal to one.
- A = R[t]/(f): `AdjoinRoot f`, defined by Mathlib as the quotient by
  `Ideal.span {f}`. Its polynomial quotient map is `AdjoinRoot.mk f`, and its
  coefficient map is `AdjoinRoot.of f`.
- g_A: `AdjoinRoot.mk f g`; B: `Localization.Away (AdjoinRoot.mk f g)`.
  The localization map out of A is its canonical `algebraMap`.
- A prime q of B: `(q : Ideal (...)) [q.IsPrime]`.
- Its contraction p to R: `(p : Ideal R) [p.IsPrime]` and the equality `hp`
  with `Ideal.comap` along the composite of `AdjoinRoot.of f` and the canonical
  localization map. This names the contraction, rather than restricting q:
  its contraction is automatically prime, and every q in the node supplies
  these data.
- k = κ(p): `p.ResidueField`, using the recorded dependency's Mathlib notion.
  No arbitrary field or embedding replaces the residue field.
- ρ: coefficient application of `algebraMap R p.ResidueField`; written as
  `P.map (algebraMap R p.ResidueField)` for any polynomial P. Thus f_k and g_k
  are exactly the two displayed mapped polynomials.
- The quotient over k: `AdjoinRoot (f.map φ)`, with φ the residue map.
  The fibre F is localized at
  `AdjoinRoot.map φ f (f.map φ) (dvd_refl _) (AdjoinRoot.mk f g)`.
  This is the class of `g.map φ`: `AdjoinRoot.map` is the quotient map induced
  by coefficient application, as follows also from its definition via
  `AdjoinRoot.lift`, `lift_mk`, and polynomial evaluation at the quotient root.
  This spelling avoids introducing an equality cast between the two equal
  localizers. It does not replace F with an arbitrary ring or tensor model.
- The canonical j: `AdjoinRoot.localizedMap φ f g`, defined by the exact
  `Localization.awayMap` of that canonical `AdjoinRoot.map`. The only proof
  supplied to the quotient map is Mathlib's `dvd_refl`; no choice or postponed
  theorem constructs this map.

Conclusion, matched clause by clause:

- Existence: `∃ h : Polynomial p.ResidueField`.
- Monic and irreducible: `h.Monic ∧ Irreducible h`. Mathlib's irreducibility
  says nonunit and every factorization has a unit factor. In the polynomial
  ring over the nonzero field κ(p) it also implies h ≠ 0; this is exactly the
  node's nonzero irreducible convention.
- Factor and avoidance: `h ∣ f.map (...)` and `¬ h ∣ g.map (...)`.
- The ideal ((h)/(f_k))F: `localizedFactorIdeal φ f g h` is explicitly
  `Ideal.map` of the `Ideal.map` of `Ideal.span {h}`: first along
  `AdjoinRoot.mk (f.map φ)`, then along the localization's `algebraMap`.
  Thus both the quotient ideal image and its extension to F are included.
- The contraction identity: `q = Ideal.comap (localizedMap φ f g)
  (localizedFactorIdeal φ f g h)`.
- The explicit fraction test: universally quantified `(P : Polynomial R)` and
  `(m : ℕ)`, with `Localization.mk (AdjoinRoot.mk f P)` over the explicitly
  typed powers-submonoid element whose value is `(AdjoinRoot.mk f g)^m`.
  Membership in q is equivalent to `h ∣ P.map (...)`.
- Uniqueness is the last universal clause, for every `h' : Polynomial κ(p)`
  satisfying monicity, irreducibility, factor, avoidance and the same ideal
  contraction, concluding `h' = h`. A competing h' is not required to satisfy
  the explicit fraction test. Thus uniqueness has precisely the scope of the
  node's original defining conditions, rather than a smaller candidate class.

Dependency declarations read and used:

- `def-weil-polynomial-ring`: `Mathlib.Algebra.Polynomial.Basic`, `Polynomial`;
  also `Polynomial.Monic`, `Polynomial.map` through the quotient API.
- `def-weil-ring-localization-away`:
  `Mathlib.GroupTheory.MonoidLocalization.Away`, `Localization.Away`;
  `Mathlib.RingTheory.Localization.Away.Basic`, `Localization.awayMap`.
- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`;
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, `Ideal.ResidueField`.
  The latter is the residue field of the former. The additional `Ideal.Fiber`
  signature/docstring was read, but this node specifies the explicit localized
  polynomial quotient model and does not need a tensor-product fibre.
- Quotient construction, from `Mathlib.RingTheory.AdjoinRoot`: `AdjoinRoot`,
  `AdjoinRoot.mk`, `AdjoinRoot.of`, `AdjoinRoot.map`.
- The proof-only dependencies with Mathlib matches are imported privately:
  `Mathlib.RingTheory.Coprime.Basic` (`IsCoprime`,
  `IsCoprime.dvd_of_dvd_mul_left`),
  `Mathlib.Algebra.Polynomial.FieldDivision` (`Polynomial.instEuclideanDomain`),
  `Mathlib.RingTheory.PrincipalIdealDomain`
  (`EuclideanDomain.to_principal_ideal_domain`). These signatures and their
  surrounding definitions were read. No unusable dependency was found.

Edge cases checked before writing and again against the completed signature:

- R may be the zero ring; then B has no prime ideals, so no impossible factor
  is asserted. No `[Nontrivial R]` binder excludes this case.
- f = 1 makes A and B zero and likewise has no admissible prime q.
- g = 0, or g nilpotent modulo f, makes B zero; again no q exists.
- m = 0 gives denominator one; all natural exponents are quantified.
- P = 0 passes the divisibility and ideal-membership test on both sides.
- Repeated factors and positive characteristic are permitted. For example,
  f = X², g = 1 over a field selects h = X, with no separability requirement.
- For an integral R and p = 0, κ(p) is the fraction field, not incorrectly R.
- A general prime p is allowed, not only a maximal ideal of R. No coefficient
  surjectivity to κ(p), or lift of an arbitrary κ(p)-polynomial to R[t], is assumed.
- The uniqueness clause covers all candidates satisfying the original ideal
  condition, not merely those already known to satisfy the membership test.
- All variables and universes are explicitly bound. The helper target coefficient
  ring has its own universe v; no artificial universe equality is imposed.

Searches for an existing statement (all via the prescribed msearch wrapper):

- LeanFinder: “A prime ideal of a localized monic polynomial quotient is the
  contraction of the ideal generated by a unique monic irreducible polynomial
  over the residue field of its contraction”. Eight hits: universal coprime
  factor lifting, Kummer–Dedekind number-field correspondences, and a general
  spectrum/fibre identification; none states this arbitrary-ring localized
  quotient classification with both its fraction test and unique monic factor.
- Loogle: `Ideal.IsPrime, Polynomial.Monic`. Two hits: an étale factor-lifting
  theorem and irreducibility descent. Neither is this statement.
- Mathlib grep: `primesOverSpanEquivMonicFactorsMod|mem_normalizedFactors_of_isPrime`
  in RingTheory. Two hits in DedekindDomain/PID, which require Dedekind-algebra
  data and concern factors of localized ideals, not this polynomial statement.
- LeanSearch: “Prime ideals of the localization of a polynomial quotient
  correspond to monic irreducible factors over the residue field”. Eight hits:
  Kummer–Dedekind, localization prime/disjointness, and a Jacobson integrality
  result; none has the required general hypotheses and conclusion.
- Project `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the node id,
  localized-fibre/prime-factor phrases, `exists.*[Uu]nique.*[Ff]actor`,
  `prime_factor`, and `Irreducible.*ResidueField|ResidueField.*Irreducible`.
  The id appears only as a proof-plan reference in
  `Sheaf.TraceFormula.StandardEtaleFiniteFreePrimeLifts`. Related root lifting,
  generic irreducibility and other factorization statements do not classify
  this prime. No exact declaration exists.
- Full helper/main-name search in Mathlib, both project roots and
  `dag/lean_names_upstream.json`: no declaration in namespace `AdjoinRoot`
  named `localizedMap`, `localizedFactorIdeal`, or
  `exists_unique_localized_fibre_prime_factor`.

A separate final clause audit of the node and module found no statement
correction, missing conclusion or extra mathematical assumption. The initial
compiler error was only a missing explicit type on the powers-submonoid
fraction denominator; the final signature supplies that type.

Validation: the prescribed `scompile.py` compiled the file in both sandbox
and library-module contexts with no errors or warnings. The theorem proof is
exactly `sorry`; both helpers contain real data. No declaration has been proved.
There is no STATEMENT-DISPUTED issue. Independent review is performed by the
maintainer, as specified by the current dispatcher brief.

## Second reading by Q22

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
