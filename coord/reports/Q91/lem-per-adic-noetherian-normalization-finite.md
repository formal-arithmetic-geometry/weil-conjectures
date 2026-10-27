## Worker report

The module `Sheaf.RingTheory.AdicNoetherianNormalizationFinite` states
`integralClosure.finite_of_noetherian_of_adicComplete`. Its only theorem has
proof `sorry`; no definition, axiom, helper theorem, or other DAG node is added.
The node changes only in `lean`. Its accepted statement and proof are unchanged.

Hypotheses and clauses, checked against the node:

- A commutative Noetherian integral domain R is `(R : Type u) [CommRing R]
  [IsDomain R] [IsNoetherianRing R]`.
- Its fraction field K is `(K : Type v) [Field K] [Algebra R K]
  [IsFractionRing R K]`. The localization condition is the actual fraction-field
  condition, not an arbitrary embedding in a field.
- A proper ideal J is `(J : Ideal R) (_hJ : J ≠ ⊤)`.
- J-adic completeness of R is `[IsAdicComplete J R]`, including Hausdorffness.
- The Nagata closed fibre is `(_hNagata : IsNagataRing (R ⧸ J))`.
  This is the recorded predicate, Noetherian plus Japanese prime quotients.
- The finite field extension L/K is `(L : Type w) [Field L] [Algebra K L]
  [FiniteDimensional K L]`. The additional interface binders `[Algebra R L]
  `[IsScalarTower R K L]` express the composite R → K → L already meant by
  integral closure in that extension; they add no mathematical restriction.
- T is exactly the canonical `integralClosure R L`, with its inherited R-module
  and ring structures. Its assumed Noetherianity is
  `[IsNoetherianRing (integralClosure R L)]`, not the much stronger assumption
  `IsNoetherian R (integralClosure R L)`.
- The sole conclusion is `Module.Finite R (integralClosure R L)`.
- There is no normality, separability, locality, or completeness-of-T binder.
  The explicit universes `u v w` are independent, so differently sized fraction
  and extension fields are included. All variables and universes are bound.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing` and its ideal-finiteness
  equivalence, for def-weil-pbc-noetherian-ring.
- `Mathlib.RingTheory.AdicCompletion.Basic`: `IsAdicComplete` (extends
  `IsHausdorff` and `IsPrecomplete`), for def-weil-pbc-adically-complete-ring.
- `WeilConjectures.RingTheory.NagataRing`: `IsNagataRing`, whose definition is
  `IsNoetherianRing R ∧ ∀ p [p.IsPrime], IsN2 (R ⧸ p) (FractionRing (R ⧸ p))`,
  for def-weil-pbc-nagata-ring. Also read its JapaneseDomain import and IsN2.
- `Mathlib.Algebra.Algebra.Defs`: `Algebra`, for def-pc-field-extension.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, the
  subalgebra with carrier `{r | IsIntegral R r}`, for def-weil-pbc-integral-closure.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`, finite generation of
  the top submodule, for def-weil-finitely-generated-module.
- Fraction field and finite extension interfaces use `IsFractionRing` from
  `Mathlib.RingTheory.Localization.FractionRing` and `FiniteDimensional` from
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`.

All available recorded proof dependencies are imported: the relevant Mathlib
modules for Jacobson ascent, Krull intersection, radical powers, minimal primes,
Noetherian submodules and quotients, and radical/zero-locus correspondence;
`WeilConjectures.RingTheory.FiniteOverCompleteRing` supplies
`Module.finite_and_span_eq_top_of_adicComplete`. The one unstated proof dependency
`lem-per-normalization-japanese-prime-quotient-finite` has neither a lean record
nor a mathlib_match and hence has no module to import. It is not needed to type
this statement. The seven-step docstring records every proof dependency and the
full argument, including separation, finite minimal primes, diagonal embedding,
monomial induction, radical power, and the final finite-module criterion.

Source check: downloaded the cited Numdam PDF into this sandbox's scratchpad
and read its text using pdftotext. Marot (1975), printed p.104 states the standing
Noetherian domain / finite fraction-field extension convention. Proposition 2.1,
p.106 uses a proper ideal, completeness, and universally Japanese quotient, with
finite generation of the radical and finiteness of minimal primes as its two
conditions. Noetherianity of T supplies both. Nagata quotient implies universally
Japanese (Stacks 0334), and its prime-quotient Japanese condition is precisely
what step 3 uses. No statement correction or dispute is needed.

Edge cases checked before writing: J = 0 is retained (completion is discrete);
J = ⊤ is excluded exactly as in the node. A field R and J = 0 are permitted.
L = K is permitted, and inseparable finite extensions in positive characteristic
are permitted. The zero ring is excluded by IsDomain, exactly as requested.
R need not be local or integrally closed. Empty radical generating families in
the r = 0 case are covered by the proof description. There is no unintroduced
arbitrary T or extra choice of embedding.

Searches for an existing exact statement (2026-10-24):

- msearch.py leanfinder: "A Noetherian integral closure in a finite field extension
  is finite over a J-adically complete Noetherian domain whose quotient by J is
  Nagata"; 8 hits, principally IsIntegralClosure.finite / isNoetherian and normal
  closure results. Read DedekindDomain/IntegralClosure.lean: the closest theorem
  assumes IsIntegrallyClosed A and Algebra.IsSeparable K L, so is not this node.
- msearch.py loogle: "IsAdicComplete, integralClosure, Module.Finite"; 0 hits.
- msearch.py grep: "integralClosure|normalization", RingTheory; 25 hits, none the
  requested complete-pair criterion.
- msearch.py leansearch: "Noetherian integral closure finite module over adically
  complete domain with Nagata quotient"; 8 hits, again the stronger-hypothesis
  DedekindDomain theorem and unrelated integrality results; no exact match.
- rg in lean/WeilConjectures and lean/Sheaf for IsNagataRing, IsAdicComplete,
  integralClosure, and Noetherian normalization; inspected NagataRing,
  NagataRingIntegralClosure, NagataOfCompleteLocal, FiniteOverCompleteRing,
  and the Tate principal-ideal interface. Those give definitions, consequences
  of an already Nagata base, complete-local results, or normal principal cases.
  None states this general complete-pair criterion.
- grep -rn for the item's id in lean/WeilConjectures returned no hit. Searches of
  dag/lean_names_upstream.json and both Lean trees found no proposed full name
  `integralClosure.finite_of_noetherian_of_adicComplete`.

Validation: scompile.py compiled this file in sandbox and library module modes
on the server with no errors or warnings (1.2 s and 1.1 s respectively).

## Second reading by Q91

Final direct rereading of the node and generated file checked the complete
hypothesis-to-binder list above and the conclusion. In particular the hypothesis
is Noetherianity as a ring of T, the conclusion is finite generation as an
R-module, and the field extension need not be separable. The scalar tower forces
the integral closure to use the specified composite inclusion. J remains proper
and completeness includes separation. No mismatch was found and no node
correction was made. This is the worker's final self-check; the maintainer's
independent review is separate, as required by the dispatcher brief.
