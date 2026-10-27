## Worker report

The module `Sheaf.RingTheory.QeMinimalFormalDefect` states
`exists_qe_minimal_formal_defect`, with exactly one postponed theorem proof (`sorry`).
The helper `qeFormalCompletion` is a transparent abbreviation for the actual Mathlib
principal-adic completion of a prime localization. The helper
`qeGenericMinimalSingularPrimes` is the indexed piece of the set S explicitly
introduced by this node, with real predicate data and no choice or postponed proof.
These are owning-node helpers, not independent replacement notions or new DAG nodes.
Only the item's `lean` record changes; its accepted statement and proof split remain intact.

Hypotheses, in node order:

- A commutative Noetherian normal domain R over Q is `(R : Type u) [CommRing R]
  [IsDomain R] [Algebra ℚ R] [IsNoetherianRing R] [IsIntegrallyClosed R]`.
  This is exactly the recorded normal-domain form. The Q-algebra structure supplies
  characteristic zero and the specified rational structure.
- Nagata is `hNagata : IsNagataRing R`.
- The chosen element and its two restrictions are `(x : R)`, `hx : x ≠ 0`,
  and `hxunit : ¬ IsUnit x`.
- Principal-adic completeness is
  `hcomplete : IsAdicComplete (Ideal.span {x}) R`.
- Universal catenarity is `hcatenary : IsUniversallyCatenary R`.
- Failure of quasi-excellence is `hnotqe : ¬ IsQuasiExcellent R`.
- Every nonzero-ideal quotient is exactly
  `hquot : ∀ K : Ideal R, K ≠ ⊥ → IsQuasiExcellent (R ⧸ K)`.
  K is not required to be prime or proper.
- Each finite field extension is quantified as `(L : Type u) [Field L]
  [Algebra R L] [Algebra (FractionRing R) L]
  [IsScalarTower R (FractionRing R) L] [Module.Finite (FractionRing R) L]`.
  The R-algebra structure and scalar tower express restriction of the field-extension
  structure along R → Frac R. They are compatible structures, not a separate constraint
  on the extensions. Using the ring's universe, rather than an unrelated possibly
  smaller universe, includes every finite extension up to R-algebra isomorphism.
- B_L is the actual `integralClosure R L` throughout. It is never a variable ring
  equipped with an arbitrary map or a chosen ring from an existential theorem.
- Its finiteness is `Module.Finite R (integralClosure R L)`.
- Its normality is the recorded inline normal-ring form: for every prime p of B_L,
  `IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`.
- Nagata and universal catenarity of B_L are respectively `IsNagataRing` and
  `IsUniversallyCatenary` applied to that same integral closure.
- Its completeness uses `Ideal.span {algebraMap R (integralClosure R L) x}`.
- The quasi-excellent closed fibre is `IsQuasiExcellent` of the quotient by this
  same principal ideal, not the quotient by a maximal ideal.
- Every maximal n is `(n : Ideal (integralClosure R L)) [n.IsMaximal]`.
  Its maximal-adic completion is
  `AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime n))
    (Localization.AtPrime n)`.
  `IsLocalRing`, `IsDomain`, and `IsIntegrallyClosed` of this very ring are the
  three conjuncts saying it is a normal local domain. They are hypotheses,
  not inferred from quasi-excellence or substituted by regularity.

Objects and conclusions, clause by clause:

- `qeFormalCompletion B x n` is
  `AdicCompletion (Ideal.span {algebraMap B (Localization.AtPrime n) x})
    (Localization.AtPrime n)`. Thus the node's C is the x-adic completion,
  distinct from the maximal-adic completion in the hypothesis.
- Sing(T) is written inline as
  `{s : PrimeSpectrum T | ¬ IsRegularLocalRing (Localization.AtPrime s.asIdeal)}`.
  This uses the ring clause of `def-weil-regular-scheme` through its Mathlib match.
- Minimal singularity is Mathlib's `Minimal` applied to that exact predicate.
  In the inclusion order on `PrimeSpectrum`, it says the prime is singular
  and any singular prime below it is equal to it. It is not minimal among
  only the primes over zero.
- Contraction to B, not just R, is the equality to bottom of `Ideal.comap`
  under the composite of the canonical B → B_n and B_n → C ring maps.
  This is the second conjunct of `qeGenericMinimalSingularPrimes` membership.
- The first main conjunct quantifies every finite L and every maximal n,
  and asserts `IsNoetherianRing C ∧ IsLocalRing C ∧` the inline normal-ring
  condition `∧ IsGRing C ∧ IsClosed` of exactly the singular set above.
- The second main conjunct chooses one `h : ℕ` with `2 ≤ h`.
- Its first subsidiary conjunct exhibits L, all compatible extension structures,
  maximal n, and s in the indexed piece of S, with
  `ringKrullDim (Localization.AtPrime s.asIdeal) = (h : WithBot ℕ∞)`.
  This states both nonemptiness of S and attainment of h.
- Its next conjunct ranges over every such L, n and s and gives
  `(h : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime s.asIdeal)`.
  Together these are exactly the least-height assertion. No preselected
  extension or maximal ideal is imposed on the minimizing triple.
- Its third conjunct ranges over every `p : PrimeSpectrum R` and gives
  `IsExcellent (Localization.AtPrime p.asIdeal)` when its dimension is ≤ h.
- Its fourth conjunct ranges over every finite L and every
  `q : PrimeSpectrum (integralClosure R L)` and gives the analogous excellence
  assertion at dimension ≤ the same h.
- All heights are literally `ringKrullDim (Localization.AtPrime ...)`, in
  `WithBot ℕ∞`, as the node defines them. There is no truncation to a natural
  number which could turn infinite dimension into zero.

Dependency declarations read and used:

- `Sheaf.RingTheory.ExcellentRing`: `IsQuasiExcellent`, `IsUniversallyCatenary`,
  `IsExcellent` (and the prime-chain definitions they use).
- `WeilConjectures.RingTheory.GRing`: `IsGRing`, using its published regular-map
  and geometrically-regular-fibre definitions. This statement dependency is public.
- `WeilConjectures.RingTheory.NagataRing`: `IsNagataRing`.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`.
- `Mathlib.RingTheory.AdicCompletion.Basic` / `.Algebra`: `AdicCompletion`,
  `IsAdicComplete`, and the canonical completion algebra map.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`
  and its canonical algebra map.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`.
- `Mathlib.RingTheory.Spectrum.Prime.Topology`: the Zariski topology on
  `PrimeSpectrum`, underlying the recorded affine spectrum.
- Mathlib `Minimal` was checked at `Order/Defs/Unbundled.lean:279`.

The scheme-only predicate `AlgebraicGeometry.IsRegularScheme` is not applicable to
this ring statement; the same dependency node explicitly records the ring notions
in `mathlib_match`, which are used directly. Likewise the affine spectrum is used
through its prime-spectrum underlying space, with the standard Zariski topology.
There is no reason to construct an auxiliary scheme or copy either notion.
All available project proof-dependency modules are imported privately, and the
Mathlib proof-dependency source modules are imported privately too. The four proof
nodes `lem-per-g-ring-quasi-excellent-closed-fibre`, `lem-per-local-g-ring-adic-lifting`,
`lem-per-quasi-excellent-localization`, and `lem-per-semilocal-g-ring-j2` currently
have no recorded declarations to import. They occur in the complete fourteen-step
natural-language proof docstring, which retains every accepted proof step and its
cited dependency ids. They are not needed to elaborate this statement.

Edge cases checked before and after writing:

- The trivial finite extension L = Frac R is included; the finite-module binder
  does not require degree > 1.
- Prime p = 0 and q = 0 are included in both excellence conclusions; there is
  no positivity hypothesis on their height.
- K = top is permitted in hquot, as it is a nonzero ideal of this domain.
  K = bottom alone is excluded.
- x = 0 and invertible x are excluded exactly as the node requires. No further
  assumption such as primality of (x) is inserted.
- An empty singular locus is allowed for individual C. S is asserted nonempty
  across all pairs, not for each pair.
- The least height is attained, and is positive in the stronger specified sense
  h ≥ 2; a mere lower bound or an unattained infimum would be insufficient.
- Normality uses all prime localizations, not only maximal localizations.
- The finite extensions and test algebras live in the ring's universe; no
  artificially smaller independent universe can make a universal hypothesis vacuous.

Searches actually run using the prescribed `msearch.py Q129
lem-per-qe-minimal-formal-defect` wrapper:

- leanfinder: `least height of a generic minimal singular prime in ideal adic
  completions controls excellence of low height localizations` — eight results
  about Krull height, principal ideals, regular localizations, or smooth loci;
  none states this quasi-excellence result.
- loogle: `IsRegularLocalRing, AdicCompletion, IsExcellent` — zero hits; the
  service explicitly reports unknown identifier `IsExcellent`, a project
  definition rather than a Mathlib declaration. This is not a proof of absence.
- grep in Mathlib RingTheory:
  `minimalFormalDefect|formalDefect|quasi.?excellent` — zero hits.
- leansearch: `A least generic formal singular height bounds excellence of low
  height localizations of an adically complete normal Nagata domain` — eight
  hits about ordinary height or adic valuations; none gives this statement.
- Direct rg in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for the three proposed full declaration names
  returned no existing declaration. Direct rg for formalDefect/minimal singular
  primes found no existing ring construction or theorem. The broader singular
  locus search found formal-scheme and Bertini constructions, whose objects
  and meanings differ. The required grep for this node id in WeilConjectures
  returned no match.

Source read: the PDF at https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf,
Theorem 5.1 Step 2, definition of S_L and (5.1)–(5.6), Claim 5.2, pp. 9–11,
and the finite-extension discussion on p. 13. The finite extensions and their
minimal singular primes agree with that source; this node is the accepted
characteristic-zero specialization with its auxiliary hypotheses explicit.
Bibliographic integration remains requested as recorded by stage 1; no shared
literature files were edited.

No statement correction, disputed statement, new node, or dependency repair is needed.
The scompile.py server wrapper compiled this module as both sandbox and library
module in 2.6 seconds each, with no errors or warnings. The final public-import
adjustment is checked again by the required delivery dry run.

## Second reading by Q129

This dispatcher assignment has one worker and expressly prohibits starting other
agents. This is an explicit self-check, not a claim of an independent worker review;
the maintainer supplies the independent review of the delivery.

Reopened the node, the Lean module, and each dependency's recorded notion. Checked
that the normal-ring conjuncts quantify all primes; that both completions use their
correct ideals; that `Minimal` imposes minimality in the entire singular locus;
and that comap contracts all the way to B_L. Verified all eight assumptions about
B_L, including normality of its maximal-adic completions. Matched every conclusion
against the node, especially attainment plus the universal least-height inequality,
and both excellence conclusions with the same h. No mathematical mismatch was found.
Changed the explicit GRing import to `public import`, because it is also a statement
dependency, and corrected the module prose to call the definition and abbreviation
“helpers.” No statement or proof-split fields changed.
