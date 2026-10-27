## Worker report

The module `Sheaf.RingTheory.CompatibleFormalIdealAdicDescent` states
`Algebra.compatible_formal_ideal_adic_descent`, with its proof `sorry`.
It introduces two helpers belonging to this statement: `Algebra.completedLocalizationMap`
names the existing, uniquely coordinate-characterized comparison, and
`Algebra.formalIdealAdicContraction` constructs the ideals a_n by actual contraction.
No mathematical statement is corrected and no independent notion is introduced.

Source read: Rotthaus, *Komplettierung semilokaler quasiausgezeichneter Ringe*,
Theorem 3, Claim 4, equations (4.1)--(4.3), pp.178--179. The source PDF was fetched
from the node's Cambridge URL into this sandbox and read with pdftotext. Claim 4
establishes the containment for a primary component, then assembles the primary
components to prove the extension/contraction equality. The node extracts this
argument for any compatible ideal E; its proof supplies the whole-fibre recovery
version. The theorem docstring carries all nine accepted proof steps and their
DAG dependencies, including the maximal-radical and empty-decomposition cases.

Hypothesis and clause correspondence:

- Commutative Noetherian semilocal B: `(B : Type u) [CommRing B]
  [IsNoetherianRing B] [Finite (MaximalSpectrum B)]`. MaximalSpectrum is precisely
  the type of maximal ideals, so finiteness is exactly semilocality, without a
  nontriviality restriction on B.
- Its Jacobson radical r: `Ideal.jacobson (⊥ : Ideal B)`. This is Mathlib's
  intersection of all maximal ideals, not the nilradical or an arbitrary ideal.
- J contained in r: `(J : Ideal B) (hJ : J ≤ Ideal.jacobson (⊥ : Ideal B))`.
- C is the actual inverse-limit completion: every occurrence is
  `AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B`, with its existing canonical
  `algebraMap B C`. There is no independent model of C or extra structure assumption.
- A prime Q of C: `Q : PrimeSpectrum C`; its ideal is `Q.asIdeal`.
  `¬ Q.asIdeal.IsMaximal` restricts to nonmaximal primes, and
  `J.map (algebraMap B C) ≤ Q.asIdeal` is Q containing JC.
- The contracted prime is `Q.comap (algebraMap B C)`; U_p is
  `Algebra.LocalCompletion (Localization.AtPrime p.asIdeal)` and T_Q is
  `Algebra.LocalCompletion (Localization.AtPrime Q.asIdeal)`. The imported abbreviation
  is exactly the maximal-ideal AdicCompletion, with no finiteness assumptions.
- The canonical alpha_Q is `completedLocalizationMap B C Q`.
  It selects the witness of the already proved `Algebra.exists_completion_map_atPrime`.
  That witness specifies the image of every completion coordinate whenever its
  source coordinate is represented by a local element. Quotient surjectivity supplies
  a representative for every coordinate and inverse-limit extensionality gives
  uniqueness, so this is the canonical map, not a freely chosen map. Its source is
  the completion of the contracted-prime localization, exactly as required.
- Faithful flatness of these maps is `hflat`, universally quantified over exactly
  the nonmaximal primes containing JC, and expressed with `RingHom.FaithfullyFlat`.
- Radicality of pC for every base prime containing J is `hradical`, using
  `(p.asIdeal.map (algebraMap B C)).IsRadical`. This is exactly the positive-power
  criterion in the node, using Mathlib's standard predicate.
- The ideal E is an unrestricted `E : Ideal C`.
- One ideal e_p for each base prime containing J is expressed by `hcompatible`:
  `∀ p : PrimeSpectrum B, J ≤ p.asIdeal → ∃ e : Ideal U_p, ∀ Q, ...`.
  Crucially the existential precedes quantification over Q. The equality
  `hp : p = Q.comap (algebraMap B C)` transports this same e to the canonical
  source type; it neither chooses another ideal nor identifies distinct completions.
- ET_Q is `E.map (algebraMap C T_Q)`; e_p T_Q is
  `Ideal.map (completedLocalizationMap B C Q) (hp ▸ e)`.
  Their equality is the final clause of `hcompatible`.
- The definition a_n is `formalIdealAdicContraction B J E n`, whose body is
  `Ideal.comap (algebraMap B C) (E ⊔ (J ^ n).map (algebraMap B C))`.
  The supremum of ideals is their sum. It is defined at all n, including zero.
- The conclusion is `∀ n : ℕ, 1 ≤ n →` the conjunction of
  `(formalIdealAdicContraction B J E n).map (algebraMap B C) =
  E ⊔ (J ^ n).map (algebraMap B C)` and
  `formalIdealAdicContraction B J E (n + 1) ⊔ J ^ n =
  formalIdealAdicContraction B J E n`.
- No J-adic completeness, nonzero-E condition or singular-locus condition is imposed.
  The original hflat and hradical assumptions are retained even though the accepted
  whole-fibre proof does not use them.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, with its complete signature
  and equivalence `isNoetherianRing_iff_ideal_fg` (lines 193--205).
- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion` (lines 167--174),
  the compatible-sequence definition. Its ring and algebra structures come from
  `Mathlib.RingTheory.AdicCompletion.Algebra`, also imported through existing modules.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`
  (lines 55--58), the localization at the prime complement.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`
  (lines 58--64); `Mathlib.RingTheory.RingHom.FaithfullyFlat`:
  `RingHom.FaithfullyFlat` (lines 23--27), the induced-module specialization.
- Added the already landed `def-trf-formal-local-presentation` to stmt_deps because
  `Sheaf.RingTheory.FormalLocalPresentation` owns the existing
  `Algebra.LocalCompletion` abbreviation (lines 27--31). Only that abbreviation
  is used; no formal presentation or coefficient-field section is assumed.
- Added the already landed `lem-weil-pbc-completion-local-map-at-prime` to stmt_deps
  because `WeilConjectures.RingTheory.CompletionAtQuasiFinitePrimeMap` supplies
  `Algebra.exists_completion_map_atPrime`. Its full signature and coordinate
  specification were read before selecting its uniquely determined witness.

Already stated proof dependencies are imported plainly: Mathlib Lasker
(`Submodule.isLasker`), completion finite quotients (`pow_smul_top_eq_ker_eval`),
faithfully flat ideal contraction (`Ideal.comap_map_eq_self_of_faithfullyFlat`),
radical-power bound (`Ideal.exists_pow_le_of_le_radical_of_fg`), local completion
locality and faithful flatness (`AdicCompletion.LocalRing`, `AsTensorProduct`,
`Module.FaithfullyFlat.of_flat_of_isLocalHom`), localization Noetherianity
(`IsLocalization.isNoetherianRing`), and
`WeilConjectures.RingTheory.AdicCompletionNoetherian` (`AdicCompletion.isNoetherianRing`).
The three newer proof nodes (flat finite intersection, flat-primary fibre recovery,
Jacobson-adic completion faithful flatness) have no recorded Lean interface on the
read base, so they are not imported or restated. They are proof inputs only.

Edge cases checked before writing:

- Zero ring: no primes/maximal ideals; `[Finite (MaximalSpectrum B)]` allows it,
  the compatibility and radicality hypotheses are vacuous, and all ideals coincide.
- J=0: every prime qualifies according to the original statement; no assumption
  or conclusion changes. For positive n the thickening is E itself.
- E=0 and E=top: both are allowed. The latter corresponds to the empty primary
  decomposition in the proof; suprema, maps and contractions preserve the unit ideal.
- Artinian semilocal B: no nonmaximal-prime tests, as in the source's maximal-primary
  case. The theorem does not mistakenly require such primes to exist.
- Base primes containing J without relevant primes above them: an ideal e_p still
  exists (e.g. top), and its test is empty, matching the original quantifier order.
- Several primes over the same p: all use the SAME existential e; the proof-equality
  transport changes only its type, and no target completions are identified.
- n=0 is excluded only in the conclusion by `1 ≤ n`, as in the node; n=1 is included.
- Universes u and v are explicit, autoImplicit is false. The main theorem uses the
  actual completion of B in its own universe, and does not impose universe equalities
  on unrelated test algebras or exclude any ring size.

Searches actually run through msearch.py for Q120 and this item:

- LeanFinder: "Compatible local ideals in completions of prime localizations descend
  to ideals in a semilocal ring". Eight hits about localization ideal detection,
  lies-over and residue fields; no exact descent statement.
- Loogle: `"AdicCompletion", "map"`. Twelve hits including transition maps,
  evaluation, algebraMap and maps of Cauchy sequences; no exact statement.
- Mathlib grep, RingTheory: `semilocal|[Ss]emi[Ll]ocal|compatible.*[Ii]deal|
  [Cc]ompletion.*[Ll]ocal.*[Mm]ap`. Eleven hits, mostly local properties of
  semilocal rings; no descent theorem.
- Mathlib grep, RingTheory: `IsSemilocal|jacobsonRadical|Jacobson`. Returned
  Jacobson-ideal tools, with the existing `Ideal.jacobson` notion used above.
- LeanSearch: "An ideal in a semilocal completion whose completed localizations are
  compatible over each base prime descends modulo powers of a Jacobson ideal".
  Eight hits, including `Ideal.jacobson`, `AdicCompletion` and radical predicates;
  none states the theorem.
- rg of `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and the upstream names index:
  searched local/completion-map names, Rotthaus, semilocality, compatible ideals and
  the exact proposed declaration names. Found and reused `LocalCompletion` and the
  existing coordinate-specified map-existence theorem. No exact descent statement,
  no collision for any of the three new declaration names.
- Exact item-ID search of `lean/WeilConjectures` returned no hit.

Validation: scompile.py compiled the sandbox and its actual library module cleanly,
13.7 s and 11.6 s respectively. Initial elaboration errors (passing a spectrum point
instead of its ideal, and breaking a field-notation token across a newline) were fixed.
The final signature has no diagnostic commands, auto-bound variables, implicit
statement-local lets, or extra hypotheses. The sole postponed theorem is the item.

## Second reading by Q120

This is the worker's final clause-by-clause self-check, not an independent review;
the dispatch brief explicitly assigns independent review to the maintainer and
forbids starting other agents. Reopened the node and final source together: checked
all four original dependency notions, semilocal finiteness, Jacobson rather than
nilradical completion, both nonmaximal-prime restrictions, faithful flatness,
radicality for every p containing J, unrestricted E, existential-before-universal
quantifier order for e_p, contraction through the canonical map, and BOTH conclusions
for every positive n. The two added dependencies are existing landed interfaces.
No statement discrepancy was found; no statement correction or disputed claim.
