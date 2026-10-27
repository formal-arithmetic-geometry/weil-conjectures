## Worker report

The module Sheaf.RingTheory.QuasiExcellentSemilocalDefectHeight states
QuasiExcellentSemilocal.semilocal_defect_height, with sorry, and supplies real
constructions/predicates for the notation introduced in this item's own statement.
There is one postponed theorem and no postponed construction or auxiliary theorem.
The statement, proof, and proof dependencies of the DAG node remain unchanged.
The only added statement dependency is the already landed
`def-trf-adic-ring-completion-map`, whose coordinatewise canonical map is used directly.
All helpers belong to the item's explicit notation and are listed in lean.declarations.
No new independent mathematical notion or dependency repair is needed.

Source checked: Kurano--Shimomoto, Ideal-adic completion of quasi-excellent rings
(after Gabber), https://www.isc.meiji.ac.jp/~kurano/ronbun/kurano40.pdf,
Theorem 5.1, Step 3, definition before Claim 5.4, Claim 5.4 and (5.8)--(5.11),
printed pp.12--13. The earlier definition of Delta is on printed p.11.
The source identifies the normalized and unnormalized boundary descriptions and
computes the two heights. The item's proof is the characteristic-zero specialization
of lem-per-gabber-semilocal-defect-height. That node has no Lean declaration yet,
so no proof import is available; its entire proof instruction is included in the
main theorem docstring. This is stage 2: its proof is postponed.

Hypotheses and notation, individually matched:

| Node | Lean rendering |
| --- | --- |
| Commutative Noetherian domain R over Q | R : Type u; CommRing R, IsNoetherianRing R, IsDomain R, Algebra ℚ R |
| Normal domain | IsIntegrallyClosed R in addition to IsDomain R |
| Nagata | hNagata : IsNagataRing R |
| Nonzero nonunit x | x : R, hx : x ≠ 0, hxunit : ¬ IsUnit x |
| (x)-adically complete | IsAdicComplete (Ideal.span {x}) R |
| Universally catenary, not quasi-excellent | hcat, hnotqe |
| Every quotient by a nonzero ideal is quasi-excellent | hquot quantifies all K ≠ ⊥, including K = ⊤ |
| Every finite extension of Frac R | hext quantifies F with Field, Algebra (FractionRing R) F and Module.Finite; the R-algebra and scalar tower enforce the same composite R-action |
| B_F is the integral closure | integralClosure R F, with x mapped by algebraMap |
| B_F finite over R | Module.Finite R (integralClosure R F) in hext |
| B_F normal | First clause of ExtensionConditions, all prime localizations are domains and integrally closed |
| B_F Nagata and universally catenary | Second and third clauses of ExtensionConditions |
| B_F (x)-adically complete | IsAdicComplete (Ideal.span {x}) B in ExtensionConditions |
| B_F/xB_F quasi-excellent | IsQuasiExcellent (B ⧸ Ideal.span {x}) in ExtensionConditions |
| Every maximal-ideal completion normal local domain | Last clause of ExtensionConditions: IsDomain, IsIntegrallyClosed, IsLocalRing of the maximal-ideal AdicCompletion of Localization.AtPrime n.asIdeal |
| C_(F,n) | localCompletion, principal completion of Localization.AtPrime n.asIdeal, distinct from its maximal-ideal completion |
| Minimal singular prime | IsGenericMinimalSingular: nonregular local ring at s; all prime ideals strictly below s have regular local rings |
| Contraction to zero | Last clause of IsGenericMinimalSingular, comap along algebraMap B C |
| S nonempty | hs supplies an actual chosen member (L,n,s); no separate redundant existential is needed |
| h is the least height across S | hmin compares h with every generic minimal singular prime in every finite fraction-field extension; hheight says that the chosen member attains h |
| h ≥ 2 | hge : 2 ≤ h |
| B is the chosen B_L | integralClosure R L throughout the conclusion |
| Finite γ of maximal ideals containing n | γ : Finset (MaximalSpectrum B), hn : n ∈ γ |
| S_γ | semilocalComplement: intersection of prime complements over the subtype of members of γ, exactly the complement of their union |
| B_γ, D_γ | semilocalization is Localization S_γ; semilocalCompletion is its principal AdicCompletion |
| Canonical D_γ → C_(L,n) | localizationMap uses IsLocalization.map with identity on B and inclusion S_γ ⊆ B\\n; completionMap uses the existing AdicCompletion.principalRingMap, then RingEquiv.cast for equality of the parameter images |
| s_γ | contractedPrime is PrimeSpectrum.comap of that canonical map |
| E_γ | boundaryNormalization is integralClosure (D/s) (FractionRing (D/s)); s is a bundled prime, so the quotient is a domain |
| B → E_γ | boundaryMap is the composite B → D → D/s → integral closure |
| Delta_γ(x) | boundary is the set of comaps of ideals in (Ideal.span {boundaryMap f s x}).minimalPrimes |

Every conclusion is a clause of Comparison, in node order:

1. IsNoetherianRing D_γ.
2. Normality, using the recorded inline normal-ring form at every prime.
3. IsNagataRing D_γ.
4. IsUniversallyCatenary D_γ.
5. IsGRing D_γ.
6. RingHom.Flat (algebraMap B D_γ).
7. A ring equivalence B_γ/(x) ≃+* D_γ/(x), with its value on EVERY residue
   specified to be the residue of the canonical algebra map. The equivalence is
   thus the canonical reduction isomorphism, not an unrelated isomorphism.
8. The comap of s_γ to B equals ⊥.
9. s_γ.height = h.
10. The local ring at s_γ is not regular.
11. Equality of boundary with the set of comaps of primes minimal over s_γ + (x),
    using ideal supremum for the sum and Ideal.minimalPrimes for minimality.
12. Every member q of boundary satisfies q.height = (h : ℕ∞) + 1.

Height is Mathlib Ideal.height, whose equality with the Krull dimension of the
prime localization is IsLocalization.AtPrime.ringKrullDim_eq_height. Since the
rings are Noetherian, heights of prime ideals are finite, so h : ℕ expresses
the node's attained least height without dropping a case. PrimeSpectrum is the
underlying spectrum used in the node; no scheme construction is needed here.
All finite extensions can be represented in Type u because finite-dimensional
extensions of FractionRing R have cardinality at most max |R| aleph0. Thus the
common universe covers every finite extension up to its canonical transport;
there is no smaller independent universe making the hypotheses vacuous.

Dependency declarations read and used:

- Sheaf.RingTheory.ExcellentRing: IsQuasiExcellent and IsUniversallyCatenary;
  its full chain and regular-locus definitions were read.
- WeilConjectures.RingTheory.NagataRing: IsNagataRing.
- WeilConjectures.RingTheory.GRing: IsGRing, exposed by ExcellentRing;
  the geometric regularity and completion definitions were read.
- Mathlib.RingTheory.AdicCompletion.Basic and .Algebra: AdicCompletion,
  IsAdicComplete, the ring/algebra structures and algebraMap; both types of
  completion in the node use these same definitions.
- Mathlib.RingTheory.Localization.AtPrime.Basic and Localization.Defs:
  Localization.AtPrime, Localization, IsLocalization.map.
- Mathlib.RingTheory.IntegralClosure.Algebra.Basic and .IntegrallyClosed:
  integralClosure, IsIntegrallyClosed, IsDomain. Normal rings use the
  node's inline prime-localization form, normal domains the domain conjunction.
- Mathlib.RingTheory.RingHom.Flat: RingHom.Flat.
- Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing.
- Mathlib.RingTheory.RegularLocalRing.Defs: IsRegularLocalRing, the ring
  clause of def-weil-regular-scheme's mathlib_match. Its recorded scheme module
  Sheaf.AlgebraicGeometry.IsRegularScheme was read but is unnecessary for a ring statement.
- Mathlib.RingTheory.KrullDimension.Basic and Ideal.Height: ringKrullDim,
  Ideal.height and their localization comparison. The affine-spectrum module's
  Spec and Spec.map were read; its underlying space PrimeSpectrum is used here.
- Sheaf.RingTheory.AdicRingCompletionMap: principalRingMap and its full residue-map
  construction. The added stmt_dep records this existing canonical map rather
  than copying its definition.

Edge cases checked before writing and again against the final file:
γ = {n} is allowed; γ = ∅ is excluded exactly by hn. The degree-one extension
L = FractionRing R is allowed. x = 0 and unit x are excluded explicitly. The zero
ring is excluded by IsDomain R, as in the node. The family S = ∅ is excluded by
hs, and h = 0 or h = 1 by hge. The quotient by the unit ideal is retained in hquot;
the empty prime spectrum of the zero quotient causes no ill-typed localization.
No height condition or nonemptiness assumption on Delta is added. Normal D_γ
is expressed prime-locally and does not silently strengthen normality to being
a domain. The quotient by s_γ is a domain, which justifies its fraction field.
Nonregularity and minimality apply to the x-adic local completion, not to the
maximal-ideal completion. Proof-dependent hn only supplies a canonical map
whose definition is independent of its proof by proof irrelevance.

Searches:

- msearch.py leanfinder, query "Semilocal adic completion minimal singular primes
  generic formal fibre heights normal Nagata universally catenary domain":
  eight hits, including Ideal.map_height_le_one_of_mem_minimalPrimes,
  IsLocalization.AtPrime.ringKrullDim_eq_height and standard height bounds;
  none states this semilocal formal-singularity comparison.
- msearch.py loogle, query "AdicCompletion.map, Ideal.height": zero hits.
- msearch.py grep, query "semilocal.*completion|singular.*height|defect.*height":
  zero Mathlib hits.
- rg in lean/WeilConjectures and lean/Sheaf for semilocal, singular-prime and
  defect-height names found ordinary semilocal normalization, length and
  generator results, and the citing QuasiExcellentCompletePair docstring,
  but no declaration of this statement. The exact node-id search in
  WeilConjectures and dag/lean_names_upstream.json returned no hits.
- Source searches for completionMap found the public, already recorded
  AdicCompletion.principalRingMap in AdicRingCompletionMap; it is reused.
  The private completionMap in CompletionTensorLocalMapsSurjective is not copied.
- DAG searches for minimal singular prime found this item, its arbitrary-
  characteristic twin and the minimal-formal-defect and Rotthaus statements;
  none has a recorded interface supplying the chosen data in this delivery.
  tools/blueprint_refs.py search "semilocal formal defect" returned zero matches;
  ancestor returned lem-per-artin-gabber-affine-curve. No helper duplicates a
  separate existing definition node.

Validation: scompile.py compiled both the sandbox probe and the delivered library
module cleanly, with no errors or warnings. The first two probes diagnosed
undetermined localization submonoids; explicit M and T arguments fixed them.
No statement correction, disputed statement or dependency repair is required.

## Second reading by Q47

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
