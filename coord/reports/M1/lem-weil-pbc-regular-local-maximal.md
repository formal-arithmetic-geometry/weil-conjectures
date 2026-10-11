## Worker report

The module `Sheaf.RingTheory.RegularLocalMaximal` states
`RingHom.isRegular_iff_localRingHom_prime_and_maximal`, with one `sorry` and no definitions.
The node's statement is unchanged. No new nodes or dependency modules are needed.

Hypothesis and clause correspondence:
- Commutative rings R and Λ: `{R : Type u} {S : Type v} [CommRing R] [CommRing S]`.
  The universes are explicit and independent; S denotes Λ.
- The ring map φ: `(f : R →+* S)`; no algebra or local-hom hypothesis is added.
- Noetherian Λ: `[IsNoetherianRing S]`. No Noetherian assumption is made on R.
- For every target prime q, the inverse-image prime p is `q.comap f`.
  `Ideal.IsPrime.comap` supplies primality. The canonical induced map is
  `Localization.localRingHom (q.comap f) q f rfl`. Its signature is precisely
  `Localization.AtPrime (q.comap f) →+* Localization.AtPrime q`;
  `Localization.localRingHom_mk'` confirms the formula f(r)/f(s).
- Condition (1): `f.IsRegular`, using the recorded predicate from def-weil-pbc-g-ring.
- Condition (2): `∀ (q : Ideal S) [q.IsPrime],
  (Localization.localRingHom (q.comap f) q f rfl).IsRegular`.
- Condition (3): `∀ (m : Ideal S) [m.IsMaximal],
  (Localization.localRingHom (m.comap f) m f rfl).IsRegular`.
  Maximal ideals are prime; their inverse images are required only to be prime, never maximal.
- Three-way equivalence: the conjunction `(1 ↔ 2) ∧ (1 ↔ 3)` records every equivalence.

Dependency declarations read and used:
- def-weil-pbc-noetherian-ring: `Mathlib.RingTheory.Noetherian.Defs.IsNoetherianRing`
  (the actual declaration name is `IsNoetherianRing`, without a namespace), defined as
  Noetherianity of R over itself, equivalently every ideal is finitely generated.
- def-weil-pbc-localization-at-prime:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime` and
  `Localization.localRingHom` (full signature and docstring read). Also read the recorded
  clauses `Ideal.ResidueField` in `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` and
  `Ideal.Fiber` in `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`; the latter are used
  inside regularity, not independently reconstructed.
- def-weil-pbc-g-ring: `Sheaf.RingTheory.GRing`, `RingHom.IsRegular` and its constituent
  `Algebra.IsGeometricallyRegular`. Read the whole module. Regularity includes flatness
  and Noetherian geometrically regular fibres; the finite purely inseparable extensions
  use the existing universe-safe definition.
The single import of GRing supplies the dependencies transitively and is used by the statement.

Source checked: the local Stacks checkout is absent on this machine, so read the official
https://stacks.math.columbia.edu/tag/07C0 page. It states exactly the three conditions and
assumes only that Λ is Noetherian. Its proof cites 00OD and 00HT.

Edge cases checked before writing:
- Zero target ring: no prime or maximal ideals, so the local conditions are vacuous.
  The zero module is flat and zero fibres are geometrically regular (zero rings are
  Noetherian and have no primes), consistent with global regularity.
- Field target: its maximal prime contracts to an arbitrary prime of R, not necessarily
  maximal. Using comap and no source-maximal hypothesis preserves this case.
- Non-Noetherian source: allowed, exactly as in Stacks 07C0.
- Positive characteristic and characteristic zero: neither is restricted; regularity
  uses the same finite purely inseparable tests as the recorded definition.
- Arbitrary ring universes: explicit u and v exclude no ring sizes.

Searches for existing statements (2026-10-11):
- msearch.py / leanfinder: "A regular ring map with Noetherian target is regular if and
  only if its induced maps of localizations at every maximal ideal are regular".
  Eight hits: regular sequences, OfLocalizationMaximal, regular elements, and injectivity
  locality. No matching regular-ring-map equivalence.
- msearch.py / loogle: "RingHom.Flat, Localization.localRingHom".
  One hit, `RingHom.Flat.localRingHom`, supplies only the flatness implication.
- msearch.py / grep: "IsRegular|regular.*local" in RingTheory/RingHom.
  No hits. The remote search results are in searches.jsonl.
- rg of WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json:
  "lem-weil-pbc-regular-local-maximal|IsRegular.*iff|isRegular.*local|regular.*localization".
  Found uses in GRingCompletionRegular and related regular-ring and regular-sequence
  lemmas, but no declaration of the node. `RingHom.IsRegular` exists in GRing and is reused.
- rg for "IsPrime.*comap|isPrime_comap" in Mathlib/RingTheory/Ideal confirms the comap
  prime instance. Read localRingHom's fraction formula directly in the Mathlib source.

Node proof fault (no statement fault): step 3 says the prime-local condition implies the
maximal-local condition "by localizing once more from a prime ... to a maximal ideal".
The first implication is simply specialization to maximal primes. For the converse, choose
q ⊆ m and localize S_m further to S_q, not in the opposite direction. The docstring states
these directions correctly while retaining the recorded proof route and dependencies.
No STATEMENT-DISPUTED marker is warranted; the statement agrees with Stacks 07C0.

Validation: scompile.py compiled the module on the server in 1.7 seconds, exit code 0,
with no warnings. All variables and universes are explicitly bound.

## Second reading by M1

Independent reading on 2026-10-11. Opened the sandbox node and module, all three
statement-dependency nodes and their actual declarations. The local Stacks .tex
checkout is absent. Read the official more-algebra.tex source instead:
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex,
section-regular, definition-regular, lemma-regular-local (current lines 9532–9577),
and https://stacks.math.columbia.edu/tag/07C0. The surrounding section introduces
geometric regularity by finite purely inseparable extensions, defines regular maps
as flat with Noetherian geometrically regular fibres, and observes that a
Noetherian target already makes the fibres Noetherian. It imposes no additional
hypothesis on the source ring.

Object, hypothesis and conclusion checklist (all PASS):
1. Two commutative rings R and Λ: `{R : Type u} {S : Type v}` with
   `[CommRing R] [CommRing S]`; S is Λ, and independent universes cover both sizes.
2. Ring map φ: `(f : R →+* S)`. No injectivity, finite presentation, localness,
   source Noetherianity, or preselected algebra structure is assumed.
3. Noetherian target Λ: `[IsNoetherianRing S]`. Read its abbreviation in
   Mathlib.RingTheory.Noetherian.Defs and `isNoetherianRing_iff_ideal_fg`:
   this is exactly finite generation of every ideal.
4. Target prime q and contracted prime p: `∀ (q : Ideal S) [q.IsPrime]`
   and `q.comap f`. The source prime is determined by contraction, as in the
   node; primality is supplied by Mathlib, without a new hypothesis.
5. Induced fraction map R_p → Λ_q: `Localization.localRingHom (q.comap f) q f rfl`.
   Opened Mathlib.RingTheory.Localization.AtPrime.Basic, the signature of
   `localRingHom`, its definition using `IsLocalization.map`, and `localRingHom_mk'`:
   its domain/codomain are exactly these prime localizations and it sends r/s
   to f(r)/f(s). This uses the recorded localization, rather than a private copy.
6. Condition (1), φ regular: `f.IsRegular`. Read Sheaf.RingTheory.GRing in full:
   `RingHom.IsRegular` installs precisely `f.toAlgebra`, requires `f.Flat`, and
   tests `Algebra.IsGeometricallyRegular p.ResidueField (p.Fiber S)` at every
   source prime. The latter includes Noetherianity and regularity after every
   finite purely inseparable extension. Opened the recorded residue field and
   fibre definitions: `Ideal.ResidueField` is the local residue field, and
   `Ideal.Fiber` is κ(p) ⊗[R] S, canonically the node's opposite tensor order.
7. Condition (2), every prime-local map regular: first right-hand side
   `∀ (q : Ideal S) [q.IsPrime],
   (Localization.localRingHom (q.comap f) q f rfl).IsRegular`.
   Exactly the same map and regularity predicate; no clause is missing.
8. Condition (3), every maximal-local map regular: second right-hand side
   `∀ (m : Ideal S) [m.IsMaximal],
   (Localization.localRingHom (m.comap f) m f rfl).IsRegular`.
   Only m in the target is maximal; its contraction is merely prime. This
   preserves the source distinction explicitly made in the node and Stacks.
9. Three equivalent conditions: `(1 ↔ 2) ∧ (1 ↔ 3)` states precisely their
   mutual equivalence. The ring map is bound before both ideal quantifiers.

Edge cases: a zero target has no primes or maximal ideals, so both local tests
are vacuous; its global map is flat with zero, regular fibres. A zero source can
map unitally only to a zero target, also covered. No nontrivial-ring instance was
added. A field target may have its zero maximal ideal contract to a nonmaximal
source prime; comap correctly covers that case. Non-Noetherian sources are
allowed. Characteristic zero and positive characteristic are both unrestricted.
There are no index sets, schemes or integer dimension parameters in this node,
so empty schemes and n = 0 introduce no extra cases. The geometric-regularity
extension universe is `max u v` for its actual field and algebra; it contains the
base field and permits representatives of every finite extension, so the tests
are not vacuous because of ring size. No unbound variables or universes occur.

Independent searches, using different wording from the first reader:
- msearch.py leanfinder: "Flat homomorphism with geometrically regular fibres can
  be checked at all target maximal ideals". Eight hits, including
  `RingHom.Flat.propertyIsLocal`, `RingHom.Flat.localRingHom`,
  `RingHom.Flat.ofLocalizationPrime`, `Module.flat_of_localized_maximal`, and
  smooth-flat/regular-sequence lemmas. These state flatness or another notion,
  not regular-map locality.
- msearch.py loogle: "RingHom.Flat, Ideal.IsMaximal". No hits.
- msearch.py grep: "geometrically.*regular|isRegular_iff_localRingHom". No hits.
- Direct rg on the source WeilConjectures/RingTheory, repository lean/Sheaf/RingTheory
  and Mathlib/RingTheory/RingHom for `IsRegular`, `geometrically.?regular`, and
  `regular.*local`, followed by a theorem/lemma declaration search across the
  entire source WeilConjectures and project RingTheory. Found the shared GRing
  definitions and completion/ascent applications; no existing declaration of
  this equivalence. Regular sequences and regular elements are different notions.
  The statement therefore needs this module; existing definitions are reused.

No Lean/node statement mismatch found; no signature or module changes needed.
No new definition nodes or dependency modules are in this delivery or needed.
The node has no stage-2 statement correction. Its proof step 3 incorrectly says
prime-to-maximal localization for the forward implication; specialization to
maximal primes suffices, and further localization goes from S_m to S_q for q ⊆ m.
The worker already gives those directions correctly in the declaration docstring,
so retained that text and recorded this proof-only fault here, without changing
the node's protected proof fields. Its three numbered proof steps otherwise cover
the node's flatness, fibre regularity and maximal-local arguments and cite the
recorded proof dependencies. Module/declaration docstrings have the source and
blueprint id. The only theorem remains `by sorry`; there are no definitions or
proofs introduced here, no hollow data, and only one used import.

Changes in the second reading: appended this independent review only. Verified
that the node's lean.statement is verbatim the whitespace-normalized signature,
all module lines have at most 100 characters, and compilation via scompile.py
with the absolute sandbox module path exits 0 in 1.7 seconds, without warnings.
The first compile invocation used a relative path from the read-only repository
and failed before invoking Lean; the absolute-path invocation corrected that.
