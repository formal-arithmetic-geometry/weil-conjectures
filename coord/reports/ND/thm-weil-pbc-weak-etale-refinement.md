## Worker report

The module `Sheaf.RingTheory.WeakEtaleRefinementProperties` states
`PrincipalWLocalization.WeakEtaleRefinement.properties`, with its sole proof `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.

Hypothesis and clause correspondence:

- The construction's commutative rings are `(A B : Type u) [CommRing A] [CommRing B]`.
  The arbitrary universe `u` is the common ambient universe used by the recorded
  `Algebra.IndEtale` API and the construction. There is no cardinality bound.
- The specified A-algebra B is `[Algebra A B]`; its weak etaleness is the explicit
  `(hweak : Algebra.WeaklyEtale A B)`, exactly the proof input of the recorded construction.
- The precise constructed B-prime, not an arbitrary ring or existential refinement,
  is `PrincipalWLocalization.WeakEtaleRefinement.algebra A B hweak`.
- The map B → B-prime is `algebraMap B (algebra A B hweak)`. Unfolding the bundled
  construction makes this its recorded `structuralMap A B`, namely the tensor inclusion
  followed by the retained-localization map.
- “B → B-prime is faithfully flat” is the first conjunct, that map's `.FaithfullyFlat`.
  This is Mathlib `RingHom.FaithfullyFlat`, faithful flatness for the induced module.
- “and ind-etale” is the second conjunct, that same map's `.IndEtale`, using the
  dependency's existing ring-map version of `Algebra.IndEtale`.
- “A → B-prime is ind-etale” is the third conjunct,
  `((algebraMap B (algebra A B hweak)).comp (algebraMap A B)).IndEtale`.
  Its source map is precisely the composite from the construction, without assuming
  an arbitrary algebra structure or requiring a separate tower hypothesis.

Dependency declarations read and used:

- `Sheaf.RingTheory.WeakEtaleRefinement`:
  `PrincipalWLocalization.WeakEtaleRefinement.algebra`, `structuralMap`,
  `tensorToRefinement`, `coverToTensor`, `coverStructuralMap`, `retainedAlgebra`,
  `closedIdeal`, `extendedIdeal`, `tensor`, and `coverAlgebra`.
- `Sheaf.RingTheory.IndPrincipalZariski` publicly exposes
  `Algebra.IndEtale`, `RingHom.IndEtale`, and `Algebra.WeaklyEtale`.
  Ind-etale is a filtered colimit of etale algebras; etale includes finite presentation.
  Weakly etale is flatness of the algebra and its tensor multiplication.
  Its other recorded declarations `Algebra.IsIndPrincipalZariski`,
  `AlgebraicGeometry.proAffineEtale_Spec_iff`, and
  `AlgebraicGeometry.weaklyEtale_SpecMap_algebraMap_iff` were also read.
- `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`.

Proof imports follow every stated proof dependency:
`Sheaf.RingTheory.IndEtaleStability` (`RingHom.indEtale_principalZariski_stability`),
`Sheaf.RingTheory.IndPrincipalZariskiOfLocalRingIso`
(`Algebra.isIndPrincipalZariski_of_bijective_localRingHom`),
`Sheaf.RingTheory.RetainedLocalizationProperties` (`PrincipalWLocalization.Retained.properties`),
`Sheaf.RingTheory.StrictWCoverProperties` (`PrincipalWLocalization.StrictWCover.properties`),
`Sheaf.RingTheory.WeaklyEtaleField` (`Algebra.weaklyEtale_field`),
`WeilConjectures.RingTheory.ProEtale.HenselianLocalRing`
(`Algebra.WeaklyEtale.bijective_of_isStrictlyHenselianLocalRing`),
`Mathlib.RingTheory.Flat.FaithfullyFlat.Basic` (`Module.FaithfullyFlat.instTensorProduct`),
and `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
(`Module.FaithfullyFlat.of_comap_surjective`).
The three-step docstring records the local-ring and retained-point proof from the node.
For precision, its last step spells out residue-field tensor products to prove that
T surjects onto Spec B; faithful flatness of B → D₀ alone would not establish this
for the retained subset.

Edge cases checked mathematically: neither ring is assumed nontrivial or a field;
zero rings and empty spectra are permitted. If B is the zero ring, the tensor and
retained localization are zero, B → B-prime is the zero-ring identity, and A → 0
is etale (localization at zero). If A is zero, its unital algebra B is zero too.
There is no characteristic, finite-type, locality, or noetherianity restriction.
The construction includes empty intersections and the empty retained subset.
Identity A → A is included. No additional w-locality or strict henselianity is assumed.

Searches made with `msearch.py ND thm-weil-pbc-weak-etale-refinement`:

- `leanfinder`: “A weakly etale algebra admits its canonical faithfully flat ind etale
  refinement which is ind etale over the base”: eight results, concerning ordinary
  etale ring maps, finite-presentation descent and standard smoothness; none state this
  refinement theorem.
- `loogle`: “Algebra.IndEtale, Algebra.WeaklyEtale, RingHom.FaithfullyFlat”: zero hits;
  its Mathlib index does not know Algebra.IndEtale (a project declaration).
- `grep`: “refinement|IndEtale” in RingTheory: zero Mathlib hits.
- `leansearch`: “A weakly etale algebra has a faithfully flat ind etale refinement
  ind etale over the base”: service unavailable (Internal Server Error), recorded as such.
- Direct `rg` in the upstream WeilConjectures tree and project `lean/Sheaf/RingTheory`
  for refinement names and the exact node id found only the existing construction and
  a consumer's proof comment, not a theorem for this construction. The full upstream
  weak/refinement search produced unrelated tactic lines. The upstream-name index
  has no WeakEtaleRefinement or weakEtaleRefinement entry. The exact item-id search
  in upstream has no matching theorem.

Validation: prescribed `scompile.py` passed the file and published-library check with
no errors or warnings. Every universe and variable is explicitly bound. No node fault
or STATEMENT-DISPUTED flag was found. Delivery dry run is the final check; the independent
second reader supplies their own reading and delivery.

## Second reading by ND

I independently read the item JSON, blueprint order 1232 and its construction at
order 1231, both statement-dependency nodes and their actual Lean modules, the
upstream ind-etale and Mathlib weakly-etale and faithfully-flat definitions, and
Stacks proetale.tex, Tag 097Z (with the preceding construction, Tag 097X).
The complete object/hypothesis/conclusion list and correspondence is:

- Arbitrary commutative rings A and B: `(A B : Type u) [CommRing A]
  [CommRing B]`. Pass: neither is required to be nonzero, local, noetherian,
  finite, or a field.
- Specified A-algebra B: `[Algebra A B]`. Pass: this fixes the original map
  `algebraMap A B`; no extra map or scalar tower is quantified.
- Weakly etale original map: `(hweak : Algebra.WeaklyEtale A B)`. Pass:
  Mathlib's fields are flatness over A and flatness of tensor multiplication.
  There is no extra etaleness or finite-presentation hypothesis.
- The particular refinement B-prime of the dependency construction:
  `algebra A B hweak`. Pass: I opened `closedIdeal`, `tensor`, `coverToTensor`,
  `extendedIdeal`, `retainedAlgebra`, `tensorToRefinement`, `structuralMap`,
  `coverStructuralMap`, `algebra`, and `coverAlgebra`. They use the recorded
  strict cover, the vanishing ideal of its closed points (the intersection of
  maximal ideals), B tensor A C, extension of that ideal, and its retained
  localization. Their data are explicit, not arbitrary existential choices.
- B to B-prime: `algebraMap B (algebra A B hweak)`. Pass: `algebra` installs
  precisely `structuralMap A B`, the left tensor inclusion followed by the
  canonical retained-localization map.
- Faithfully flat B to B-prime: first conjunct `.FaithfullyFlat`. Pass:
  RingHom.FaithfullyFlat is faithful flatness for this map's induced algebra.
- Ind-etale B to B-prime: second conjunct `.IndEtale`. Pass: upstream
  RingHom.IndEtale is the filtered-colimit-of-etale-algebras predicate for
  precisely that ring map; Algebra.Etale includes finite presentation.
- Ind-etale A to B-prime: third conjunct
  `((algebraMap B (algebra A B hweak)).comp (algebraMap A B)).IndEtale`.
  Pass: it is the composite through B, with no independently chosen action.
  All quantifiers precede all three conclusions, as in the node.

Source check: Tag 097Z assumes only a weakly etale ring map. It states the
existence of a refinement; this blueprint node states the properties of its
specified construction. Stacks uses an additional refinement after identifying
local rings. Here the blueprint instead invokes the already recorded
`Algebra.isIndPrincipalZariski_of_bijective_localRingHom`, whose signature I
opened: all canonical local-ring maps bijective and w-local target imply the
principal ind-Zariski presentation. Its supplied denominator-clearing and
finite clopen partition argument applies to this target. Thus the difference
from the literal Stacks proof does not add a hypothesis or require replacing
the specified B-prime. I also checked the signatures of StrictWCover.properties,
Retained.properties, the stability theorem, weaklyEtale_field, and the upstream
strict-local bijectivity theorem; the proof imports represent the node's route.
The declaration docstring includes all three proof steps and the explicit
residue-field tensor argument needed for retained-point surjectivity.

Edge cases: zero rings and empty spectra remain allowed. B = 0 gives a zero
refinement and its identity B-map, faithfully flat over the zero ring; A to 0
is etale via localization at zero. A = 0 forces B = 0. Empty maximal spectra
and empty retained sets use the dependency's empty intersection/localization;
no Nonempty instance is imposed. Identity maps are included. There is no n or
characteristic restriction. `u` is arbitrary and is the common ambient universe
of the recorded IndEtale API, its diagram and rings; no unrelated small test
universe or finite cardinal bound occurs. The construction at these parameters
has universe `max u u = u`. Every variable and universe is explicitly bound.

Independent searches (different wording from the worker): msearch leanfinder,
“Every weakly etale ring homomorphism has an ind etale faithfully flat extension
of its target”, returned eight ordinary etale/composition/descent results, no
refinement theorem. msearch loogle, `"WeaklyEtale"`, returned twelve scheme-level
weak-etale property and stability declarations, no such refinement. msearch
grep, `weakly.*etale.*refin|refin.*weakly.*etale|faithfully.*IndEtale`, returned
zero hits. Direct rg of Mathlib RingTheory, upstream WeilConjectures and project
lean/Sheaf for both word orders of faithfully/ind-etale and refinement spellings
found only the recorded construction, strict-cover properties, unrelated
contraction instances, and consumer proof comments. No exact existing statement
was found, so the module is retained. No new node or dependency module is present.

No mismatch was found; no Lean or node change was necessary. Only this second
reading was appended. The sole theorem proof is `sorry`; there are no new
hollow definitions, private notions, file-local notation, or proved helpers.
The recorded lean.statement is verbatim the declaration signature. Independent
scompile.py validation passed both the sandbox and library-path checks (1.7 s
and 1.8 s), with no errors or warnings.
