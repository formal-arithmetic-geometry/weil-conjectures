## Worker report

The module Sheaf.AlgebraicGeometry.EtaleLocalizeUpstairs states
AlgebraicGeometry.exists_etale_localization_of_prime_mem, with only `sorry` as proof.
No new nodes, dependency modules, or statement correction are needed.

Clause correspondence:
- Commutative rings A and B: `{A B : Type u} [CommRing A] [CommRing B]`.
  The universe u is arbitrary, with no countability or nontriviality restriction.
- Ring homomorphism A → B: `(φ : A →+* B)`.
- Ideal of B: `(𝔟 : Ideal B)`.
- Every prime containing the ideal: `∀ (𝔮 : PrimeSpectrum B), 𝔟 ≤ 𝔮.asIdeal → ...`.
  PrimeSpectrum bundles exactly a prime ideal, not only closed or maximal points.
- A principal neighborhood outside that prime: `∃ s : B, s ∉ 𝔮.asIdeal ∧ ...`.
- The induced Spec B_s → Spec A is étale: `Etale (Spec.map (CommRingCat.ofHom
  ((algebraMap B (Localization.Away s)).comp φ)))`. The ring map is exactly
  A → B → B_s; Spec.map is contravariant. No algebra instance on B over A is required.
- Existence of g in B: `∃ g : B, ...`.
- Its quotient image is a unit: `IsUnit (Ideal.Quotient.mk 𝔟 g)`.
  This does not strengthen the conclusion to equality with 1.
- Étaleness of the same induced morphism for g: the identical expression with g.

Dependency: def-weil-etale-morphism is a Mathlib leaf, recorded as
AlgebraicGeometry.Etale in Mathlib.AlgebraicGeometry.Morphisms.Etale.
Its full class signature and docstring were read: the maps of rings of sections
on affine opens are étale. The dependency's recorded equivalence identifies this
with the source's locally finitely presented, flat, unramified morphisms.
Mathlib.Localization.Away, algebraMap, PrimeSpectrum.asIdeal, and
Ideal.Quotient.mk supply the remaining standard ring-theoretic notions.

Source checked directly at https://stacks.math.columbia.edu/tag/07M0 because
literature/stacks-project/more-algebra.tex is absent on this machine. The lemma
allows arbitrary rings and ideals, and says exactly that g is invertible modulo
J and B_g is étale over A. The module docstring carries all five DAG proof steps,
including the empty-cover case and the named proof dependencies.

Edge cases checked: 𝔟 = ⊤ gives an empty hypothesis; g = 0 is permitted, and
its image in the zero quotient is a unit, with B_0 the zero ring and empty
spectrum. Zero A or B is allowed. 𝔟 = ⊥ requires the neighborhood condition
at all primes and concludes a unit in B. No finite-presentation hypothesis is
added to B, and no assumption that the quotient or the rings are nonzero appears.
The fixed universe can encompass any two ring universes by choosing their maximum.

Searches (2026-10-11):
- msearch.py leansearch, “etale localization unit modulo ideal”: service unavailable
  (Internal Server Error), recorded without a match verdict.
- msearch.py leanfinder, “etale near every prime containing an ideal implies exists
  principal localization etale and unit modulo ideal”: 8 hits, including
  Algebra.exists_etale_of_isEtaleAt, Algebra.basicOpen_subset_etaleLocus_iff_etale,
  RingHom.Etale.ofLocalizationSpanTarget. They are ingredients only; the first two
  require finite presentation and the last is a local-cover criterion, not this theorem.
- msearch.py loogle, “Algebra.Etale, Ideal.Quotient.mk”: 0 hits.
- msearch.py grep, “07M0|localize.upstairs|zeroLocus.*etaleLocus|etaleLocus.*zeroLocus”:
  0 Mathlib hits.
- rg in WeilConjectures and lean/Sheaf for the tag, localization-upstairs name,
  and exists_etale_localization_of_prime_mem: no identical statement or name.
- rg for the item id in WeilConjectures: no hit. The same declaration-name/tag
  search in dag/lean_names_upstream.json has no hit.
- Read Mathlib Etale/Locus candidates from their returned signatures: they do not
  match the arbitrary-ring neighborhood hypothesis. No duplicate definition is made.

Validation: single-file server compilation passes cleanly. Independent second
reading is left to the dispatcher-appointed second worker; no delivery was pushed.

## Second reading by C1

Independent reading of the node, its entire module, its sole statement dependency,
and the Stacks source. No mathematical or Lean mismatch was found; the statement,
node record, and proof-plan docstring are retained. This reading adds only this
report section.

Source checked: the raw Stacks `more-algebra.tex`, label
`lemma-localize-upstairs` (Tag 07M0), and the introduction to
`section-lifting`, which adds no standing finiteness, field, or Noetherian
hypothesis. The local literature checkout lacks the .tex, so I read
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex
and https://stacks.math.columbia.edu/tag/07M0. Definition 00U1 at
https://stacks.math.columbia.edu/tag/00U1 defines etale at a prime by an
etale principal localization outside that prime, precisely the node's hypothesis.

Object/hypothesis/conclusion inventory and verdicts (H3):
1. Arbitrary commutative rings A, B: `{A B : Type u} [CommRing A]
   [CommRing B]`. Correct; no field, nontriviality, or finiteness assumptions.
2. The given ring map A to B: `(φ : A →+* B)`. Correct; neither injectivity
   nor a separately chosen algebra structure is required.
3. An arbitrary ideal of B: `(𝔟 : Ideal B)`. Correct, including top and bottom.
4. Each prime of B containing that ideal: `∀ (𝔮 : PrimeSpectrum B),
   𝔟 ≤ 𝔮.asIdeal → ...`. Correct; PrimeSpectrum bundles all prime ideals,
   with no maximality restriction.
5. For each such prime, an element outside it: `∃ s : B,
   s ∉ 𝔮.asIdeal ∧ ...`. Correct quantifier order: s may depend on the prime.
6. Its induced principal localization is etale over A:
   `Etale (Spec.map (CommRingCat.ofHom
   ((algebraMap B (Localization.Away s)).comp φ)))`. Correct: the canonical
   map B to B_s composes with the GIVEN map φ, and Spec reverses direction.
7. One element g in B after the entire neighborhood hypothesis: `∃ g : B`.
   Correct; no dependence on a selected prime remains.
8. Its quotient image is invertible: `IsUnit (Ideal.Quotient.mk 𝔟 g)`.
   Correct, without strengthening the conclusion to congruence with 1.
9. Etaleness of Spec B_g to Spec A: the same expression in item 6 with g.
   Correct, in conjunction with item 8 for the same witness g.

Dependency review (H4/H13): opened
`dag/nodes/sec-nagata-compactification/def-weil-etale-morphism.json`, then
`Mathlib/AlgebraicGeometry/Morphisms/Etale.lean`. The recorded class
`Etale {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop` requires etale maps on affine
sections; `Etale.iff_flat_and_formallyUnramified` explicitly identifies it with
flatness, formal unramifiedness, and local finite presentation. This is the
node's scheme notion, with the diagonal characterization recorded in the
leaf. The module imports this dependency directly. No new definition node,
private notion, unusable dependency, or dependency module is present or needed.
There is no statement_change in this delivery.

Edge cases: for 𝔟 = top the premise is vacuous, and g = 0 is allowed;
B_0 has empty spectrum, and the zero quotient admits a unit. For 𝔟 = bottom
all primes are tested and the conclusion asks for a unit in B. Zero rings and
empty spectra are admitted; no Nontrivial instance is present. Characteristic
is unrestricted. No index set or integer n occurs in the statement. The proof
plan explicitly handles the empty finite sum/cover (n = 0). Universe u is
explicit and arbitrary: scheme morphisms use Mathlib's common ambient universe,
which may be taken to contain both rings (cumulativity); no size bound is added.
All objects, variables, and the universe are explicitly bound.

Independent searches on 2026-10-11, using queries different from the worker's:
- LeanSearch via msearch: “If etale principal opens cover the vanishing set
  of an ideal, there is an etale localization at an element invertible in the
  quotient ring”. Service unavailable (Internal Server Error); no match verdict
  is claimed for this service.
- LeanFinder via msearch: “An ideal J of a ring B admits g invertible in B/J
  with B localized at g etale over A if the etale principal opens cover V(J)”.
  Eight results: etaleLocus/basicOpen lemmas, exists_etale_of_isEtaleAt,
  RingHom.Etale.ofLocalizationSpan/ofLocalizationSpanTarget, and
  Algebra.Etale.of_isLocalizationAway. I opened Etale/Locus.lean: the actual
  etale-neighborhood existence result assumes FinitePresentation R A and
  discusses one prime, not a closed subset. The local-cover results have no
  quotient-unit conclusion. These are ingredients, not this statement.
- Loogle via msearch: `IsUnit, Ideal.Quotient.mk, Localization.Away`:
  zero hits.
- Independent rg searches over all Mathlib, WeilConjectures, lean/Sheaf,
  and dag/lean_names_upstream.json: `07M0|localize.upstairs|
  exists_etale_localization_of_prime_mem|[Ee]tale.*[Qq]uotient|
  [Qq]uotient.*[Ee]tale`, plus searches for invertibility modulo an ideal.
  No identical statement/name/tag found. Hits concerned standard-etale
  quotient presentations or etale torsor quotients, not this lemma.

H5/H6/H8/H9: no definitions, hence no hollow data; exactly one theorem with
proof `by sorry`, nothing proved. Module and declaration docstrings name the
source and blueprint id. The five numbered proof steps match all five DAG
steps, including the dependencies for zero loci, basic opens, localization open
immersions, etale composition, and source locality. Both imports are used.
Namespace, copyright header, 100-character line width, and explicit bindings
meet the conventions. The node's lean.statement is verbatim the file signature.

Validation: independent single-file server compilation passed without errors or
warnings. Delivery preflight and dry run are run after this report is appended.
