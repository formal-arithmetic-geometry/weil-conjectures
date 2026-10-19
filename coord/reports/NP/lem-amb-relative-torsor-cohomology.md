## Worker report

The delivery states `lem-amb-relative-torsor-cohomology` in
`lean/Sheaf/AlgebraicGeometry/RelativeTorsorCohomology.lean`. It supplies two
missing definition nodes and their modules. All theorem proofs are `sorry`.
Definitions have actual data: the relative complex is Mathlib's mapping cone
of restriction, shifted by minus one; its maps are the actual maps of shifted
cones. No data is selected from a theorem asserting mere existence.

The main classification is `AlgebraicGeometry.Etale.relative_torsor_cohomology`.
Its existential is a simultaneous family of bijections for all schemes, opens,
abelian sheaves and injective-resolution models. The direction is from torsor
classes to relative H1, equivalently the bijection in the node. It includes all
four clauses in the same existential, so its naturality clauses constrain the
same bijection as its normalization and forgetful clause. The other declarations
listed in `lean.declarations` supply the connecting maps and the comparison
interfaces required to state their canonical meaning.

Hypothesis and clause correspondence:

- `T : Scheme.{u}` is the arbitrary scheme. `W : T.Opens` represents the open
  complement V, with object `Scheme.Etale.mk W.ι`. No construction depends on
  the scheme structure of the closed complement. For the node's closed
  immersion i use its open complement as W; conversely every open complement
  has a closed subscheme structure, so using arbitrary W neither restricts
  nor strengthens the assertion about pairs (T,V). Nilpotents on Z impose
  no additional hypothesis. Under h the open is exactly `h ⁻¹ᵁ W`.
- `G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u+1}` is the abelian sheaf,
  with the project's existing small-site size convention. There is no torsion,
  finite-type, separatedness, nonemptiness, or characteristic hypothesis.
- `I : InjectiveResolution G` is a computational model, universally quantified,
  rather than a geometric hypothesis. `relativeSections` evaluates its
  nonnegative complex and extends by zero. `relativeSectionRestriction` is
  the existing section restriction from the identity terminal object.
  `relativeSectionComplex` is literally
  `(CochainComplex.mappingCone restriction)⟦(-1 : ℤ)⟧` and
  `relativeCohomology` is its homology in integer degree q. Open restriction
  preserves K-injectives, so the two terms compute the RΓ terms of the node.
  This uses no alternative derived category or arbitrary cone object.
- `Sheaf.Torsor.WithSection` is `(P : Torsor G) × P(U)`.
  `WithSection.IsIsomorphic` requires a torsor isomorphism whose actual section
  map carries P's section to Q's. `WithSection.Classes` is the quotient by
  exactly that equivalence relation. The equivalence-relation proof is a
  named theorem, with its statement included in the new definition node.
- The main existential's `e T W G I` is a bijection between these classes and
  `relativeCohomology ... I 1`. Its first conjunct sends the class of
  `(Torsor.trivial G, 0)` to zero, the additive identity-section convention.
- Its second conjunct uses `relativeForgetH1`: actual shifted-cone first
  projection, homology, the standard extension-by-zero homology isomorphism,
  then the existing normalized `ResolutionSectionCanonicalComparison`.
  Its value is the existing `Torsor.classH1` of the underlying torsor P.
  The comparison parameter is universally quantified over normalized
  comparisons; it is not an unconstrained equivalence. The existing
  `EtaleResolutionSectionCanonicalData` proves their existence.
- The third conjunct quantifies over every coefficient map f, every
  augmentation-preserving `InjectiveResolution.Hom`, and every existing
  `ContractedProductPresentation`. The specified section is exactly
  `q.quotient U s 0`. The map on cohomology is homology of the actual
  coefficient-induced shifted-cone map `relativeSectionMap`.
- The fourth conjunct permits every scheme morphism h and every
  `f : G ⟶ (lowerStar _ h).obj G'`. By the recorded inverse-image/direct-image
  adjunction these are exactly all maps `h⁻¹G ⟶ G'`, including the identity
  coefficient case, not only cases where inverse image equals G'. The
  resolution augmentation equality fixes which coefficient map is lifted.
  The natural transformation b is a map from P to the direct image of Q,
  with explicit f-equivariance `hb`. Such a map identifies Q with the
  contracted product of the pulled-back torsor under this coefficient map:
  locally trivializing P makes this a translation of G'. The new section is
  b(s) restricted along the existing `openSectionPullback h W`. The equality
  uses `relativeTransfer`, built from the existing global and open section
  transfers by extension and the actual cone map.
- `relative_comparison_exists` supplies an augmentation-preserving comparison
  for every adjoint coefficient map, so the fourth conjunct is not conditional
  on an unavailable comparison. `relativeTransfer_independent` says any two
  such comparisons induce exactly the same map in every integer degree.
  Comparison between resolution models, identity maps, and compositions
  therefore have the same canonical interpretation as the node's maps.
- `relative_coefficient_sequence` starts with any actual
  `S : ShortComplex (Sheaf ... AddCommGrpCat)` and `hS : S.ShortExact`.
  It supplies injective resolutions and commuting augmentation equations,
  a zero composite, and split rows using Mathlib's existing
  `ShortComplex.Splitting`. It states that their relative complex sequence
  is short exact. Thus no class of short exact coefficient sequences is omitted.
- `relativeConnecting T U S hs q` is literally the existing homology boundary
  `(relativeShortComplex_shortExact ...).δ q (q+1) rfl`. Its domain and target
  are Hq of the third relative complex and H(q+1) of the first. It is not an
  unspecified homomorphism. The split-row witnesses are only proofs about
  the supplied horseshoe model, not extra hypotheses on the coefficients.
- `relativeConnecting_forget` identifies its composite with cone projection
  with the ordinary boundary of the same evaluated horseshoe.
  `relativeConnecting_coefficient_naturality` gives the boundary square for
  a morphism of coefficient-resolution sequences.
  `relativeConnecting_pullback_naturality` gives that square under arbitrary
  h and a sequence comparison into direct image, including arbitrary
  subsequent coefficient morphisms. These are the maps used in the main
  bijection's naturality clauses. Applied to lifts of coefficient-sequence
  identities, these statements also give independence of horseshoe choices.

The coefficient-sequence results are stated for the explicit split resolution
models, rather than asserting a choice of boundary with no relationship to
coefficient sequences. The supplied existence theorem ensures every short exact
coefficient sequence has such a model. The connecting naturality docstrings
explain the exact relative functor, shift sign, cone comparison, and horseshoe
boundary comparison used to identify this model with the derived boundary.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.DerivedCategories` and Mathlib's
  `DerivedCategory`, cochain complexes, homology, cone and shift, as recorded
  for `def-weil-pbc-derived-categories` and `def-weil-abstract-derived-category`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`: the recorded abelian/set
  sheaf conventions; the actual category here is Mathlib's `Sheaf` on the
  small etale topology.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar`, `Etale.lowerStar`, and
  `Etale.upperStarLowerStarAdjunction`; naturality uses the adjoint encoding.
- `WeilConjectures.CategoryTheory.Sites.Torsor`:
  `CategoryTheory.Sheaf.Torsor`, `Torsor.Iso`, `Torsor.trivial`, and the
  normalized ordinary class `Torsor.classH1`.
- `Sheaf.CategoryTheory.Sites.ContractedProductPresentation`:
  `Torsor.ContractedProductPresentation` and its actual `quotient` map.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`:
  `Etale.rightDerivedGlobalSections` and `Etale.cohomology`, whose resolution
  convention the actual relative cone computes.
- `Sheaf.AlgebraicGeometry.EtaleResolutionSectionTransfer`:
  `resolutionSectionTransfer`, `globalResolutionSectionTransfer`,
  `openResolutionSectionTransfer`, `openSectionPullback`, and the terminal/open
  naturality square. These canonical maps are reused, not copied.
- `Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison`:
  `ResolutionSectionCanonicalComparison`, including its cocycle normalization.
- Mathlib's `InjectiveResolution`, `ShortComplex`, `ShortComplex.Splitting`,
  `ShortComplex.ShortExact.δ`, `HomologicalComplex.extendMap`,
  `extendHomologyIso`, and `homotopyCofiber.mapArrowHom`.

Recorded proof-dependency modules are imported without `public`, including the
horseshoe, inverse-image exactness, ordinary torsor naturality, and derived-unit
comparison modules. The full ten-step DAG proof is in the main theorem's
docstring. Each other postponed theorem has its source, blueprint marker,
mathematical statement, and proof plan in its own docstring.

Sources opened: `sites-cohomology.tex`, `lemma-torsors-h1` (03AJ), including
its canonical free-abelian-sheaf extension and connecting image of 1;
`cohomology.tex`, `lemma-triangle-sections-with-support` (0G71), and
`remark-support-functorial` (0G78). The relative refinement is explicitly
agent-stated in the DAG, not attributed verbatim to 03AJ.

Searches: renewed `msearch.py` LeanFinder query "Relative first cohomology
classifies abelian sheaf torsors with a specified section on an open subset"
returned eight ordinary cover-Cech H1 hits, not the relative classifier.
Loogle `CochainComplex.mappingCone` returned the generic cone API used here,
not relative sections or pointed torsors. Mathlib grep
`relativeCohomology|torsor.*section|WithSection` under CategoryTheory returned
zero hits. LeanSearch was attempted separately for pointed torsor classes and
relative resolution cones; both requests returned Internal Server Error,
recorded as unavailable. Direct rg of the source tree and project `lean/Sheaf`
found no relative classifier or either new notion; exact item-id upstream
search found no match. A final search for every declared name found no
collision in Mathlib, the source project, or existing project Sheaf modules.
Blueprint searches "torsor section" and "relative cohomology" each returned
zero matching blueprint nodes. The searches and digests are recorded in each
new node and the sandbox search log.

Edge cases: W empty gives ordinary torsors and H1; W=T gives a contractible
relative cone and one class of globally pointed torsors. G=0 gives one class.
The empty scheme and arbitrary nonreduced closed complements are included.
The constructions accept all integer q, including negative q; extension by
zero makes the expected negative relative groups vanish. Identity h, arbitrary
coefficient morphisms, and zero coefficient sequences are not excluded.
No statement correction or mathematical dispute was identified.

Validation: all delivered modules are compiled separately using `scompile.py`
on the server, nice 19, two threads, 60 seconds per file. No local compiler or
lake build was used. Final delivery dry-run outcome is recorded below after
preflight. Nothing is pushed by this worker; independent second reading remains
the next step.

## New nodes

`def-amb-torsor-with-section` introduces the pair, section-preserving
isomorphism relation, its equivalence law, and quotient classes. It uses the
existing general `Torsor` definition. Source: relative refinement of 03AJ as
specified in the item's proof. The recorded searches found only ordinary
Cech classes and no existing pointed-torsor quotient.

`def-amb-relative-etale-cohomology` introduces evaluated resolution complexes,
restriction, the actual shifted cone, its homology, maps of strict restriction
squares, and the forgetting projection. Source: the explicit relative
resolution refinement in the item's proof, compared with 0G71 and 0G78.
The generic cone operations found by Loogle are used directly; they do not
already define this geometric restriction complex. The evaluation and section
transfer primitives of existing project nodes are imported and reused.

There are no dependency modules. The earlier normalized absolute comparison
prototype is retained only in scratchpad and is not part of this delivery.

Final worker verification: all three modules compiled cleanly, with no warnings.
`deliver2.py NP lem-amb-relative-torsor-cohomology --no-push` printed
`OK (dry run)`: the packet compiles and passes preflight except for the independent
second-reading section, which the second reader writes. The first preflight's
metadata faults (a docstring word picked up as a declaration, and a signature
modifier outside the recorded keyword) were repaired. No delivery was pushed.

## Second reading by NP

I independently read the node, both new nodes, all three modules, and the recorded
statement-dependency interfaces. I opened Stacks sites-cohomology.tex,
lemma-torsors-h1 (03AJ), including its pushout extension and boundary of 1;
and cohomology.tex, lemma-triangle-sections-with-support (0G71) and
remark-support-functorial (0G78). The latter are comparison sources for the
explicitly agent-stated relative refinement, not verbatim small-etale-site
statements. The general-site torsor source imposes no omitted finiteness,
Noetherian, characteristic, or nonemptiness hypothesis.

My object/hypothesis/conclusion checklist against the node follows. Each
entry gives the Lean rendering and my verdict.

- Arbitrary scheme T and closed immersion with open complement V and j:
  `T : Scheme.{u}`, `W : T.Opens`, `Scheme.Etale.mk W.ι`. Exact equivalent
  parameterization: only the open complement enters the construction. Every
  open has a reduced closed subscheme complement; the given closed subscheme
  may instead be nonreduced without changing the pair. Pullback is `h ⁻¹ᵁ W`.
- Arbitrary abelian etale sheaf G: `Sheaf T.smallEtaleTopology
  AddCommGrpCat.{u+1}`. Exact recorded coefficient category, without torsion
  or constructibility assumptions. I read upstream upperStar, lowerStar and
  upperStarLowerStarAdjunction: adjoint coefficient maps really represent
  all h⁻¹G→G', rather than an equality h⁻¹G=G'.
- Relative group defined by Cone(RΓ(T,G)→RΓ(V,j⁻¹G))[-1]:
  `relativeSections`, `relativeSectionRestriction`, `relativeSectionComplex`,
  `relativeCohomology`. Exact actual Mathlib cone, shift and homology.
  `InjectiveResolution` has nonnegative complex, injectivity, augmentation
  and quasi-isomorphism fields; it is a model parameter, not a restriction
  on G. Open restriction preserves injectives via exact extension by zero,
  so open evaluation computes the required derived sections.
- P a G-torsor and s a section on V, with section-preserving isomorphisms:
  `WithSection` is the dependent pair, `IsIsomorphic` uses upstream
  `Torsor.Iso` and equality on the section, and `Classes` its quotient.
  Exact. I read upstream Torsor, Iso, and trivial, including equivariance
  and local nonemptiness, rather than relying on their names.
- Canonical bijection: `∃ e : ∀ T W G I, ... ≃ ...`. Exact bijection in
  the inverse direction of the node's wording. All four laws constrain
  the same simultaneous e; comparisons cover changes of resolution model.
- Trivial torsor and identity section map to zero: first conjunction,
  `Torsor.trivial G` with actual zero section, followed by `= 0`. Exact.
- Forgetting s gives the ordinary class: second conjunction,
  `relativeForgetH1 ... (e ... ⟦P⟧) = Torsor.classH1 ... ⟦P.1⟧`. Exact.
  I read ResolutionSectionCanonicalComparison, including its global_cocycle
  normalization by extMk, and the existing existence theorem in
  EtaleResolutionSectionCanonicalData. Thus this is not a vacuous comparison
  quantifier or an arbitrary equivalence. I checked mappingCone.fst and
  equivHomShift in Mathlib: projection is the source coordinate; negating
  the B coordinate identifies the actual cone with the proof's signed model.
- Naturality for every G→G': third conjunction uses every f, every
  augmentation-compatible `I.Hom J f`, actual relativeSectionMap, and
  ContractedProductPresentation. Exact. I read the presentation's quotient,
  invariance, translation, naturality and universal-property fields.
  `q.quotient ... P.2 0` is precisely the induced specified section.
- Naturality for every scheme map followed by every coefficient map:
  fourth conjunction uses adjoint f, augmentation-preserving a, and
  f-equivariant b into the direct image of Q. Exact adjoint encoding.
  Locally trivializing P identifies the induced contracted-product map with
  a translation of G', hence an isomorphism. No arbitrary relative-group
  map is assumed. The section is b(P.2) restricted along openSectionPullback.
  I read the actual existing section-transfer definitions and restriction
  square. relative_comparison_exists and relativeTransfer_independent ensure
  availability and independence of lifts, including identity maps.
- Every short exact coefficient sequence and every integer q:
  relative_coefficient_sequence takes any short exact sheaf ShortComplex,
  supplies resolutions and commuting augmentations, and supplies split rows.
  relativeConnecting is the actual Mathlib homology boundary of its relative
  short exact complex sequence. Exact: split rows are provided models, not
  restrictions on coefficient sequences.
- Boundary commutation with forgetting support, coefficient maps and scheme
  pullback: relativeConnecting_forget, relativeConnecting_coefficient_naturality,
  relativeConnecting_pullback_naturality. Exact three squares, stated as
  separate declarations recorded under this item. Horseshoe morphism lifting
  supplies sequence comparisons; identity sequence comparisons give model
  independence. Docstrings identify the boundary sign using the horseshoe
  off-diagonal, shift comparison and cone convention.

Both new nodes also pass separate source and definition review. The pointed
node adds just a specified section, its preserving relation and quotient to
existing torsors. Its equivalence proof is a separate named theorem; data is
not sorry. The relative node adds evaluation/restriction and an actual cone,
not another derived category. Its strict-square map is Mathlib's shifted
homotopyCofiber.mapArrowHom, and its forgetting map the actual projection.
I checked their chapter/unit, definition kind, split status, empty proof fields,
null mathlib_match, creation, blueprint ancestry, searches and lean records.
Both are cited by the item. There are no dependency modules and no statement
correction. Blueprint ancestry was independently checked with blueprint_refs.py.

Edge cases: W empty recovers ordinary torsors and absolute H1; W=T gives
an acyclic identity cone and one class of globally pointed torsors. G=0 and
the empty scheme give singleton classifications. Nonreduced complements are
allowed. Degree zero and all negative integers are accepted by the group and
boundary definitions. No index-family or characteristic restriction appears.
The pointed construction has independent site/coefficient universes u,v,w;
the geometric construction uses the recorded small-site coefficient size u+1,
without equating site object and morphism universes or adding a smallness
hypothesis. Identity h and arbitrary subsequent coefficient maps are included.

Independent searches used different phrasing. LeanFinder query "Isomorphism
classes of abelian torsors trivialized over an open subscheme and cohomology
with support" returned eight hits: ordinary cover Cech H1 and unrelated
scheme section lemmas, no relative classifier. Loogle mappingCone returned
twelve generic cone declarations, which are reused. LeanSearch query "Abelian
sheaf torsors with a trivialization on an open set classify degree one
cohomology with support" returned Internal Server Error: unavailable, not a
negative verdict. Direct rg of all Mathlib, upstream WeilConjectures and
project Sheaf for relativeCohomology, WithSection, pointed.?torsor and
trivialized.?torsor found no existing declarations. Additional conceptual DAG
searches found supported Kummer and Cartier-map consumers, not a pre-existing
node defining either new notion. The existing transfer and normalized absolute
comparison notions are imported and reused.

No mathematical or signature mismatch was found; no Lean or node statement
was rewritten. All postponed proofs are named theorem proofs; definitions
contain real constructions with separate named proof obligations. Every
source/blueprint docstring is present, including the ten-step proof. All three
files compiled separately and cleanly via scompile.py on the server, nice 19,
two threads, 60 seconds per file (1.0 s, 1.5 s, 5.9 s respectively). This
independent review record is the only change made by the second reading.


## Immutable-delivery maintainer review

Independent review of d38829693117d39a8c1b950ea938f0935fca31b5 found
one stage-2 gate defect (delivery-errors H6): relativeFiberMap contained
an inline arithmetic tactic proof. The complete replacement module uses
Mathlib's existing sub_add_cancel j 1 instead. The reflexivity witness in
relativeForgetH1 is also expressed directly as rfl rather than an inline
by block. Neither change alters a declaration signature, mathematical
statement, definition data, dependency record, or universe.

All three modules in the corrected overlay compiled separately through
scompile.py, nice 19, two threads, 60 seconds per file: TorsorWithSection
1.1 s, RelativeEtaleCohomology 1.4 s, RelativeTorsorCohomology 5.9 s,
exit status 0 with no diagnostics. The immutable versions also compiled
cleanly (1.1 s, 1.5 s, 5.7 s). Only review artifacts were written; the
snapshot and project clones were not edited. Full clause, dependency,
source, size, edge-case and definition checks are recorded in review.md
beside the immutable snapshot. No mathematical correction was required.
