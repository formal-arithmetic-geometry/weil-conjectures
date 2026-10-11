## Reviewer fix (R-taf1249)

The delivery recorded the source's generic `DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat`
(arbitrary closed braided monoidal Grothendieck abelian `C`, `K : DerivedCategory C`,
`ObjectProperty.flat`) as `existing: true`. That is a generalization, not the node: the node is
about a cochain complex M of A-modules, flat A-modules (`Module.Flat`), and a ≤ b. Restated as a new
module `Sheaf.Algebra.Homology.TorAmplitudeFlatModel`,
`DerivedCategory.module_torAmplitudeIn_iff_exists_flat_model`: `{A : Type u} [CommRing A]
[HasDerivedCategory.{w} (ModuleCat.{u} A)] (M : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
(hab : a ≤ b)`, `torAmplitudeIn (ModuleCat A) a b (Q.obj M) ↔ ∃ P, (∀ i, Module.Flat A (P.X i)) ∧
(∀ i, i < a ∨ b < i → IsZero (P.X i)) ∧ Nonempty (Q.obj M ≅ Q.obj P)` (proof `sorry`; the reviewer
checked in a sandbox that it follows from the generic source theorem via
`ObjectProperty.flat_iff_preservesFiniteLimits` and `Module.Flat.iff_preservesFiniteLimits_tensorLeft`
and `CochainComplex.isStrictlyGE_iff`/`isStrictlyLE_iff`, so the statement is faithful). The
Tor-amplitude notion is the source's `DerivedCategory.torAmplitudeIn` (Stacks 0651); no new definition.

## Worker report

Existing declaration, no new module: `DerivedCategory.torAmplitudeIn_iff_exists_iso_Q_obj_flat`
in `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`, lines 300–309 of the
read-only slopmaster2 source. Its docstring states the bounded-flat-model equivalence.
The source file also contains the complete truncation/Tor-criterion proof. This declaration
was missed by the stage-1 searches. Record it instead of duplicating it.

Source checked: https://stacks.math.columbia.edu/tag/0654 (currently Lemma 15.68.3;
the node's older section number is immaterial). Its two clauses are precisely Tor amplitude
and a quasi-isomorphic flat complex supported in the interval. Stacks uses commutative
unital rings throughout, as also recorded in the correction of the existing dependency
`lem-pc-module-bounded-flat-kflat`. Thus `CommRing A` renders the source's ring convention.

Hypothesis and clause correspondence:

- A ring A: specialize `C := ModuleCat.{u} A`, with `(A : Type u) [CommRing A]`.
  Arbitrary u is allowed; the zero ring is allowed.
- M a cochain complex: `(M : CochainComplex (ModuleCat.{u} A) ℤ)`, and set
  `K := DerivedCategory.Q.obj M`. The theorem permits every derived object, hence every M.
- Integers a ≤ b: the existing theorem binds `(a b : ℤ)` and works without an ordering
  restriction. Applying it to the node's ordered pair does not require any added hypothesis
  and does not discard the a = b case. We record the stronger generic declaration as an
  existing specialization, rather than create an unnecessary wrapper.
- Tor-amplitude clause: `torAmplitudeIn (ModuleCat A) a b (Q.obj M)` unfolds to
  `∀ N : ModuleCat A, homologyConcentratedIn a b (Q.obj M ⊗ (singleFunctor _ 0).obj N)`.
  The tensor is the derived tensor, constructed by K-flat localization, not an arbitrary
  monoidal structure. `homologyConcentratedIn` is `IsGE a ∧ IsLE b`; Mathlib's
  `DerivedCategory.isGE_iff` and `isLE_iff` identify these with vanishing cohomology below a
  and above b, respectively. This is exactly the quantified H^i(M tensor-derived N) clause.
- Existence of P: `∃ (P : CochainComplex (ModuleCat A) ℤ)`.
- Termwise flatness: `∀ n, ObjectProperty.flat (P.X n)`. The source defines flat objects by
  exactness of tensor on both sides. Its `ObjectProperty.flat_iff_preservesFiniteLimits`
  identifies this with preservation of finite limits by tensorLeft. Mathlib's
  `Module.Flat.iff_preservesFiniteLimits_tensorLeft` identifies precisely the same predicate
  with `Module.Flat A (P.X n)`. There is no extra projectivity or finite-generation clause.
- P^i = 0 outside [a,b]: existential `P.IsStrictlyGE a` and `P.IsStrictlyLE b`.
  `CochainComplex.isStrictlyGE_iff` says `∀ i < a, IsZero (P.X i)`;
  `isStrictlyLE_iff` says `∀ i > b, IsZero (P.X i)`. IsZero is the categorical zero module.
- Isomorphism in D(A): `Nonempty (Q.obj P ≅ Q.obj M)`, equivalent by taking inverses to
  the requested `Q.obj M ≅ Q.obj P`. No chain isomorphism is demanded.
- If and only if: the declaration's outer `↔`.

The theorem's general category hypotheses specialize without extra mathematical assumptions:
ModuleCat is Grothendieck abelian, braided symmetric monoidal closed and monoidal preadditive.
`ModuleCat.hasFunctorialFlatResolution` in
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution` supplies functorial
flat resolutions for every commutative A. `[HasDerivedCategory.{w} (ModuleCat.{u} A)]` merely
chooses the localization and its morphism universe; Mathlib supplies `HasDerivedCategory.standard`.
The server check explicitly used arbitrary universes u,w and synthesized every other instance.

Dependency declarations read:

- `def-pc-cochain-complex-modules`: `CochainComplex` in
  `Mathlib.Algebra.Homology.HomologicalComplex`; the recorded generic declaration supplies
  the same integer-indexed complex construction with C = ModuleCat A.
- `def-pc-kflat-complex`: `CochainComplex.IsKFlat` / `IsKFlatResolution` in
  `Sheaf.Algebra.Homology.KFlat`. These are sheaf predicates and are not directly applied to
  ModuleCat; the node only needs them in its proof. The existing theorem's module uses the
  equivalent module K-flat construction already carried by `def-pc-module-kflat-complex`,
  rather than defining a duplicate sheaf or module predicate.
- `def-pc-derived-category`: `AlgebraicGeometry.schemeDerivedCategory` in
  `Sheaf.AlgebraicGeometry.DerivedCategory`. This is specifically D(O_X), not D(A).
  Its citation in the item is a loose reference to the underlying localization construction.
  For the module category, the existing theorem uses Mathlib `DerivedCategory` and Q,
  the generic construction carried by `def-weil-abstract-derived-category`.
  No dependency definition needs rewriting: both specialized sheaf definitions are correct,
  and no new Lean statement using an ill-typed specialization is written in this delivery.

Edge cases checked: zero ring, zero complex, acyclic M (zero flat representative), singleton
interval a = b (a shifted flat module), negative endpoints and shifts, arbitrary unbounded M,
and arbitrary module N without finite-generation restrictions. A nonflat module in degree zero
does not satisfy Tor amplitude [0,0], so the statement does not confuse ordinary tensor with
derived tensor. The existing theorem even handles reversed intervals, but the item only asks
for ordered intervals. No statement dispute or mathematical correction is needed.

Searches made (actual outputs are logged in searches.jsonl):

- msearch leanfinder: "A complex of modules has Tor amplitude in [a,b] if and only if it has a
  bounded flat representative in those degrees"; eight generic derived-category support hits,
  including exists_iso_Q_obj_of_isGE_of_isLE, but no flat-model equivalence in Mathlib.
- msearch loogle: "Module.Flat, CochainComplex"; zero hits.
- msearch grep: "torAmplitudeIn_iff|tor.amplitude.*flat", Algebra/Homology; zero hits.
- msearch leansearch: "Tor amplitude of a derived complex of modules tested against all modules
  in degree zero"; unavailable, Internal Server Error (no negative-match verdict).
- msearch grep: "torAmplitude|TorAmplitude", Algebra/Homology; zero hits.
- rg of the source and lean/Sheaf for torAmplitude / IsKFlat: found the generic source
  TorAmplitude module and landed sheaf K-flat modules; no module-specific duplicate in Sheaf.
- rg of the source, lean/Sheaf and dag/lean_names_upstream.json for
  "torAmplitudeIn_iff_exists_iso_Q_obj_flat|torAmplitudeIn_iff_exists_flat": found the exact
  existing theorem in the source FlatModel module, line 302.
- rg of the source for the item id: no hits (the new generic theorem has no blueprint id).
- tools/blueprint_refs.py search "Tor amplitude": existing scheme/sheaf nodes, no second
  module flat-model node; ancestor returns lem-sc-finite-duality.

Validation: scratchpad/Check.lean imports the existing theorem and the ModuleCat flat-resolution
instances; it checks the theorem specialized to C = ModuleCat A and K = Q.obj M and checks both
flatness equivalences. This is a scratch check only, not a delivery module. No proof or new
notion is added, and the node changes only in lean.


## Second reading by M1

I independently opened the delivered JSON and the existing declaration at
`WeilConjectures/CategoryTheory/DerivedCategory/FlatModel.lean:302`, including its
section variables at lines 196–199 and the definitions it uses. Verdict: keep the existing
record; no new module, definition node, dependency module, or statement correction is needed.
The node's `lean.statement` agrees verbatim with the declaration signature before `:=`.
No mathematical or Lean change was made; this second-reading section is the change.

The local literature checkout is absent on this machine. I therefore fetched the Stacks
`.tex` sources into the sandbox scratchpad and read `more-algebra.tex`, section `section-tor`,
labels `definition-tor-amplitude` and `lemma-tor-amplitude`, and `algebra.tex`, section
`section-conventions`. These are the source places behind [Tag 0654]
(https://stacks.math.columbia.edu/tag/0654) and its amplitude definition Tag 0651.
The ring convention includes commutativity, a unit, and the zero ring. No Noetherian,
finite-generation, projectivity, boundedness of the input, or characteristic hypothesis
is assumed by the lemma. The source allows arbitrary integer endpoints; the node restricts
its requested instances to ordered endpoints.

Object/hypothesis/conclusion checklist, made before comparing the signature:

1. **Ring A.** Instantiate `C := ModuleCat.{u} A` with `A : Type u` and `[CommRing A]`.
   Verdict: same rings as the source, including the zero ring. All generic category,
   abelian, Grothendieck, braided monoidal, closed, and preadditive assumptions are
   supplied by ModuleCat instances. The additional generic flat-resolution class is
   supplied for every such A by `ModuleCat.hasFunctorialFlatResolution` (opened at
   `GrothendieckAbelian/Monoidal/FlatResolution.lean:135`). No ring hypothesis is added.
2. **Cochain complex M of A-modules.** `M : CochainComplex (ModuleCat.{u} A) ℤ`, with
   the theorem's `K := DerivedCategory.Q.obj M`. Verdict: same complex, no input
   support restriction. I opened Mathlib's `CochainComplex` abbreviation and the
   `DerivedCategory`/`Q` definitions, not just their names.
3. **Integers a ≤ b.** The declaration binds `(a b : ℤ)` without a comparison hypothesis.
   Verdict: for every ordered pair in the node, its specialization is exactly the requested
   equivalence. Reusing a generic declaration also applicable to other pairs adds no
   assumption to that specialization; it is not a replacement claim with a stronger
   conclusion for the ordered pair. No wrapper should duplicate this existing theorem.
4. **Amplitude against every module N and every degree outside [a,b].** The left side is
   `torAmplitudeIn (ModuleCat A) a b (Q.obj M)`. I opened `TorAmplitude.lean:59`:
   it universally quantifies `F : C`, tensoring K with `(singleFunctor C 0).obj F`.
   `homologyConcentratedIn` is the standard t-structure's `IsGE a ∧ IsLE b`, hence
   vanishing below a and above b, with endpoints included. Verdict: both universal
   quantifiers and degree bounds agree, and N has no finiteness restriction.
   I opened `Monoidal/Instances/DerivedCategory.lean` and
   `HasMonoidalDerivedCategory.lean`: this tensor is the left derived tensor of the
   ModuleCat tensor, obtained through K-flat localization. It is not an arbitrary tensor
   or ordinary tensor on M. The FlatModel comparison with tensoring a K-flat complex
   by F in degree zero confirms that interpretation.
5. **One complex P exists.** `∃ (P : CochainComplex C ℤ)` lies on the right of `↔`.
   Verdict: one representative P works for all modules N; it is not selected separately
   for each N.
6. **Every term of P is flat.** `(∀ n, ObjectProperty.flat (P.X n))`.
   I opened `ObjectProperty.flat_iff_preservesFiniteLimits` and Mathlib's
   `Module.Flat.iff_preservesFiniteLimits_tensorLeft`. Both identify their flatness
   predicates with finite-limit preservation of the same `tensorLeft` functor.
   Verdict: precisely ordinary flat A-modules, no free/projective or finite-rank demand.
7. **Terms vanish outside [a,b].** Existential witnesses of `P.IsStrictlyGE a` and
   `P.IsStrictlyLE b`. I opened Mathlib `Embedding/CochainComplex.lean:139–151`:
   these mean `IsZero (P.X i)` for i < a and b < i. Verdict: termwise zero, not merely
   vanishing cohomology. A categorically zero module is exactly the zero-module condition.
8. **Isomorphism M ≅ P in D(A).** `Nonempty (Q.obj P ≅ Q.obj M)`.
   Verdict: invert the isomorphism to obtain the node's orientation. This is an
   isomorphism in the localization, not a chain isomorphism or a demand for a single
   directed quasi-isomorphism between the original two complexes.
9. **Equivalence.** The outer `↔` includes both implications. Verdict: all clauses agree.

Dependency records and signatures were read independently. `def-pc-cochain-complex-modules`
records Mathlib's generic `CochainComplex`, which directly supplies the ModuleCat complex.
`def-pc-derived-category` records the scheme specialization `schemeDerivedCategory`; it is
not itself D(A). Its defining module explicitly applies Mathlib's generic derived-category
construction, already carried by `def-weil-abstract-derived-category` (a proof dependency
of this item). The theorem uses that shared generic construction directly. Likewise
`def-pc-kflat-complex` records the ringed-site predicate `CochainComplex.IsKFlat`; it is not
applied to ordinary modules here. The theorem's proof uses the generic
`MorphismProperty.kFlat` predicate already recorded on `def-pc-module-kflat-complex`.
The sheaf dependency modules state their own nodes correctly; replacing their declarations
with module-only predicates would be wrong. The item's references are to those constructions
specialized to ordinary modules, and its amplitude definition is self-contained.
There is no missing notion, private definition, or unusable definition that this delivery
needs to recreate. There are no new nodes or delivered dependency modules to review.

Edge cases: u is arbitrary; w is the chosen localization morphism universe, with a standard
localization available in the allowed universe. The scratch specialization checks arbitrary
u,w conditional on `HasDerivedCategory`, without a restriction on A. Zero A, zero M,
acyclic M, negative endpoints, and a = b are all covered. For [0,0] the representative is
one flat module in degree zero, so an arbitrary nonflat module is not incorrectly asserted
to qualify. No nonzero, field, characteristic, inhabited-index, or finite-generation
hypothesis appears. There is no scheme or index set in the statement; empty-scheme and
empty-index tests are inapplicable. The existing theorem also covers the empty interval
b < a, where the supported representative is zero, though the node only requests a ≤ b.

Independent searches with different queries:

- `msearch leanfinder "vanishing derived tensor cohomology equivalent to flat resolution
  of prescribed length"`: eight hits, ordinary Tor/projective-vanishing and module-flatness
  criteria, not a competing flat-model statement.
- `msearch loogle "Module.Flat, CategoryTheory.MonoidalCategory.tensorLeft"`: four hits;
  in particular the precise Mathlib flatness comparison used above.
- `msearch grep "flat.*opcycles|exists.*flat.*isStrictly" Algebra/Homology`: zero hits.
- Direct `rg` for `tor.?Amplitude|flat.*model|bounded.*flat` in source derived-category
  modules, Mathlib Algebra/Homology, and project `lean/Sheaf`: the existing FlatModel
  equivalence is the match; project bounded-flat/K-flat and descent lemmas have different
  conclusions. The existing declaration should therefore be reused, without a new file.

H5/H6/H8/H9: the delivery adds no definitions, proof, or Lean file; the existing source
module is read-only and is correctly reused under the existing-declaration rule. Its
module documentation and converse theorem explain the same bounded-flat/K-flat,
Tor-criterion, and lower-truncation proof steps as the node. The source theorem's own
proof is pre-existing, not a stage-2 proof written by this delivery. Every variable in
its recorded signature is bound in the opened surrounding section. I left all correct
source text and node fields unchanged.

Validation: I reran `scompile.py M1 lem-pc-module-tor-amplitude-flat-model scratchpad/Check.lean`
on the absolute sandbox path. Server compile succeeded (exit 0, 1.8 seconds), without
warnings, printing the full generic signature, its ModuleCat/Q.obj M specialization,
and both flatness comparisons. Since the delivery has no Lean modules, there are no
additional delivery files to compile.
