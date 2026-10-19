## Worker report

The delivery states `SSet.Marked.Over.relative_cartesian_equivalence_saturation` in
`Sheaf.AlgebraicTopology.RelativeCartesianEquivalenceSaturation`. Its sole proof is `sorry`.
It uses the genuine existing prerequisite
`lem-coef-finite-relative-lifting-recognition` as landed and reviewed by Q44.
That prerequisite owns the finite relative generator definition and its lifting-recognition
statement. No new DAG nodes, statement corrections, or disputed statements are needed.
The item gains this prerequisite in `stmt_deps`; it was already in `proof_deps`.

Source checked directly: Lurie, Higher Topos Theory, Proposition the project server, proof of (1),
printed pp. 158-159; Definition A.2.6.12 and Corollary A.2.6.14, printed p. 825.
The PDF was downloaded from the node's source URL into this sandbox and converted to text.
The source has exactly the finite quotient detector, constant-vertex detector labels,
all other generator base maps, filtered-colimit-preserving replacement, and perfectness.
The node supplies the fiber criterion as a hypothesis to avoid presupposing the relative model.
The source says transfinite attachments; the node's sequential construction uses finite domains,
so an omega sequence suffices. The Lean conclusion records this omega sequence explicitly.

Clause-by-clause correspondence for the item:

- Arbitrary small base: `(S : SSet.{u})`, with no `Quasicategory S` hypothesis.
  Every marked object over the sharp base is the existing `SSet.Marked.Over S`.
- The mapping-test class `W_S` is the existing `SSet.Marked.Over.weak false`.
  Its definition quantifies over every small `Z : Over S` satisfying
  `IsNaturallyFibrant false Z` and tests `Enhanced.IsWeakHomotopyEquivalence
  (mapSharpPre f Z)`. These are precisely the node's relative sharp mapping tests.
  `relative_marked_anodyne_calculus` supplies the equivalence between naturally marked
  Cartesian fibrations and this natural-fibrancy encoding; no model structure is an input.
- Assumed fiber criterion: for every map `g : P ⟶ Q`, the two premises
  `IsNaturallyFibrant false P` and `IsNaturallyFibrant false Q` restrict the criterion
  to naturally marked Cartesian fibrations, exactly as in the node.
  The equivalence is `weak false g ↔ ∀ s, Enhanced.IsFunctorEquivalence (fiberMap g s)`.
  `fiberMap` uses the strict vertex fiber; `IsFunctorEquivalence` means an inverse up
  to coherent natural equivalences. Fibers of these inner fibrations are quasicategories.
- Replacement functor and natural map: `∃ (T : Over S ⥤ Over S)
  (η : 𝟭 (Over S) ⟶ T)`. They are witnesses of the theorem, not definitions using
  choice from an unproved arbitrary existence result.
- Its value is `Q_U^natural`: for every `X`, the conclusion supplies `Q : SSet.{u}`
  and `q : Q ⟶ S`, `relativeFibration false q`, and
  `T.obj X = cartesianNaturalOver q`. Thus both the underlying object and its map
  to the base, as well as the complete natural marking, are identified.
- Every unit belongs to the mapping-test class: `∀ X, ... ∧ weak false (η.app X)`.
- Preservation of filtered colimits: `PreservesFilteredColimits T`. For this slice the
  morphism universe is `u`, so the abbreviation fixes both diagram universes to `u`.
- Sequential finite-cell saturation: there is a family `j : ∀ i : I, A i ⟶ B i`,
  `I : Type u`, with `finiteRelativeGenerators S = ofHoms j`.
  Thus exactly the generators are enumerated, not a superclass or arbitrary filler maps.
  For each input `X`, `D : ℕ ⥤ Over S` is a sequence, `e : X ≅ D.obj 0` identifies
  its start, and `c : Cocone D` is a colimit with `c.pt = T.obj X`.
  The equation `e.hom ≫ c.ι.app 0 ≫ eqToHom h = η.app X` identifies its initial map
  with the actual unit. The use of isomorphism at the start and equality at the end
  only avoids prescribing choices of categorical colimits.
  At each `n`, the two colimit cofans are indexed by **all** pairs
  `k : Σ i : I, A i ⟶ D.obj n`. The first incidence equation specifies their attaching
  map as `k.2`, and the second specifies the coproduct of the generators as `j k.1`.
  `IsPushout t m (D.map (homOfLE (Nat.le_succ n))) r` requires the next term to be
  their attaching pushout. This expresses the actual simultaneous-cell construction,
  rather than just transfinite membership in a saturated class.
- Generators and labels: `finiteRelativeGenerators S` consists of the three exact
  existing families `flatMap (horn n i).ι`, `finalMarkedHorn n`, `triangleMarkingMap`,
  each indexed by every `b` from its marked codomain to `sharp S`. The last family is
  `flatToMarked markedEquivalenceDetector` with only `SSet.const s` as base map,
  one for each `s : S _⦋0⦌`. Fully marked base means such `b` are exactly arbitrary
  underlying simplicial maps to `S`. No Kan-complex generator (iv) is used.
- Contains isomorphisms: `isomorphisms (Over S) ≤ weak false`.
- Two-out-of-three: the three displayed implications cover closure under composition,
  cancellation of the first factor, and cancellation of the second factor.
- Closure under filtered colimits in the arrow category:
  `IsStableUnderFilteredColimits.{u, u} (@weak S false)`. Mathlib defines this via
  colimits of natural transformations, equivalently colimits in the arrow category.
- Fixed small subset and generation: `∃ G : MorphismProperty (Over S), G.IsSmall.{u}
  ∧ G ≤ weak false ∧ ...` gives the subset once for the entire class. For each arrow
  in the class the conclusion then supplies a small filtered `J`, an arrow-valued
  diagram `F`, and a colimit `c` with all `G (F.obj j).hom` and
  `Nonempty (c.pt ≅ Arrow.mk f)`. Colimits are understood up to their canonical
  isomorphisms, so this is the required filtered-colimit generation, not retract generation.
- Input universe: `S`, `Q`, slice Hom sets, generator indices `I`, all attachment indices,
  the generation subset's smallness, and the generation indexing category use `u`.
  `ℕ` is small in `u` and only sequences of small colimits occur. The type of all small
  simplicial sets itself lives in `u+1`, as usual. No equality of independent object and
  morphism universes and no additional model-category data are assumed.

Dependency declarations read and reused:

- `Sheaf.AlgebraicTopology.RelativeMarkedAnodyneCalculus`:
  `SSet.Marked.cartesianNatural`, `cartesianNaturalOver`, and
  `SSet.Marked.Over.relative_marked_anodyne_calculus`. The full source declaration
  and its proof docstring were read. Its arbitrary-base natural marking and relative
  mapping calculus supply the exact objects of the statement.
- `Sheaf.AlgebraicTopology.MarkedAnodyneLiftingCalculus`:
  `SSet.Marked.flatToMarked`, `finalMarkedHorn`, `finalMarkedSimplex`,
  `triangleMarkingMap`, `markedEquivalenceDetector`, `marked_anodyne_lifting_calculus`.
  Its definitions, full theorem signature and proof docstring were read. The detector
  is the genuine coequalizer of the two displayed face-degeneracy equations.
- Their existing public dependency `Sheaf.CategoryTheory.MarkedRelativeCartesianModel`:
  `SSet.Marked.Over` (the slice abbreviation),
  `IsNaturallyFibrant`, `relativeFibration`, `weak`, `mapSharp`, `mapSharpPre`, `fiberMap`,
  and `toBase`. Only these definitions are used; the downstream model-existence theorem
  is not used or assumed.
- `Sheaf.CategoryTheory.EnhancedDiagramsCones`:
  `SSet.Enhanced.IsFunctorEquivalence`, `AreNaturallyEquivalent`,
  `IsWeakHomotopyEquivalence`; the literal definitions and docstrings were checked.
- The landed Q44 prerequisite module gives `SSet.Marked.Over.finiteTestOver`,
  `finiteRelativeGenerators`, and `finite_relative_lifting_recognition`.
- Recorded, available proof dependencies are imported:
  `Sheaf.AlgebraicTopology.MarkedPointCartesianModel`,
  `Sheaf.AlgebraicTopology.KanQuillenRightProper`,
  `Sheaf.AlgebraicTopology.MarkedSaturationPerfectEquivalences`,
  `Sheaf.CategoryTheory.AccessibleArrowInverseImage`, and the original two dependencies.
  The recorded weak-equivalence-accessibility node has no declaration to import;
  it is a future proof dependency, not an extra hypothesis or needed statement notion.
- Mathlib `MorphismProperty.IsSmall`, `ofHoms`, `IsStableUnderFilteredColimits`,
  `PreservesFilteredColimits`, `Cofan`, `Cocone`, `IsColimit`, `IsPushout`, `Arrow` and
  `homOfLE` express all categorical notions. The Mathlib proof dependencies on
  elementwise filtered colimits and commutation with finite limits are imported through
  `Mathlib.CategoryTheory.Limits.Types.Filtered` and
  `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`.

Edge cases checked before completing the statement:

- Empty `S`: every object over it is empty; all four generator families have no base
  labels. Empty coproducts and pushouts give identity steps. Fiber quantification is
  vacuous as it should be, and no nonemptiness of `S` is introduced.
- `S = Δ[0]`: all base maps are unique and the generators become the absolute finite
  generators. The theorem specializes to absolute natural fibrancy and perfectness.
- Non-quasicategory bases: neither theorem has a quasicategory premise on its base
  or total space; the only quasicategories needed are vertex fibers of inner fibrations.
- Empty input or empty vertex fiber: all maps from nonempty generator domains to the
  empty object are absent, so the construction and the equivalence criterion retain
  these cases. `IsFunctorEquivalence` uses actual coherent inverses, so empty-to-nonempty
  fiber maps are not accidentally equivalences.
- The `n = 0` member of `finalMarkedHorn n` is the dimension-one generator, supplying
  prescribed-target lifts. Inner-horn indices require `0 < i.val` and `i.val < n`,
  so spurious zero-dimensional horns are not imposed.
- The detector's nonconstant base maps are deliberately excluded. Marking a detector
  over an arbitrary base would not be the source's Cartesian-fibrancy construction.
- All coproducts can have empty indexing types, while the filtered generation index
  uses `IsFiltered J`, including its required nonemptiness. No inhabitance assumption
  is imposed on a simplicial set or a fiber.

Searches performed (through `msearch.py Q107 lem-coef-relative-cartesian-equivalence-saturation`):

- LeanFinder: “Functorial finite cell saturation over a simplicial base and perfectness
  of Cartesian equivalences of marked simplicial sets”: 8 hits, finite-presentability
  and Kan-Quillen declarations, no exact marked relative saturation theorem.
- LeanSearch: “A class of cartesian equivalences of marked simplicial sets over a base
  admits finite sequential fibrant replacement preserving filtered colimits”: 8 hits,
  generic filtered-colimit, fibration, and finite-presentability results; no match.
- Loogle: `SSet, MorphismProperty.IsStableUnderFilteredColimits`: 0 hits with unknown
  unqualified identifier; retry `CategoryTheory.MorphismProperty.IsSmall`: 12 hits
  confirming Mathlib's small-arrow-set interface, no marked saturation theorem.
- Mathlib grep: `relative.*saturation|cartesian.*perfect|finiteMarkedGenerators` under
  `AlgebraicTopology`: 0 hits.
- Project/upstream rg: `finiteMarkedGenerators|finiteRelativeGenerators|
  relative_cartesian_equivalence_saturation|IsPerfectClass`. No upstream match;
  the side project already has the absolute `finiteMarkedGenerators` and absolute
  `marked_saturation_perfect_equivalences`. Neither is the arbitrary-base result.
  The existing slice primitives were found and reused rather than redefined.
- `rg` for the item ID in upstream `WeilConjectures` and `dag/lean_names_upstream.json`
  found no statement already formalizing this node. A direct search for
  `generatorOver|finiteRelativeGenerators` in the upstream source found no separate declaration;
  the landed Q44 declaration in this repository was then reused.
- The existing `lem-coef-finite-relative-lifting-recognition` node was found in the DAG;
  its landed Lean record is the Q44 declaration in
  `Sheaf.AlgebraicTopology.FiniteRelativeLiftingRecognition`, so it is reused rather than
  duplicated or overridden. The helpers are recorded under that owning module.

Validation: the item module and the landed Q44 prerequisite were compiled separately in
dependency order by `scompile.py Q107 lem-coef-relative-cartesian-equivalence-saturation`,
including the private side-project overlay. All compiler passes were clean. Both postponed theorems have full
node-proof docstrings; definitions contain real data and no `sorry`.
The required delivery dry run is recorded below after completion.

## Dependency modules

`lem-coef-finite-relative-lifting-recognition` is the landed Q44 prerequisite, and this
delivery leaves its node JSON and module unchanged. The saturation statement reuses
`Sheaf.AlgebraicTopology.FiniteRelativeLiftingRecognition`, which supplies Q44's
`finiteTestOver` (the slice's canonical `homMk` construction), `finiteRelativeGenerators`
(the four exact relative families), and `finite_relative_lifting_recognition`.
For every `(S : SSet.{u}) (X : Over S)`, its statement is
`(finiteRelativeGenerators S).rlp (toBase X) ↔ IsNaturallyFibrant false X`.
The right lifting problem in the slice against the map from `X` to the terminal sharp
base is precisely a marked diagonal over `S` for the node's `p : X.left ⟶ sharp S`.
The right side is an arbitrary-base Cartesian fibration with exactly its Cartesian edges
marked. No hypothesis on `S` or `X` being a quasicategory, no model structure, and no extra
marked edges are added. Its proof docstring reproduces all five node proof steps.
Its two recorded statement dependencies are public imports; the finite point criterion
and marked triangle cancellation are nonpublic proof imports. The empty-base, point-base,
dimension-one and detector-constant-label checks above also apply to this module.

Delivery dry run completed successfully: `deliver2.py Q107
lem-coef-relative-cartesian-equivalence-saturation --no-push` printed
`OK (dry run): commit 655da208b5 passes the preflight and compiles; nothing pushed.` The retained
second-reading section is unchanged, and nothing was delivered or pushed.

## Earlier second reading (a previous round; superseded)

I reread the item JSON, the landed prerequisite node, the item module and landed prerequisite module, and the
source at HTT Proposition the project server(1), printed pp. 157--159 (especially pp. 158--159),
with Definition A.2.6.12 and Corollary A.2.6.14 on printed p. 826. The node's step-1
inventory and the corresponding Lean are as follows.

- The arbitrary small base is `(S : SSet.{u})`; `SSet.Marked.Over S` is the existing
  `Over S` slice over `sharp S`. No quasicategory, nonempty, or characteristic hypothesis
  is added. Verdict: exact.
- The test class is `weak false`; its definition tests every `Z : Over S` satisfying
  `IsNaturallyFibrant false Z` with `Enhanced.IsWeakHomotopyEquivalence (mapSharpPre g Z)`.
  This is precisely the node's relative sharp mapping test into every naturally marked
  Cartesian fibration. Verdict: exact.
- The assumed fiber criterion is the first implication in the theorem binder:
  `∀ {P Q : Over S} (g : P ⟶ Q), IsNaturallyFibrant false P →
  IsNaturallyFibrant false Q → (weak false g ↔ ∀ s : S _⦋0⦌,
  Enhanced.IsFunctorEquivalence (fiberMap g s))`. The hypotheses are exactly the two
  natural-Cartesian-fibration hypotheses, and `fiberMap` is the recorded strict vertex
  fiber map. Verdict: exact; fiber quasicategory structure follows from the cited relative
  calculus and is not silently assumed as an extra premise.
- The replacement data are `∃ (T : Over S ⥤ Over S) (η : 𝟭 (Over S) ⟶ T)`. For every
  `X`, Lean supplies `∃ Q q, relativeFibration false q ∧ T.obj X =
  cartesianNaturalOver q`, and separately `weak false (η.app X)`. This identifies both
  the underlying map `q : Q ⟶ S` and its natural Cartesian marking, and gives the unit's
  mapping-test property. Verdict: exact.
- `PreservesFilteredColimits T` is the filtered-colimit clause with the input universe
  fixed by the category `Over S`. Verdict: exact.
- The finite-cell choice is represented by `∃ I : Type u, A B : I → Over S, j : ∀ i,
  A i ⟶ B i`, with `finiteRelativeGenerators S = ofHoms j`. For each `X`, Lean gives
  `D : ℕ ⥤ Over S`, an initial isomorphism `e : X ≅ D.obj 0`, a cocone `c`, its colimit,
  `c.pt = T.obj X`, and the equation identifying the initial cocone leg with `η.app X`.
  At every `n`, the two `Cofan`s range over all `Σ i, A i ⟶ D.obj n`; their incidence
  equations and `IsPushout t m (D.map (homOfLE (Nat.le_succ n))) r` state simultaneous
  attachment of every finite generator. Verdict: exact expansion of the node's stated
  sequential finite-cell saturation; the equality and `Nonempty (IsColimit ...)` avoid
  arbitrary chosen colimits.
- The four generator families are rendered by `finiteRelativeGenerators`: all possible
  base maps for inner horns, final marked horns, and the triangle map, and only constant
  vertex labels for `flatToMarked markedEquivalenceDetector`. Verdict: exact.
- The perfectness clauses are rendered separately by `isomorphisms (Over S) ≤ weak false`,
  the three displayed two-out-of-three implications, `IsStableUnderFilteredColimits.{u,u}`,
  and the fixed small `G` with `G.IsSmall.{u}`, `G ≤ weak false`, and filtered-arrow-colimit
  generation. Verdict: all four clauses present with the same quantifier order and no
  extra model-structure assumption.

The prerequisite was also reread. Q44's landed `FiniteRelativeLiftingRecognition.lean` uses the recorded
`cartesianNatural`, `relativeFibration`, `IsNaturallyFibrant`, and existing marked-anodyne
families; its `finite_relative_lifting_recognition` signature is exactly
`(finiteRelativeGenerators S).rlp (toBase X) ↔ IsNaturallyFibrant false X`, matching the
dependency node. Its finite generator definitions contain real constructions and no hollow
data. No dependency module is duplicated or overridden by this delivery.

Edge cases checked independently: `S = ∅` (only the empty slice object and vacuous vertex
criterion), `S = Δ[0]` (the absolute point case), non-quasicategory bases, empty inputs and
empty fibers, `n = 0` (the final-horn family remains the dimension-one generator while inner
horn indices are empty), empty coproduct index types, and the required nonempty filtered
index category in the generation clause. Universes are consistently `u`; no independent
index, site, or morphism universe is introduced. No characteristic, Noetherian, or finiteness
hypothesis appears.

For the one-definition-per-notion check I repeated LeanFinder, LeanSearch, Loogle, and grep
searches over Mathlib, `WeilConjectures/`, and this project's `lean/Sheaf/` for relative
Cartesian equivalence saturation, finite relative generators, and the full theorem name.
Only the existing relative mapping/fibration primitives and the absolute saturation theorem
were found; there is no pre-existing relative saturation statement. The finite lifting
recognition node has Q44's landed Lean record, so that declaration is cited by `stmt_deps` and
is left unchanged in this delivery.

No mismatch was found, so no Lean, node statement, dependency field, or source-based correction
was needed. The only implementation choice checked against the source was replacing its
transfinite presentation by the node's explicitly requested omega-stage simultaneous finite
attachment; finite domains make every lifting map factor through a finite stage, so this is the
stated sequential form and does not add a hypothesis. Both modules were recompiled separately
with `scompile.py`; compilation completed without errors or warnings beyond permitted `sorry`.

## Second reading by Q107

I reread the source at Lurie, *Higher Topos Theory*, Proposition the project server(1), printed
pp. 158–159, including the quotient detector construction, and Definition A.2.6.12 and
Corollary A.2.6.14, printed p. 825. I compared the complete node statement with
`SSet.Marked.Over.relative_cartesian_equivalence_saturation` and with the recorded
finite relative lifting dependency.

The node inventory and Lean verdicts are:

- The input is an arbitrary small simplicial set `S : SSet.{u}`. Lean uses the existing
  `SSet.Marked.Over S` slice over `sharp S`; it adds no quasicategory, nonempty,
  characteristic, Noetherian, or finiteness hypothesis. Verdict: exact.
- The mapping-test class `W_S` is rendered by `weak false`, whose definition tests every
  `Z : Over S` with `IsNaturallyFibrant false Z` using
  `Enhanced.IsWeakHomotopyEquivalence (mapSharpPre f Z)`. The relative calculus identifies
  these targets with naturally marked Cartesian fibrations and their sharp mapping tests.
  Verdict: exact.
- The assumed fiber criterion is the first theorem premise, for every `g : P ⟶ Q` with
  `IsNaturallyFibrant false P` and `IsNaturallyFibrant false Q`, equating `weak false g` with
  `Enhanced.IsFunctorEquivalence (fiberMap g s)` for every vertex `s`. `fiberMap` is the
  recorded strict vertex-fiber map. Verdict: exact, with no extra fiber or model hypothesis.
- The replacement witnesses are `T : Over S ⥤ Over S` and
  `η : 𝟭 (Over S) ⟶ T`. For each `X`, Lean supplies `Q : SSet.{u}`, `q : Q ⟶ S`,
  `relativeFibration false q`, and `T.obj X = cartesianNaturalOver q`, together with
  `weak false (η.app X)`. This identifies the underlying map and the full natural marking.
  Verdict: exact.
- `PreservesFilteredColimits T` gives the filtered-colimit preservation clause at the input
  universe. Verdict: exact.
- The finite-cell data are `I : Type u`, `A B : I → Over S`, and `j : ∀ i, A i ⟶ B i`,
  with `finiteRelativeGenerators S = ofHoms j`. For every `X`, Lean gives an omega diagram
  `D : ℕ ⥤ Over S`, an initial isomorphism, a colimit cocone identified with `T.obj X`, the
  unit equation, and at each stage simultaneous coproduct attachment over every
  `Σ i, A i ⟶ D.obj n`, expressed by the two cofan incidence equations and `IsPushout`.
  Verdict: exact expansion of the node's sequential finite-cell saturation.
- `finiteRelativeGenerators S` is exactly the three all-base-map families (inner horns,
  final marked horns, and the triangle map), plus `flatToMarked markedEquivalenceDetector`
  labelled only by constant maps `SSet.const s`. Verdict: exact source labeling, with no
  nonconstant detector labels or extra Kan generators.
- The perfectness conclusion contains isomorphisms, all three two-out-of-three implications,
  `IsStableUnderFilteredColimits.{u,u} (@weak S false)`, and one fixed small
  `G : MorphismProperty (Over S)` whose arrows filtered-generate every `weak false` arrow in
  `Arrow (Over S)`. Verdict: all four clauses and their quantifier order are present.

The finite relative prerequisite was checked against its node and source: its declaration is
`finite_relative_lifting_recognition (S : SSet.{u}) (X : Over S)`, asserting exactly
`(finiteRelativeGenerators S).rlp (toBase X) ↔ IsNaturallyFibrant false X`; its helper
definitions have real data and no hollow definitions. The item module imports and uses this
landed declaration rather than duplicating it.

Edge cases checked were empty `S` (the slice and vertex quantifier are vacuous), `S = Δ[0]`
(the absolute point specialization), non-quasicategory bases, empty inputs and empty fibers,
the `n = 0` final-marked-horn case, empty attachment coproducts, and the required nonempty
filtered indexing category in the generation clause. All simplicial sets, slice objects,
generator indices, and filtered indices use universe `u`; no independent index universe or
universe equality is imposed. No characteristic or scheme hypotheses occur.

Searches repeated with `msearch.py` (LeanFinder, LeanSearch, Loogle), `rg` over Mathlib,
`WeilConjectures/`, and project `lean/Sheaf/` found no existing relative saturation theorem
or duplicate declaration. They found only the absolute saturation theorem and the relative
mapping/fibration primitives, all of which are reused.

One dependency mismatch was found: the repository node's original `stmt_deps` omitted
`lem-coef-finite-relative-lifting-recognition`, even though the conclusion names its
`finiteRelativeGenerators` definition. I added that prerequisite to the sandbox node copy and
retained the corresponding import; the item statement itself and all other node fields are
unchanged. No source-based statement correction or edge-case repair was needed.

Both sibling modules compiled separately with
`python3 /home/ubuntu/weil-launcher-nt/scompile.py Q107
lem-coef-relative-cartesian-equivalence-saturation`; there were no errors or warnings beyond
the permitted postponed theorem proofs.
