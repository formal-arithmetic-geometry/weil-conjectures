## Worker report

The module `Sheaf.CategoryTheory.HomotopyLocalEquivalencesAccessible` states
`CategoryTheory.homotopy_local_equivalences_accessible`, with `sorry` as its entire proof.
It defines three real predicates belonging to the notions introduced by this node:
`derivedPrecompositionIsEquivalence`, `IsHomotopyLocalObject`, and
`homotopyLocalEquivalences`. There are no new nodes, dependency repairs, statement changes,
or disputed statements. The only change to the original node is `lean`.

Source read: [Barwick, On Left and Right Model Categories and Left and Right Bousfield
Localizations](https://webhomes.maths.ed.ac.uk/~cbarwick/papers/complete.pdf), printed p. 43,
Lemmas 4.5 and 4.6; also Definition 4.2 and Notation 3.61 on printed pp. 40 and 42.
Lemma 4.6 assumes combinatoriality and a small localizing set. Left properness appears
in the subsequent existence theorem, Theorem 4.7, and is not imposed here. The module's
proof docstring gives all six steps of the expanded DAG proof, including accessible
cofibrant replacement, framed local replacement, detection of original weak equivalences
between local objects, and the accessible inverse-image argument.

Hypotheses and clauses, matched to Lean:

- The size convention is metatheoretic. Explicit `u v t` allow `M : Type u` with
  `Category.{v} M` and the coherent localization in `SSet.{max u v t}`. Small sets,
  small diagrams, and accessibility cardinals all use `v`, as in the recorded ordinary
  accessibility interfaces. There is no equality of object and morphism universes.
- A combinatorial model category with functorial factorizations is
  `[ModelCategory M] [HasLimits M] [HasColimits M]` and
  `_hM : CombinatorialModelCategory.{u, v, v} M`. That existing structure includes
  local presentability, small generating families for both left classes, and both
  functorial factorization properties; no extra cofibrant-generation axiom is added.
- The original homotopy function complexes are represented by a localization
  `q : FiniteReedy.largeNerve M ⟶ K`, with
  `_hq : FiniteReedy.IsLocalization (weakEquivalences M) q`. The quasicategory condition
  is already part of `_hq`. These binders specify the original derived mapping spaces
  already present in the informal statement, rather than a localized model structure.
- A small set of arrows is expressed by `{I : Type v} (S : I → Arrow M)`. An indexed
  family and its image set impose precisely the same tests; any small set can be
  enumerated by its subtype. Repetitions impose no additional condition.
- To express `Map^h(Y,Z) → Map^h(X,Z)` without a noncanonical strict composition law,
  `derivedPrecompositionIsEquivalence q f Z` tests the actual simplicial map induced
  by `frameEvaluation K 0` on mapping spaces from the diagram `q(f)` to the constant
  arrow at `qZ`. The other evaluation, at 1, canonically identifies this source space
  with `Map_K(qY,qZ)`: maps of arrows from `qX → qY` to `id(qZ)` are exactly maps
  `qY → qZ`, including all coherent homotopies. Under this equivalence evaluation at
  0 is precomposition by `q(f)`. Thus its weak homotopy equivalence is exactly the
  required derived precomposition equivalence. This uses precisely the evaluation
  span of `FrameMappingRelation`, with the other arrow degenerate, and the same
  `SSet.Enhanced.mappingSpace` and `IsWeakHomotopyEquivalence`. It does not test only
  components or ordinary Hom sets, and it contains no arbitrary map witness.
- Originally fibrant and S-local is
  `IsHomotopyLocalObject q S Z := IsFibrant Z ∧ ∀ i, ... (S i).hom Z`.
  The original instance `[ModelCategory M]` is the only model instance in scope.
- Membership in W_S is `homotopyLocalEquivalences q S f`, universally testing
  `derivedPrecompositionIsEquivalence q f.hom Z` for every such local `Z`.
  This is an `ObjectProperty (Arrow M)`, hence defines the full subcategory with
  all ambient commuting squares as its morphisms.
- Repleteness is `(homotopyLocalEquivalences q S).IsClosedUnderIsomorphisms`.
- One infinite regular cardinal is `∃ (κ : Cardinal.{v}) (_ : Fact κ.IsRegular)`.
  Mathlib `Cardinal.IsRegular` includes `aleph0_le`; its regularity is equivalent
  to the union-size condition in the node (see `Cardinal.sum_lt_of_isRegular`).
- Lambda-filteredness is `IsCardinalFiltered J κ`. Its definition quantifies over
  functors with fewer than κ arrows and asserts a cocone, exactly the node's convention.
- Ambient closure is the first conjunct under that existential: for every small
  κ-filtered `D : J ⥤ Arrow M` with all objects in W_S and every ambient colimit
  cocone `c`, the apex `c.pt` is in W_S. The colimit is in the original arrow category.
- Small generation is `∃ (A : Type v) (G : A → Arrow M)`, all `G a` in W_S, and
  for each member `f` a small κ-filtered diagram `D`, with objects isomorphic to
  generators, an ambient colimit cocone, and an isomorphism `c.pt ≅ f`.
  Repleteness makes the isomorphism form identical to generation under those colimits.
  It uses the same κ as closure. No presentability-at-the-generating-rank clause is added.
- No left properness, simplicial enrichment, or cofibrancy of S's endpoints is bound.

Dependency declarations read and reused:

- `def-weil-size-convention`: its record is explicitly a convention without a Lean
  declaration. Universe binders implement it.
- `Sheaf.CategoryTheory.CombinatorialLocalizationPresentability`:
  `HomotopicalAlgebra.ModelLocalization.combinatorialLocalizationPresentability`;
  its imported `Sheaf.CategoryTheory.ModelColimitLocalizationComparison` defines
  `HomotopicalAlgebra.CombinatorialModelCategory`, used directly here.
- `Sheaf.CategoryTheory.CosimplicialFrameMapping`:
  `CategoryTheory.cosimplicial_frame_mapping`, `CosimplicialFrameMappingData`,
  `FrameMappingRelation`, `frameEvaluation`, and `frameQEdge`. The original coherent
  mapping spaces and canonical action span, including the full naturality signature,
  were read; the helpers reuse the latter two actual constructions directly.
- Their original localization interface is
  `HomotopicalAlgebra.FiniteReedy.IsLocalization`, from
  `Sheaf.CategoryTheory.FiniteReedyLocalization`. Its definition includes the full
  coherent functor-category universal property, not just the homotopy category.
- Stated proof prerequisites are imported without `public`:
  `AccessibleArrowInverseImage.accessible_arrow_inverse_image` (in namespace
  `CategoryTheory`), `AccessibleSmallObjectFactorization`'s
  `CategoryTheory.MorphismProperty.exists_accessible_functorial_factorization`,
  `LocalizationHomotopyCategory`'s `SSet.Enhanced.localization_homotopy_category`,
  `ModelLocalizationDetectsWeakEquivalences`'s
  `HomotopicalAlgebra.modelLocalization_weakEquivalence_iff_isIso`, and
  `ModelWeakEquivalencesAccessible`'s `CategoryTheory.model_weak_equivalences_accessible`.
  The expanded accessibility conclusion follows the last and inverse-image signatures.
  Mathlib's lifting-property and transfinite-composition modules supply the recorded
  mathlib matches of the two lifting-closure proof dependencies. The framed localizing
  cofibration prerequisite currently has no recorded module, so it is mentioned in the
  proof plan but has no import. It is a proof dependency, not a statement dependency.

Edge cases checked before writing and again after compilation:
empty I (local means every originally fibrant object), repeated localizing arrows,
identity arrows, originally weak arrows, and noncofibrant endpoints are all admitted.
The test for an identity arrow is evaluation from maps between constant arrows and is
an equivalence. Empty mapping spaces are tested by weak homotopy equivalence, including
bijection on components; no inhabited-space premise is hidden. Small diagrams have no
extra nonemptiness assumption; κ-filteredness itself implies the required nonemptiness.
The object universe u and mapping-space enlargement t are independent of v. Colimit
closure quantifies over every cocone satisfying `IsColimit`, not an arbitrary apex.

Searches made (all with item `lem-cbc-homotopy-local-equivalences-accessible`, group Q09):

- `msearch.py ... leanfinder "Local equivalences for a small set of morphisms in a
  combinatorial model category form an accessible accessibly embedded subcategory
  of the arrow category"`: eight hits, chiefly
  `MorphismProperty.isCardinalAccessible_ι_isLocal`,
  `MorphismProperty.isLocallyPresentable_isLocal`, and ordinary presentability.
  Read `Mathlib/CategoryTheory/Presentable/OrthogonalReflection.lean`: it tests ordinary
  Hom-set orthogonality, not the derived function-complex condition. No exact match.
- `msearch.py ... loogle '"ModelCategory", "Accessible"'`: zero hits.
- `msearch.py ... grep 'localEquivalence|local.*equivalence.*accessib|Bousfield.*accessib'`:
  zero Mathlib hits.
- `msearch.py ... leansearch 'homotopy local equivalences form an accessible subcategory
  of arrows'`: eight hits on original weak equivalences, the inclusion of cofibrant
  objects, and generic accessible categories; no derived local-equivalence theorem.
- `rg` in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, with
  `LocalEquivalence|localEquivalence|HomotopyLocal`, and the exact item id: no matching
  declaration. Searched new full names there, in Mathlib, and `dag/lean_names_upstream.json`;
  no collision.
- `rg` in `lean/Sheaf` with `CombinatorialModelCategory|localEquivalence|LocalEquivalence`
  and with `mappingSpace.*[Pp]re|precomp|preComp`: found the recorded combinatorial
  structure and `CategoryTheory.BousfieldLocalization.IsLocal/localEquivalences` in
  `Sheaf.CategoryTheory.BousfieldLocalFibrations`. Read their full declarations: they
  require `[SimplicialCategory M]` and an enriched replacement functor. They cannot
  express the unenriched statement here. This is why no private duplicate of that
  specialized definition is used. The new predicates are the general notions
  introduced by the item's own statement and are listed in `lean.declarations`.
- Read the existing `AccessibleArrowInverseImage` and `ModelWeakEquivalencesAccessible`
  statements: they supply the exact ambient-closure and small-generation formulation,
  but neither states this derived local-equivalence theorem.

Validation: prescribed `scompile.py Q09 lem-cbc-homotopy-local-equivalences-accessible
<module>` passed for both sandbox and library-path checks (1.8 seconds each), no errors
or warnings. Every theorem proof is exactly `sorry`; definitions have real terms.
The absent framed-localizing-cofibrations statement requires no assumption or extra
module in this stage-2 statement. No other DAG node is stated.

## Second reading by Q09

Author's second pass, with the node and completed module open; the maintainer supplies
the independent review under this dispatch protocol. Matched the model/factorization
conventions to the existing combinatorial structure, the original mapping-space test
to the canonical source-evaluation leg, original fibrancy to `IsFibrant`, and both
universal local-object tests to the definitions. Matched repleteness to the Mathlib
object-property class, and the same existential regular κ to ambient colimit closure
and the small generator presentations. Verified the κ-filtered definition counts
arrows and the regular-cardinal definition includes infinitude. Re-read the mapping
span in `FrameMappingRelation`: the direction is source evaluation from q(f) to id(qZ),
so it tests precomposition, not postcomposition. The target evaluation is the canonical
equivalence to Map(qY,qZ), with no arbitrary comparison choice. All arrows of S and f
have unrestricted endpoints. No statement mismatch or change was found. The natural
statement, dependency list, proof and other node fields remain unchanged. All new
helpers belong to this item's stated notions and carry this node's source/blueprint tag.
