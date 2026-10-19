## Worker report

The module `Sheaf.CategoryTheory.UniversalLocalizationPushout` states
`SSet.Enhanced.isUniversallyLocalizing_pushout_map`, with its entire proof `by sorry`.
The node's natural statement is unchanged. No definitions, new nodes or dependency
repairs are needed. The docstring carries all seven proof steps verbatim from the DAG
(with line wrapping only).

Source checked: [Kerodon Proposition the project server, Tag 02MA](https://kerodon.net/tag/02MA),
read on the containing [section 6.3.5, Tag 02LZ](https://kerodon.net/tag/02LZ).
Its clauses (a), (b), (c) are precisely the two degreewise pushouts, the two
subscript-0 monomorphisms, and the three universally localizing vertical maps.
The node packages clause (a) using the chosen pushouts rather than arbitrary
objects and witnesses for the same colimits. This is the canonical induced-map
form already required by the node.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- Small simplicial sets: `{A₀₁ A₀ A₁ B₀₁ B₀ B₁ : SSet.{u}}`. The explicitly
  declared universes `u v` are arbitrary. `v` is the independent enlargement for
  test quasicategories in the recorded localization predicate; the same pair
  `.{u, v}` occurs in all three assumptions and the conclusion.
- The two spans: `a₀ : A₀₁ ⟶ A₀`, `a₁ : A₀₁ ⟶ A₁`, `b₀ : B₀₁ ⟶ B₀`,
  `b₁ : B₀₁ ⟶ B₁`.
- Their vertical maps: `f₀₁ : A₀₁ ⟶ B₀₁`, `f₀ : A₀ ⟶ B₀`,
  `f₁ : A₁ ⟶ B₁`.
- Strictly commuting map of spans: `h₀ : a₀ ≫ f₀ = f₀₁ ≫ b₀` and
  `h₁ : a₁ ≫ f₁ = f₀₁ ≫ b₁`. These are literal equations of simplicial maps.
- Monomorphism on the subscript-0 A leg: `ha₀ : ∀ n : SimplexCategoryᵒᵖ,
  Function.Injective (a₀.app n)`.
- Monomorphism on the subscript-0 B leg: `hb₀ : ∀ n : SimplexCategoryᵒᵖ,
  Function.Injective (b₀.app n)`. Thus both injectivity hypotheses include degree zero.
- Universal localization on the three vertices: `hf₀₁`, `hf₀`, `hf₁` have the
  respective types `IsUniversallyLocalizing.{u, v} f₀₁`,
  `IsUniversallyLocalizing.{u, v} f₀`, `IsUniversallyLocalizing.{u, v} f₁`.
- The degreewise pushouts and their induced map are the source and target of
  `pushout.map a₀ a₁ b₀ b₁ f₀ f₁ f₀₁ h₀ h₁` from Mathlib. Its full signature and
  defining `pushout.desc` were read in
  `Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean:309`.
  Presheaf colimits are degreewise; the relevant construction and evaluation
  preservation were read in `Mathlib/CategoryTheory/Limits/FunctorCategory/Basic.lean`
  (`pointwiseCocone`, `pointwiseIsColimit`, `functorCategoryHasColimitsOfShape`,
  `evaluation_preservesColimitsOfShape`). Existence is synthesized, not assumed.
- Conclusion: `IsUniversallyLocalizing.{u, v} (pushout.map ...)`, exactly the
  universally localizing induced map in the node.
- The unrestricted legs `a₁`, `b₁` and all three vertical maps have no injectivity
  hypothesis. No quasicategory, Kan, finite, inhabited, or nonempty hypothesis is
  present on any of the six simplicial sets or their pushouts.

Dependencies read and reused:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`: its module and all definitions
  were read, notably `SSet.Enhanced.IsFunctorEquivalence`, `fullSubcomplex`,
  `AreNaturallyEquivalent` and the coherent diagram/cone constructions; Mathlib's
  `SSet` and `SimplexCategory` are the underlying simplicial objects and degree category.
- `Sheaf.CategoryTheory.UniversallyLocalizingSimplicialMap`:
  `SSet.Enhanced.IsUniversallyLocalizing`, `IsLocalizationAtEdges` and
  `edgeInvertingDiagrams`. The full definitions and docstrings were read.
  Universal localization quantifies over all small base changes, chooses edges
  before the test target, and uses coherent functor equivalences into targets in
  `SSet.{max u v}`. Neither input is assumed a quasicategory.
- Proof-only imports, as mandated by stage 2:
  `Sheaf.CategoryTheory.EnhancedFunctorConeCalculus`
  (`SSet.Enhanced.enhanced_functor_cone_calculus`),
  `Sheaf.CategoryTheory.IsofibrationExponentiation`
  (`SSet.Enhanced.isofibration_exponentiation`),
  `Sheaf.CategoryTheory.IsofibrationPullbackLimit`
  (`SSet.Enhanced.isofibration_pullback_limit`),
  `Sheaf.CategoryTheory.InfinityMappingComposition`
  (`SSet.Enhanced.mapping_composition`), and
  `Sheaf.CategoryTheory.InfinityTerminalPullbackCriterion`
  (`SSet.Enhanced.infinity_terminal_pullback_criterion`).
- The proof node `lem-coef-universal-localization-degenerate-edges` has no `lean`
  record in the read repository and hence no module to import. It is cited in the
  proof docstring for its later stage-3 use. It is not needed to type this statement.

Edge cases checked before writing:

- Empty overlap gives the coproduct map; both injectivity assumptions are automatic
  on empty domains, and no nonemptiness premise prevents this case.
- All six simplicial sets may be empty, or all maps identities. The assertion then
  specializes to universal localization of the corresponding identity map.
- Either unrestricted span leg may collapse several vertices or edges. The only
  injectivity premises are `ha₀` and `hb₀`, so this case remains included.
- Vertical maps may collapse simplices (for example contractible-factor projections);
  no accidental `Mono` or bijectivity requirement is imposed on them.
- Arbitrary non-quasicategorical shapes (for example simplex boundaries) are allowed;
  only the target categories quantified inside the dependency are quasicategories.
- The degree-zero injectivity tests and arbitrary target enlargement were checked
  explicitly against the dependency. There is no index universe below `u` and no
  equality imposed between `u` and `v`.

Searches for an existing declaration (all negative for this exact gluing theorem):

- `msearch.py grep`: query `localiz.*pushout|pushout.*localiz`; 15 hits. Candidates: `Mathlib/AlgebraicGeometry/Sites/SmallAffineZariski.lean`, `Mathlib/AlgebraicGeometry/QuasiAffine.lean`, `Mathlib/RingTheory/LocalProperties/Basic.lean`, `Mathlib/Algebra/Category/Ring/Constructions.lean`, `Mathlib/Algebra/Category/Ring/Constructions.lean`, `Mathlib/RingTheory/Localization/BaseChange.lean`, `Mathlib/RingTheory/Localization/BaseChange.lean`, `Mathlib/RingTheory/Localization/BaseChange.lean`.
- `msearch.py loogle`: query `SSet, pushout, IsUniversallyLocalizing`; 0 hits. loogle: unknown identifier 'pushout' Candidates: .
- `msearch.py leanfinder`: query `Universal localization of simplicial sets preserved by pushout gluing along monomorphisms in both spans`; 8 hits. Candidates: `SSet.instIsStableUnderCobaseChangeMonomorphisms`, `SSet.modelCategoryQuillen.J`, `SSet.modelCategoryQuillen.I`, `SSet.Subcomplex.BicartSq.isPushout`, `SSet.instIsStableUnderFilteredColimitsMonomorphisms`, `SSet.horn₂₂.isPushout`, `SSet.modelCategoryQuillen.J_le_monomorphisms`, `SSet.horn₂₀.isPushout`.
- `msearch.py leansearch`: query `Pushout gluing of universally localizing maps of simplicial sets`; 8 hits. Candidates: `SSet.horn₂₂.isPushout`, `CategoryTheory.Limits.pushoutIsPushout`, `CategoryTheory.Limits.pullback.desc'`, `SSet.Subcomplex.BicartSq.isPushout`, `CategoryTheory.IsPushout.of_hasPushout`, `CategoryTheory.Limits.PushoutCocone.IsColimit.desc'`, `HomotopicalAlgebra.AttachCells.isPushout`, `CategoryTheory.Limits.Types.Pushout.cocone`.
- `msearch.py loogle`: query `CategoryTheory.Limits.pushout.map`; 12 hits. Candidates: `CategoryTheory.Limits.pushout.map_id`, `CategoryTheory.Limits.pushout.map`, `CategoryTheory.Limits.pushout.congrHom_hom`, `CategoryTheory.Limits.pushout.congrHom_inv`, `CategoryTheory.Limits.pushout.map_isIso`, `CategoryTheory.Limits.pushout.map_comp`, `CategoryTheory.Limits.pushout.map_comp_assoc`, `CategoryTheory.Limits.op_pullbackMap`.

The LeanFinder hits are monomorphism stability, horns and ordinary simplicial
pushout primitives. LeanSearch similarly returns pushout constructors and
universal properties. Loogle's corrected fully qualified query locates the canonical
`pushout.map`, which is used, but no localization assertion. The grep hits concern
ring localization and are unrelated. `CategoryTheory.Functor.IsLocalization` was
read in `Mathlib/CategoryTheory/Localization/Predicate.lean:54`: it concerns ordinary
categories and is not this universal simplicial localization.

Direct `rg -n` searches for
`IsUniversallyLocalizing|universally.localizing|universal_localization_pushout|localiz.*pushout|pushout.*localiz`
in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
`/home/ubuntu/weil-newtargets-shared/lean/Sheaf` found the recorded definition,
proof-plan references in `FiniteEmbeddedSimplexResolution`, and unrelated ring
or model-localization material, with no matching theorem.
The item-id search in upstream `WeilConjectures` and the name search in
`dag/lean_names_upstream.json` found no declaration. No duplicate is introduced.

No statement faults or disputed clauses were found. No file outside this sandbox
was edited; compilation uses the prescribed wrapper only.

Validation: the prescribed `scompile.py Q27 lem-coef-universal-localization-pushout`
compiled this file cleanly (sandbox 2.0 s, library 2.1 s). The required
`deliver2.py Q27 lem-coef-universal-localization-pushout --no-push` printed
`OK (dry run)` and confirmed compilation and server preflight, except for the
independent second reading which the designated second worker will write.
Nothing was pushed. The dry run staged exactly the module, node copy and report.


## Second reading by Q27

I independently read the sandbox node and module, both recorded statement-dependency
nodes and their actual Lean definitions, and Kerodon subsection 6.3.5, Tag 02LZ,
including Proposition the project server (02MA) and Definition the project server (02M0). The source here
is Kerodon, not Stacks; its containing section imposes no additional global
hypotheses. The direct 02MA page timed out, but the containing 02LZ page includes
the complete proposition, diagram and proof. No mathematical mismatch was found.

The following is my inventory of the node's statement, matched with the Lean.
All rows pass.

| Object, hypothesis or conclusion in the node | Lean rendering and verdict |
| --- | --- |
| Six small simplicial sets, with no quasicategory condition | `{A₀₁ A₀ A₁ B₀₁ B₀ B₁ : SSet.{u}}`; Mathlib's actual simplicial sets, arbitrary `u`, with no extra instances. Pass. |
| The first span | `(a₀ : A₀₁ ⟶ A₀) (a₁ : A₀₁ ⟶ A₁)`; both legs are arbitrary simplicial maps at introduction. Pass. |
| The second span | `(b₀ : B₀₁ ⟶ B₀) (b₁ : B₀₁ ⟶ B₁)`; the same shape and orientation. Pass. |
| The map on the three span vertices | `(f₀₁ : A₀₁ ⟶ B₀₁) (f₀ : A₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁)`; no injectivity or equivalence presumed. Pass. |
| Strict commutation on the 0 leg | `h₀ : a₀ ≫ f₀ = f₀₁ ≫ b₀`; equality of simplicial maps with the required endpoints. Pass. |
| Strict commutation on the 1 leg | `h₁ : a₁ ≫ f₁ = f₀₁ ≫ b₁`; the other commutative square, with no homotopy substituted for equality. Pass. |
| Monomorphic 0 leg of the first span | `ha₀ : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (a₀.app n)`; exactly degreewise injection. Pass. |
| Monomorphic 0 leg of the second span | `hb₀ : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (b₀.app n)`; the required second monomorphism. Pass. |
| Universal localization of the overlap map | `hf₀₁ : IsUniversallyLocalizing.{u, v} f₀₁`; the recorded predicate. Pass. |
| Universal localization of the 0 map | `hf₀ : IsUniversallyLocalizing.{u, v} f₀`; same predicate and universes. Pass. |
| Universal localization of the 1 map | `hf₁ : IsUniversallyLocalizing.{u, v} f₁`; same predicate and universes. Pass. |
| Degreewise pushouts of both spans | `pushout a₀ a₁` and `pushout b₀ b₁`, as the source and target of `pushout.map`; the presheaf colimits exist without an added hypothesis. Pass. |
| Canonically induced map, universally localizing | `IsUniversallyLocalizing.{u, v} (pushout.map a₀ a₁ b₀ b₁ f₀ f₁ f₀₁ h₀ h₁)`; the argument order sends both summands and the overlap through their specified vertical maps. Pass. |
| No injectivity on the other legs or vertical maps; no quasicategory assumption on any shape | There are no other binders or instances. Pass. |

I opened `Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.lean:309`:
`pushout.map` is the actual `pushout.desc` with components
`f₀ ≫ pushout.inl _ _` and `f₁ ≫ pushout.inr _ _`, with `h₀,h₁` proving
compatibility. Thus it is not an arbitrary map between the two colimit objects.
I also read `pointwiseCocone`, `pointwiseIsColimit`,
`functorCategoryHasColimitsOfShape` and `evaluation_preservesColimitsOfShape` in
`Mathlib/CategoryTheory/Limits/FunctorCategory/Basic.lean`. They justify that these
are the node's degreewise pushouts. The source's arbitrary pushout squares and
the node's chosen-pushout formulation agree through the unique colimit isomorphisms;
the node itself explicitly requests the induced map between these pushouts.

For the meaning of localization, I read all three definitions in
`Sheaf.CategoryTheory.UniversallyLocalizingSimplicialMap`. In particular,
`IsUniversallyLocalizing` quantifies over `T : SSet.{u}` and `g : T ⟶ B`, then
chooses `W`, then invokes `IsLocalizationAtEdges`. That last predicate quantifies
over every `E : SSet.{max u v}` with `Quasicategory E` and requires an actual
restriction factorization equation and `IsFunctorEquivalence`. The edge collection
therefore cannot vary with `E`. The map is the pullback projection in the correct
direction. The degreewise `ULift` permits arbitrary test-target enlargement;
there is no independent smaller target universe or equality imposed on `u,v`.

I also opened the relevant definitions in
`Sheaf.CategoryTheory.EnhancedDiagramsCones`: `IsEquivalenceEdge`, `fullSubcomplex`,
`AreNaturallyEquivalent` and `IsFunctorEquivalence`. The latter gives a genuine
simplicial quasi-inverse with coherent equivalences of both composites.
`edgeInvertingDiagrams` reuses `EnrichedMarkedRealization.invertingDiagrams`,
whose actual definition is the full subcomplex defined by the images of marked
edges being equivalences. Its separate `IsEdgeLocalization` requires the target
shape to be a quasicategory, so it cannot replace this dependency's predicate for
arbitrary shapes. There is no private duplicate or hollow datum in this delivery.
No new nodes, sibling modules or dependency repairs are present or needed.

Edge cases checked: empty overlap (coproducts); all objects empty; identity maps;
a collapsing unrestricted leg; noninjective vertical maps; and shapes that are
not quasicategories. All remain in the statement. The empty-to-nonempty vertical
map is not accidentally declared localizing: it must satisfy the substantive
`hf` premise. Degree zero is included by quantification over all objects of
`SimplexCategoryᵒᵖ`, as are all higher dimensions. There is no numerical,
characteristic, ring, finiteness or nonemptiness restriction. The six small
objects may all lie in any common universe, and the same arbitrary enlargement
is used in every localization hypothesis and the conclusion.

Independent duplicate searches (with different wording from the worker):

- `msearch.py ... leanfinder "Gluing localization functors of simplicial sets across two pushout squares with injective horizontal maps"`: eight hits, including `SSet.instIsStableUnderCobaseChangeMonomorphisms`, `SSet.Subcomplex.BicartSq.isPushout`, horns and `SSet.hasColimits`. These provide simplicial pushout or monomorphism facts, not the asserted gluing of universal localizations.
- `msearch.py ... leansearch "A commutative cube of simplicial sets with monomorphic pushout faces preserves universal localization"`: eight hits. The candidates concern commutative-ring localization pushouts, ordinary-category localization, and monomorphism stability; none states this theorem.
- `msearch.py ... loogle "CategoryTheory.Limits.pushout.map"`: twelve hits. I read the actual constructor; its functoriality and isomorphism lemmas do not assert this localization property.
- `msearch.py ... grep 'universally.?localiz|[Ll]ocaliz.*[Gg]lu|[Gg]lu.*[Ll]ocaliz'`: three hits about gluing localized structure sheaves; no match.
- Direct `rg` of the same conceptual expressions, this item's id, and the declaration name in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, its Mathlib, the shared `lean/Sheaf`, and `dag/lean_names_upstream.json`: no duplicate theorem. The relevant project hits are the localization definition and the finite embedded simplex resolution's proof-plan reference. Ring and sheaf gluing hits concern different objects. I read `CommRingCat.isPushout_of_isLocalization` and `CategoryTheory.Functor.IsLocalization` to exclude those candidates explicitly.

The module's only theorem has precisely `by sorry`; nothing is proved in the
delivery, and it introduces no definitions. Both docstrings give the correct
source and blueprint id. All seven DAG proof texts occur in the theorem
docstring verbatim after whitespace and TeX-escaping normalization. I checked the
proof-dependency records: all recorded modules are imported, while
`lem-coef-universal-localization-degenerate-edges` still has no Lean record and
is correctly retained as a proof-plan citation. There is no repair note for this
item and no `statement_change`, so no correction/citer audit is required.

The node copy differs from the shared node only in `lean`. Its `lean.statement`
is verbatim equal to the complete theorem signature in the file. There are no
lines over 100 characters, no file-local notation or instances, and no unbound
variable or universe: `u,v` are declared and every object is an explicit or
implicit binder. No Lean or node edit was needed; the only second-reading change
is this report section.

Validation: the prescribed `scompile.py` with the absolute sandbox file path
compiled the single delivered module cleanly in both sandbox (1.8 s) and library
(2.2 s) modes, with no errors or warnings. An initial relative path was resolved
against the read-only project cwd and found no file; rerunning with the actual
sandbox path succeeded. This was an invocation correction, not a compiler failure.
