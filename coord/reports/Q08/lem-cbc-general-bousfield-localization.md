## Worker report

The module `Sheaf.CategoryTheory.GeneralBousfieldLocalization` states
`HomotopicalAlgebra.GeneralBousfield.general_bousfield_localization`. Its only theorem
has proof `sorry`. The three real, proof-free predicate definitions introduce exactly
the local objects, local equivalences, and derived precomposition test used by this
node; no model structure or arbitrary map is selected from an existence assertion.
The node statement is unchanged. There are no new nodes or dependency repairs.

Source checked: Barwick, *On left and right model categories and left and right
Bousfield localizations*, Scholium 3.64, Definition 4.2 and Theorem 4.7,
printed pp. 41--44, at
https://webhomes.maths.ed.ac.uk/~cbarwick/papers/complete.pdf.
The theorem's docstring gives all ten proof steps from the node, including
recognition, the transfinite limit argument, both fibrancy implications, and the
unenriched Quillen universal property.

Hypotheses and terminology, matched clause by clause:

- The size convention is represented by explicit object/hom universes `u`, `v` and
  independent target universes `u'`, `v'`. `I : Type v` is any small set in the bound
  used for local presentability and both generating families; `s : I → Arrow M`
  includes empty families, repetitions and arbitrary endpoints.
- A model category is `[m : ModelCategory M]`, with `[HasLimits M] [HasColimits M]`
  for completeness and cocompleteness. Mathlib supplies two-out-of-three,
  retract closure and the two weak factorization systems.
- `_hM : CombinatorialModelCategory.{u, v, v} M` is the dependency's existing
  structure: local presentability, small generating families, and both functorial
  factorizations. The presentability and generators use the same small universe.
- `_hLeft : (weakEquivalences M).IsStableUnderCobaseChangeAgainst (cofibrations M)`
  is exactly pushout of a weak equivalence along a cofibration, with no endpoint
  cofibrancy condition. This uses Mathlib's existing relative pushout-stability notion.
- `IsFrameOrthogonal m f Z` renders equivalence of the derived precomposition map.
  It quantifies over cofibrant `Xc,Yc`, weak-equivalence augmentations
  `pX : Xc ⟶ X`, `pY : Yc ⟶ Y`, frames `A,B`, and frame maps `a` satisfying
  `a.app ⦋0⦌ ≫ eqToHom B.degree_zero ≫ pY =
  eqToHom A.degree_zero ≫ pX ≫ f`. Naturality along the unique map `[n] → [0]`
  extends this equation to the complete augmentation square. The test is the
  actual `SSet.Enhanced.IsWeakHomotopyEquivalence (frameHomPre a Z)`.
  For fibrant `Z`, the dependency's `hom_kan`, `comparison` and `frame_naturality`
  identify precisely this map with derived precomposition, conjugated by the
  equivalences induced by `pX,pY`. The test is therefore independent of all choices.
  It is not vacuous: functorial cofibrant replacement followed by the functorial
  relative Reedy frame construction gives compatible frame maps for every arrow.
  Concretely, factor the degree-zero left Kan extension into the constant object,
  fixing degree zero; both functorial factorizations in `_hM` make this natural
  on arrows, as in the frame theorem's proof step 2.
- `IsLocal m s Z` is `IsFibrant Z ∧ ∀ i, IsFrameOrthogonal m (s i).hom Z`.
  Thus fibrancy is original fibrancy and every member of S is tested.
- `localEquivalences m s` tests `IsFrameOrthogonal m f Z` for every `Z` satisfying
  that exact original fibrant-local-object predicate. Higher homotopy information
  is retained; this is not ordinary Hom-set orthogonality.

Conclusions, matched clause by clause:

- `∃ L : ModelCategory M` gives a structure on the same underlying category.
- `@CombinatorialModelCategory ... L` asserts combinatoriality for that structure
  and includes its two functorial factorizations. The following relative
  pushout-stability conjunct asserts left properness of `L`.
- Equality of the `L` and `m` cofibration projections gives the original cofibrations.
- Equality of `L`'s weak-equivalence projection with `localEquivalences m s`
  gives exactly the stated S-equivalences.
- `∀ Z, L.categoryWithFibrations.fibrations (terminal.from Z) ↔ IsLocal m s Z`
  gives exactly the originally fibrant S-local objects, in both directions.
- The existential `R : M ⥤ M`, `η : 𝟭 M ⟶ R` has localized trivial-cofibration
  components and localized fibrant values: the specified functorial fibrant replacement.
  Both model factorizations are already part of localized combinatoriality.
- The next two conjuncts say the identity preserves old cofibrations and old
  trivial cofibrations, respectively. The identity adjunction is canonical.
- The last clause quantifies over every complete and cocomplete target model
  category `T`, any functors `F,G`, and the unchanged ordinary adjunction `F ⊣ G`.
  Its two old preservation hypotheses are exactly the definition of left Quillen.
  There is no enrichment, properness, combinatoriality or functorial-factorization
  hypothesis on `T`.
- `Q,ε` range over old functorial cofibrant replacements; their hypothesis is
  cofibrancy of `Q.obj X` and an old weak-equivalence augmentation. Such replacements
  exist by `_hM`. Thus this does not restrict the Quillen adjunction being tested.
  `IsIso ((weakEquivalences T).Q.map (F.map (Q.map (s i).hom)))` is precisely
  invertibility of `LF(s i)` in the ordinary localization at target weak equivalences.
  Using all choices of `Q` makes no choice of a total derived functor part of the data.
- Its two final preservation conclusions are exactly the assertion that the same
  adjunction is Quillen from `L` to `T`. Every source class is an explicit projection
  of `m` or `L`, so binding `L` cannot silently change the model for locality or LF.

Dependency declarations read and used:

- `def-weil-size-convention`: a recorded metatheoretic convention, with no module
  or declaration; implemented by the explicit universe binders above.
- `Sheaf.CategoryTheory.CombinatorialLocalizationPresentability`,
  `HomotopicalAlgebra.ModelLocalization.combinatorialLocalizationPresentability`:
  read its signature and complete docstring. Its public imports provide the recorded
  `HomotopicalAlgebra.CombinatorialModelCategory` from
  `Sheaf.CategoryTheory.ModelColimitLocalizationComparison`, whose five fields were
  also read directly. The presentability theorem itself is not assumed as an extra
  hypothesis; this node uses the combinatorial terminology attached to it.
- `Sheaf.CategoryTheory.CosimplicialFrameMapping`,
  `CategoryTheory.cosimplicial_frame_mapping`, `CategoryTheory.CosimplicialFrame`,
  `CategoryTheory.frameHomPre`, and the `comparison`, `hom_kan`, `frame_naturality`
  fields of `CosimplicialFrameMappingData`: these are the existing actual framed
  mapping spaces and their derived-precomposition characterization.
- Mathlib's `MorphismProperty.IsStableUnderCobaseChangeAgainst`,
  `ModelCategory`, `MorphismProperty.Q`, `Functor`, `Adjunction`, `IsIso`,
  `Cofibration` and `WeakEquivalence` supply the remaining standard notions.
- Proof-only imports retain the available DAG plan: lifting/retract closure,
  transfinite lifting, accessible small-object factorization, Smith recognition,
  detection of old weak equivalences, derived adjunctions and the fibrant Quillen test.
  `lem-cbc-homotopy-local-equivalences-accessible` and
  `lem-cbc-left-proper-derived-cell-colimits` have no module recorded on the base,
  so there is no module to import for those proof-only nodes. They remain in
  `proof_deps` and are explicitly cited in the complete proof docstring.

Edge cases checked: S empty (local means original fibrant and S-equivalences are
old weak equivalences by the derived Yoneda criterion); identity/invertible arrows;
noncofibrant sources and targets; empty mapping spaces; repeated generators;
arbitrary small infinite families; and targets with unrelated object and morphism
universes. No finite, countable, nonempty or simplicial restriction was introduced.
For the frame test, naturality at `[n] → [0]` proves that degree-zero compatibility
really does fix the represented original arrow in every degree. Terminal/initial
objects chosen by either model encode the same invariant fibrancy/cofibrancy notions.

Searches for existing declarations:

- `msearch.py`, LeanFinder: "A left proper combinatorial model category admits left
  Bousfield localization at a small set of maps without simplicial enrichment".
  Eight hits: ordinary cofibrant-object homotopy localization and ordinary reflective
  Bousfield localization, not existence of this model structure.
- `msearch.py`, Loogle: `ModelCategory, IsLeftProper`. Zero hits; the endpoint reported
  unknown identifier `ModelCategory`.
- `msearch.py`, LeanSearch: "Left Bousfield localization of a combinatorial model
  category has the same cofibrations and local fibrant objects". Eight hits, including
  `ObjectProperty.isLocal` and ordinary reflective-localization facts. Read
  Mathlib `CategoryTheory/Localization/Bousfield.lean`: these use Hom-set bijections,
  not homotopy function complexes, and do not construct model structures.
- `msearch.py`, grep: `Bousfield|IsLeftProper|CombinatorialModelCategory` in
  `CategoryTheory`. Sixteen ordinary localization-related hits, no model theorem.
- Direct `rg` in Mathlib ModelCategory and MorphismProperty found the standard
  model structure and `IsStableUnderCobaseChangeAgainst` used above, but no general
  Bousfield model existence theorem.
- Direct `rg` in `WeilConjectures` and `lean/Sheaf/CategoryTheory` for
  `Bousfield|IsLeftProper|CombinatorialModelCategory|IsLocalObject|localEquivalences`,
  and item-id search in `WeilConjectures`: no upstream item match. The two existing
  `BousfieldLocalFibrations` and `BousfieldQuillenDescent` modules were read in full:
  both assume an existing localized structure and a simplicial source; neither states
  this existence theorem. Their enriched `IsLocal` has a different domain, so it
  cannot replace the unenriched framed test here.
- Search over DAG bindings and project modules found no existing `GeneralBousfield`
  declarations. No independent notion was missing: all three predicates are the
  terminology explicitly introduced by the item's own statement.

Validation: the prescribed `scompile.py` wrapper compiled the sandbox and module
successfully, with no errors or warnings (2.4 s and 2.1 s). Every universe and variable
is explicitly bound; all lines are at most 100 characters. Definitions contain no
postponed data or proofs. Only the named node theorem has `sorry`.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
