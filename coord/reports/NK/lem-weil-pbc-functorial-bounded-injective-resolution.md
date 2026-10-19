## Worker report

The module `Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution` states
`CochainComplex.exists_functorial_bounded_injective_resolution`, with its proof `sorry`.
It introduces no new definition. The node is unchanged outside `lean`.

Hypotheses and clauses, in order:

- An abelian category is `{C : Type u} [Category.{v} C] [Abelian C]`, with independent
  explicitly declared object and morphism universes.
- The supplied functorial embedding is `(J : C ⥤ C) (η : 𝟭 C ⟶ J)`.
  `hη : ∀ A : C, Mono (η.app A)` expresses its monomorphic components;
  `hJ : ∀ A : C, Injective (J.obj A)` expresses injectivity of every target.
  No additivity or zero-preservation of the supplied J is assumed.
- The category of bounded-below integer cochain complexes is Mathlib's `Plus C`:
  `(CochainComplex.plus C).FullSubcategory`, where `plus C K` is
  `∃ n : ℤ, K.IsStrictlyGE n`. It retains all chain maps between these objects.
- `∃ (I : Plus C ⥤ Plus C)` is the one replacement endofunctor.
- `α : Plus.ι C ⟶ I ⋙ Plus.ι C` is the natural augmentation in the ambient complex
  category. The inclusion is fully faithful, so this equally expresses the natural
  transformation from the identity to I in the full subcategory, without introducing
  another natural-transformation definition or additional data.
- `∀ K : Plus C, QuasiIso (α.app K)` gives the natural quasi-isomorphism at every K.
- `∀ (K : Plus C) (n : ℤ), Injective (((I.obj K).obj).X n)` gives every injective term.
- `∀ (K : Plus C) (a : ℤ), K.obj.IsStrictlyGE a → (I.obj K).obj.IsStrictlyGE a`
  expresses preservation of every lower bound. Mathlib's `isStrictlyGE_iff` identifies
  this with `∀ n < a, IsZero (K.X n)`, i.e. termwise vanishing, not just cohomology.
- The existential functor and augmentation precede all K and a quantifiers. Since
  I is a functor on the whole category, any diagram F is resolved by F ⋙ I and its
  augmentation by whiskering α with F. Thus no separate common-bound, shape, size,
  or diagram hypothesis is imposed, and no mere objectwise choice replaces naturality.

Dependency declarations inspected and used:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`, imported through DerivedCategory.Basic.
- `def-sp-injective-resolutions`: `CategoryTheory.Injective`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`. Also read the complete
  `InjectiveResolution` structure in Preadditive.Injective.Resolution; it resolves
  single objects and is not the replacement functor of this node.
- `def-weil-abstract-derived-category`: `Mathlib.Algebra.Homology.DerivedCategory.Basic`;
  its underlying Mathlib `CochainComplex` and `QuasiIso` notions are used. No localized
  derived object occurs here, so no HasDerivedCategory hypothesis is needed.
- The existing Mathlib `CochainComplex.Plus`, `Plus.ι` and `IsStrictlyGE` are imported
  from `Mathlib.Algebra.Homology.CochainComplexPlus`. These are specializations of
  the complexes in the preceding dependency; there is no private replacement notion.
- Proof imports: `Sheaf.CategoryTheory.DoubleComplexTotal` for
  `def-sp-double-complex-total`, and `Sheaf.Algebra.Homology.FirstQuadrantAugmentation`
  for `HomologicalComplex₂.quasiIso_of_column_augmentation`.

Source checked: `literature/stacks-project/derived.tex`,
`lemma-functorial-injective-resolutions` (Tag 0141), assertion (1) and its proof.
The normalization J(0)=0, recursive cokernels, and total-complex construction there
justify the simultaneous termwise bound preservation. The declaration docstring
includes all eight proof steps, including the expanded functoriality verification
and the first-quadrant reduction recorded in the node.

Edge cases checked before writing: the zero complex has every integer lower bound
and must therefore have zero output terms in every degree; the normalized construction
has this property. A nonzero J(0) is allowed as input and is normalized in the proof.
A complex may have any negative or positive integer lower bound. Different objects
in a diagram may have arbitrarily different bounds; neither Plus nor the conclusion
chooses a common bound. Empty total diagonals are zero and injective. A zero abelian
category is allowed. No countable coproduct assumption, enough-injectives assumption,
Grothendieck assumption, or additivity of J has been added.

Searches (2026-10-15):

- `msearch.py ... leansearch 'Functorial injective resolution of bounded below complexes
  preserving lower bounds'`: unavailable (Internal Server Error), recorded as unavailable.
- `msearch.py ... leanfinder 'Functorial injective resolutions of bounded below complexes
  preserving every lower bound'`: eight hits, mostly `InjectiveResolution.of_def`,
  object-resolution injective-term instances and right-derived-functor statements;
  none gives the required endofunctor on all bounded-below complexes.
- `msearch.py ... loogle '"InjectiveResolution"'`: twelve hits describing object
  resolutions and their morphisms; no strictly functorial, bound-preserving resolution
  of complexes.
- `msearch.py ... grep 'functorial.*injective|injective.*functorial'`: twenty hits,
  primarily concrete-category factorizations; the injective-resolution functor lands
  in the homotopy category and resolves objects, not the present statement.
- Local Mathlib rg for Plus, bounded-below and IsStrictlyGE found and reused
  CochainComplexPlus.lean and Embedding/CochainComplex.lean. Read their definitions,
  the full signatures/docstrings of the recorded dependency declarations, and
  `isStrictlyGE_iff`.
- Local rg of the source project's WeilConjectures for functorial/injective patterns
  found GrothendieckAbelian/KInjectiveResolution and KInjectiveResolutionInjective.
  Read their APIs: they assume a Grothendieck abelian category and resolve unbounded
  complexes; they do not assert simultaneous preservation of termwise lower bounds.
  Exact blueprint-id search in the source project returned no hit.
- Local rg of `lean/Sheaf` for bounded injective resolutions and functorial injectives
  found objectwise bounded-below resolution statements, ringed-site K-injective
  resolutions, and embeddings for specific categories. None states this general
  bound-preserving endofunctor from a supplied functorial injective embedding.

No statement correction, new node, dependency repair, or statement dispute is needed.


## Second reading by NK

Independent review against the sandbox node, its eight proof steps, Stacks
`derived.tex`, Tag 0141 (`lemma-functorial-injective-resolutions`), the surrounding
section, and `homology.tex`, `definition-functorial-injective-embedding`.
The source's arrow-category section is equivalently an endofunctor with a natural
monomorphic embedding. Neither source imposes additivity on that functor.

Object/hypothesis/conclusion checklist, in node order:

1. Abelian category A: `{C : Type u} [Category.{v} C] [Abelian C]`. PASS.
   Read Mathlib.CategoryTheory.Abelian.Basic: the class extends Preadditive and
   normal mono/epi categories, with finite products, kernels and cokernels.
   This is the recorded def-sp-abelian notion, including its derived zero object.
2. Functorial embedding: `(J : C ⥤ C) (η : 𝟭 C ⟶ J)` and
   `hη : ∀ A : C, Mono (η.app A)`. PASS: η's naturality supplies exactly the
   commutative squares of the arrow-category formulation; there is no extra
   zero-preservation, additivity or exactness assumption.
3. Injective targets: `hJ : ∀ A : C, Injective (J.obj A)`. PASS.
   Opened the dependency's Injective class in Preadditive.Injective.Basic:
   its factors field extends every map along every mono. Also read
   Preadditive.Injective.Resolution's InjectiveResolution structure; that
   object-resolution structure is not the replacement functor required here.
4. All bounded-below integer cochain complexes: `Plus C`. PASS.
   Read CochainComplexPlus: Plus is the full subcategory for the predicate
   `∃ n : ℤ, K.IsStrictlyGE n`, not complexes with a chosen common bound.
   Its inclusion `Plus.ι C` retains every chain map. Opened the recorded
   DerivedCategory.Basic dependency: it uses exactly CochainComplex C ℤ and
   its quasi-isomorphisms. Its localization-size assumption is unnecessary
   here because the conclusion is entirely in complexes, before localization.
5. One replacement functor: `∃ (I : Plus C ⥤ Plus C)`. PASS. Both its domain
   and codomain are the required full category; output boundedness is bundled.
6. Natural quasi-isomorphism: `(α : Plus.ι C ⟶ I ⋙ Plus.ι C)` and
   `∀ K : Plus C, QuasiIso (α.app K)`. PASS. The fully faithful inclusion
   identifies this with an augmentation inside Plus. Read QuasiIso's class:
   it requires isomorphisms on homology in every degree, as the node requires.
7. Every output term injective: `∀ (K : Plus C) (n : ℤ),
   Injective (((I.obj K).obj).X n)`. PASS: all integers, not merely nonnegative
   degrees, and the same I as in the augmentation.
8. Preservation of every lower bound: `∀ (K : Plus C) (a : ℤ),
   K.obj.IsStrictlyGE a → (I.obj K).obj.IsStrictlyGE a`. PASS.
   Read Embedding.CochainComplex.isStrictlyGE_iff: this is IsZero of every
   term in degree i < a, rather than merely cohomological vanishing.
9. The same I for all bounds and diagrams: both I and α are quantified before
   K, n and a. PASS. For any diagram F into Plus, F ⋙ I and the augmentation
   obtained by whiskering α provide exactly the diagram statement, without
   restricting its indexing universe or requiring a common lower bound.

Edge cases: the zero complex satisfies every lower bound, so the conclusion
forces every output term to be zero, consistent with normalization J(0)=0 in
Tag 0141. A supplied J with nonzero J(0) is allowed and normalized in the proof.
The zero abelian category is allowed. All a, including zero and negative bounds,
are covered. An empty diagram has its unique whiskered augmentation; infinite
diagrams with unboundedly varying lower bounds are allowed. Finite diagonal
support includes empty diagonals (zero, hence injective). The independent
universes u and v are explicitly bound; there is no smallness, countable
coproduct, Grothendieck, field, characteristic or scheme hypothesis. Scheme and
characteristic edge cases introduce no separate conditions in this abstract node.

Independent reuse searches:

- msearch leanfinder: "Natural replacement endofunctor on bounded below complexes
  by complexes of injective objects with unchanged lower vanishing bounds".
  Eight hits. Opened cm5b.I: its differential is zero and it is not a natural
  quasi-isomorphic resolution; its bound-preservation instance is insufficient.
  K-injectivity criteria and object resolutions do not assert this theorem.
- msearch loogle: the initial query `"Plus" "Injective"` was rejected by the
  query parser (not evidence of absence). The valid `"injectiveResolutions"`
  query returned five hits. Opened CategoryTheory.injectiveResolutions:
  C maps to HomotopyCategory C (up ℕ), resolving objects only up to homotopy,
  not an endofunctor on integer complexes preserving all termwise bounds.
- msearch grep: `resolutionFunctor|injectiveReplacement|functorial_injective`
  returned no hits. Independently rg searched Mathlib's homology and injective
  directories, the upstream WeilConjectures tree, and this project's lean/Sheaf
  for resolution/functor and bounded/injective word pairs. Inspected upstream
  kInjectiveResolutionFunctor, toKInjectiveResolution and its injective-term
  instance: these use IsGrothendieckAbelian and have no preservation of termwise
  lower bounds. The leftResolution/minusResolutionFunctor material has opposite
  variance/direction and no theorem with the present input and conclusion.
  No exact existing declaration was found; the module should remain.

No new definition node or dependency module is included or needed (H12/H13).
Read the imported DoubleComplexTotal and FirstQuadrantAugmentation declarations:
these supply the recorded totalization and first-quadrant augmentation proof
inputs with the same abelian category and commuting bicomplex conventions.
The declaration docstring follows all eight node proof steps, including the
normalization, retract argument, recursive cokernels, exact columns, natural
bicomplex, finite total diagonals, reindexing and simultaneous bound argument.
Its source and blueprint marker are present. One theorem with a sorry proof,
no data definitions or hidden local notions. No mismatch found and no Lean or
node change made; this independent review is the only addition.

Validation: the node's lean.statement equals the complete file signature
verbatim. All universes and variables are explicitly bound. The single delivered
module compiled cleanly through scompile.py on the server (1.0 s; nice 19;
two threads; default 60-second limit), with no warnings or errors.
