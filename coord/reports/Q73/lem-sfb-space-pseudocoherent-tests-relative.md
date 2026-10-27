## Worker report

The item module `Sheaf.AlgebraicGeometry.SpacePseudoCoherentTestsRelative` states
`AlgebraicGeometry.AlgebraicSpace.isPseudoCoherentRelativeTo_of_pseudoCoherent_tensor_tests`.
Its only theorem proof is `sorry`. The additional definition module introduces the
space-relative predicate using the existing scheme predicate, without postponed data.
The source is Stacks Tag 0CTT, spaces-more-morphisms.tex,
`lemma-characterize-pseudo-coherent`, read together with Tags 0CSY and 0CSX.
The source and item's mathematical statement agree; no correction is needed.

Clause-by-clause correspondence:

- A commutative ring is `A : CommRingCat.{u}`; `X : AlgebraicSpace (Spec A)` and
  `f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec A)))` give the specified morphism to Spec A.
  The existing `schemeSpace` is the represented fppf sheaf, not another space model.
- Separatedness is `_hsep : MapIsSeparated f`, exactly representability of the relative
  diagonal by closed immersions. Finite presentation is the three conjuncts of `_hfp`:
  quasi-compactness of f, quasi-compactness of its diagonal (quasi-separatedness), and
  local finite presentation on every compatible pair of etale scheme charts.
- `K : X.DerivedQCoh` is an object of the full subcategory of the unbounded derived
  module category with quasi-coherent cohomology. It does not require the representative
  terms themselves to be quasi-coherent or bounded.
- `_htests : ∀ E : X.DerivedModules, X.IsPseudoCoherent E → ...` ranges over every
  pseudo-coherent E in the ambient category. It adds no perfectness, boundedness,
  quasi-coherence or flatness hypothesis on E. `X.IsPseudoCoherent` is the existing
  covering-sieve predicate with locally bounded-above finite-free representatives.
- `X.derivedDualityModel.closed.tensor.obj (E, K.obj)` is the existing normalized
  K-flat derived tensor, in the order E tensor K stated by the node.
- `affineDerivedSections A (Over.mk (𝟙 (Spec A))) (Iso.refl _) X f` is the existing
  A-linear K-injective RΓ. It retains the A-action pulled back along f, rather than
  forgetting to abelian groups. `DerivedCategory.IsPseudoCoherent` on its value is
  precisely a bounded-above complex of finite free A-modules up to derived isomorphism.
- The conclusion `IsPseudoCoherentRelativeTo f K` unfolds to every integer m and then
  every U in X.EtaleSite, V in the target.EtaleSite, every scheme map h : U → V with
  `U.obj.hom ≫ f.hom.hom = yoneda.map h ≫ V.obj.hom`. These are exactly the etale
  vertical maps and commutative squares in the node. `derivedSchemeRestriction X U K.obj`
  is the existing right-derived restriction to Zariski opens. On D_QCoh this is the
  scheme object corresponding to exact etale restriction. Scheme relative
  m-pseudo-coherence is the recorded `Scheme.IsMPseudoCoherentRelativeTo`, with
  pointwise affine neighbourhoods, finite affine-space closed embeddings, and
  m-pseudo-coherent derived direct image. Its existential choices remain inside m.
- The definition's `∃ hf : LocallyOfFiniteType h.left, ...` supplies the proof argument
  required by the scheme predicate. On the specified locally finite type domain this
  is automatic by the chart definition. Here local finite presentation in `_hfp`
  implies it for every h. It is not an additional theorem assumption.
- Explicit u, w, wZ retain the section size and independent localization morphism sizes.
  The scheme HasDerivedCategory family supplies the categories needed for all charts,
  affine spaces and restrictions. No equality of w and wZ is imposed. No flatness,
  properness or Noetherian assumption occurs.

Dependency declarations used (their source and full signatures were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `EtaleSite`, `etaleForget`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `AlgebraicSpace.QCoh`,
  using Mathlib's `SheafOfModules.IsQuasicoherent` unchanged.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `DerivedQCoh`, `derivedQCohProperty`, `derivedSchemeRestriction`, `derivedDualityModel`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsSeparated`,
  `MapIsLocallyOfFinitePresentation`; the inherited `MapIsQuasiCompact` is used for f
  and its relative diagonal.
- `Sheaf.AlgebraicGeometry.SpaceAffineGlobalSections`: `affineDerivedSections`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex`: `IsPseudoCoherent`.
- `WeilConjectures.RingTheory.RingPseudoCoherent`: `DerivedCategory.IsPseudoCoherent`.
- `Sheaf.AlgebraicGeometry.RelativePseudoCoherentComplex`:
  `Scheme.IsMPseudoCoherentRelativeTo`, `Scheme.IsPseudoCoherentRelativeTo`.
- `Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses` and
  `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses` are public dependency imports.
  Their H0/abelian-group and perfect-package declarations provide contextual notions;
  the tensor test uses the already available A-valued whole derived sections, not H0.
- `def-weil-size-convention` is a metatheoretic convention with no importable declaration.

All recorded proof-dependency modules are imported without `public`. Those not yet
recorded are not re-stated: lem-sfb-qcqs-space-pushforward-right-adjoint,
lem-sfb-etale-pseudocoherence-descent, lem-sfb-space-qcqs-derived-projection-formula,
lem-sfb-projective-space-pseudocoherence-twist-test,
lem-sfb-flat-ambient-relative-pseudocoherence, and
lem-sfb-space-relative-pseudocoherence-etale-locality. The theorem docstring carries all
8 proof steps and these node references for stage 3. Existing proof imports are the
Chow-neighbourhood, projective twists, flat-proper direct image, scheme pseudo-coherent
QCoh, etale/Zariski equivalence, derived QCoh pullback/tensor, derived pushforward
composition and Chow transform-restriction modules.

Edge cases checked before writing: A may be the zero ring, X may be empty, K and E may
be zero, m ranges over all integers (including negative degrees), and no common global
bound on local models or finite atlas is required. Empty covering sieves are available
where appropriate. No nonempty index, positive rank or nonzero ring assumption is added.
The scheme definition includes zero-dimensional affine space. Charts are not restricted
to a smaller independent universe that could make the tests vacuous.

Searches for an existing theorem or notion:

- msearch LeanFinder: "Pseudo coherent global tensor tests imply relative pseudo
  coherence for a separated finitely presented algebraic space over a ring": 8 scheme
  separated/finite-presentation results, no derived tensor criterion.
- msearch Loogle: `AlgebraicGeometry.AlgebraicSpace.IsPseudoCoherent,
  AlgebraicGeometry.Scheme.IsPseudoCoherentRelativeTo`: 0 hits, unknown project identifier.
- msearch grep `IsPseudoCoherentRelativeTo|pseudo.?coherent.*tensor` in
  Mathlib/AlgebraicGeometry: 0 hits.
- msearch LeanSearch: "Relative pseudo coherence of complexes on algebraic spaces defined
  on all etale scheme charts": 8 general etale scheme/ring results, no relative predicate.
- msearch LeanFinder: "Definition of m pseudo coherent relative to a base for a derived
  quasi coherent object on an algebraic space using every etale square of schemes":
  8 results (etale sites/morphisms and local finite presentation), no matching definition.
- msearch grep `IsMPseudoCoherentRelativeTo|IsPseudoCoherentRelativeTo` in all Mathlib:
  0 hits. The exact results and date are recorded in the new node.
- rg of WeilConjectures/ and Sheaf/ for the relative predicate names found only the
  scheme and ring predicates and their consumers. rg of the item id in WeilConjectures/
  found no declaration. The already available space pseudo-coherence, tensor, sections,
  and scheme relative predicate are reused.
- DAG title/statement search found relative-locality statements, but no definition node
  for space-relative pseudo-coherence. `tools/blueprint_refs.py search 'relative pseudo'`
  returned 0 blueprint nodes. This new id did not already exist.

Validation: both delivered modules compiled separately through scompile.py against the
published server library, with no errors or warnings. Definitions have real terms and
there are no auto-bound variables (`set_option autoImplicit false`).

## New nodes

`def-sfb-space-relative-pseudo-coherent-complex` defines the fixed-degree and all-degree
relative predicates from Stacks Tags 0CSY (definition) and 0CSX (every etale square).
It is built on `derivedSchemeRestriction` and `Scheme.IsMPseudoCoherentRelativeTo`.
The explicit chart finite-type witness supplies the scheme definition's proof argument;
it is automatic on the source's locally finite type domain. No extra approximation,
functor or chosen map is introduced. The three searches above, project rg, DAG search
and blueprint search found no existing space-level definition. The item additionally
cites the landed owner nodes of the existing tensor/category calculus, scalar sections,
morphism properties, pseudo-coherence and scheme-space embedding it uses.

## Second reading by Q73

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
