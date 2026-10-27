## Worker report

The module `Sheaf.CategoryTheory.Sites.AcyclicBasisCohomology` states
`CategoryTheory.RingedSiteAcyclicBasis.exists_acyclicBasisCohomology`, with one
`sorry`, and five fully defined helpers for this very comparison. No other DAG
node, statement, proof plan, or dependency record is changed.

Source read: `literature/stacks-project/sites-cohomology.tex`, Tag 0BKZ,
`lemma-cohomology-over-U-trivial`, statement and complete proof (lines 5466–5503),
and the preceding Tag 0D6P statement. The source proves the unbounded result by
the lower truncation tower, not an unbounded spectral sequence. The formal
normalization uses the actual quotient of cycles, rather than an arbitrary
isomorphism. This characterizes the same bounded spectral-sequence edges and
therefore their stabilized composite.

Hypothesis and clause mapping:

- A ringed site is `C : Type c`, `[Category.{v} C]`,
  `J : GrothendieckTopology C`, and `R : Sheaf J RingCat.{max c v r}`.
  `_hcomm` says every section ring is commutative. Encoding commutativity as a
  property of the underlying ring sheaf changes no ring, action, or object.
- `c`, `v`, `r`, `w` are explicitly declared independent universes. The module
  universe is `max c v r`; `[HasSheafify J AddCommGrpCat.{max c v r}]` and
  `[J.WEqualsLocallyBijective ...]` expose Mathlib's sheafification structures,
  which exist for this relatively small site. The size-convention node has no
  mathematical definiendum; these universe/size binders are its implementation.
  No equality of site object and morphism universes is assumed.
- The module category is the dependency's `ringedSiteModules.{max c v r} R`,
  transparently Mathlib's `SheafOfModules`. Its morphisms are the sectionwise
  linear maps and its restriction maps are the existing semilinear maps.
- `[HasDerivedCategory.{w} ...]` and the universally quantified `K` use the
  recorded unbounded `DerivedCategory`, not a bounded subcategory. Its
  `DerivedCategory.homologyFunctor` supplies the kernel/image cohomology sheaf.
- `B : Set C` and `_hB` assert that every object admits a covering presieve
  whose domains lie in B: `Sieve.generate S ∈ J U`. A covering family need not
  be closed under precomposition; requiring every domain of the generated
  sieve to be in B would have strengthened the hypothesis and is avoided.
- `IsAcyclicOn R B K` states the exact displayed vanishing for every U in B,
  every p > 0 and every integer q. It computes derived evaluation on every
  K-injective quasi-isomorphism `H^q(K)[0] ⟶ I`, with the existing
  `CochainComplex.IsKInjective` and `QuasiIso`. The target is the homology of
  `SheafOfModules.evaluation R (op U)` applied termwise, so its coefficient ring
  is exactly R(U). Quantifying all models is the choice-independent form of
  the node's evaluation on a K-injective representative. Resolutions exist by
  the recorded existence theorem; this predicate is not vacuous.
- `sectionCohomology R q` is cohomology of the underlying presheaf-module
  complex; `cohomologySections R q` is the underlying presheaf of the actual
  cohomology module sheaf. Evaluation of the first is canonically the
  cohomology of the evaluated complex, since presheaf evaluation is exact.
  Thus no ordinary (underived) evaluation of an arbitrary K is substituted
  for derived evaluation: the isomorphism assertion explicitly requires a
  K-injective model I of the given derived object K.
- The conclusion quantifies a unique family `α` of natural transformations
  between those two functors. Its first clause says that the actual cycle
  quotient followed by α is the image of the sheaf cycle quotient. The real
  kernel isomorphism `sectionCyclesIso` identifies the cycle objects. Since
  the presheaf homology quotient is epic, this fixes α uniquely. There is no
  choice of an unconstrained map or unspecified data from a sorry theorem.
- `modelEdge` composes α with the inverse of the standard
  `DerivedCategory.homologyFunctorFactors` and H of the chosen model
  isomorphism `e : Q I ≅ K`. For every K satisfying the hypothesis, every
  K-injective I and every such e, its component at every U in B is `IsIso`.
  This is an isomorphism in `ModuleCat R(U)`; `asIso` supplies the requested
  linear isomorphism and its linear inverse. All models and their comparison
  isomorphisms are included, rather than a selected representative only.
- Naturality in K is the third conjunct: for every derived a, any chain map f
  representing a between any two models, and every q, the square for
  `modelEdge` commutes. The K-injective Hom bijection ensures every derived
  map is represented in this manner when the models are K-injective.
- Restriction compatibility is built into the type of `modelEdge`: it is a
  morphism of the existing `PresheafOfModules R.obj`, whose naturality field
  is the restriction square after restriction of scalars. This includes all
  V → U in B, and uses R(U) → R(V), not a constant coefficient ring.
- The fourth conjunct explicitly uses
  `DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))`. For `1-q ≤ n` it asserts
  that H^q of the evaluated model map of this projection is an isomorphism on
  B, and that the model-edge square commutes. In this range H^q(c_n) is also
  the canonical cohomology isomorphism. Solving the square identifies the edge
  for K with the bounded-below edge after the truncation projection. Any two
  n compare through their maximum, giving exactly the eventually constant
  limit construction of 0BKZ. The cycles equation fixes the bounded edges as
  the column-zero spectral-sequence comparisons, without adding arbitrary
  spectral-sequence data to the hypotheses.
- The last conjunct is literally an identity on the underlying module
  presheaf of M: the canonical identification M with cycles of M[0], followed
  by the cycle quotient, α in degree zero, and the standard H^0(M[0]) ≅ M,
  equals `𝟙`. Naturality with the resolution M[0] → I gives precisely the
  derived degree-zero normalization, also when M[0] is not K-injective.

Dependency declarations used/read:

- `def-weil-size-convention`: its convention-only record; explicit universes
  and the chosen derived localization above, not a duplicate definition.
- `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`;
  Mathlib `SheafOfModules`, `SheafOfModules.forget`, and
  `SheafOfModules.evaluation` (full signatures and module docstrings read).
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`; `DerivedCategory.homologyFunctor` and
  `homologyFunctorFactors` in `...DerivedCategory.HomologySequence`.
- `def-pur-kinjective-complex` is a Mathlib leaf, without a lean record:
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`,
  `CochainComplex.IsKInjective`, defined by null homotopy of every map from
  an acyclic complex. Used directly, with no copied predicate.
- `prop-pur-kinjective-resolutions-exist`:
  `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
  Its complete signature and proof docstring were read: it supplies the
  Grothendieck structure and all functorial, degreewise injective resolutions,
  with independent site universes.

Every recorded proof-dependency module is imported, using its current record:
Mathlib's K-injective Hom bijection, `Sheaf.CategoryTheory.KInjectiveComputes`,
`Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`, upstream
`WeilConjectures.CategoryTheory.TruncationHypercohomology`,
`Sheaf.CategoryTheory.SiteTruncationDerivedLimit`,
`Sheaf.CategoryTheory.Sites.RGammaDerivedLimit`, upstream
`WeilConjectures.CategoryTheory.DerivedLimitRoosAbelianGroups`, and upstream
`...Triangulated.MilnorBoundaryFactorization` and `...MilnorProjectionFactorization`.
The proof docstring follows all nine inherited proof steps, combining the
bounded-edge calculation and its transition compatibility in steps 2 and 7.

Edge cases checked before drafting: zero K and the zero sheaf; every positive,
zero and negative q; n=0 when 1-q ≤ 0; the empty category; B empty on a site
where empty coverings suffice; zero section rings; a genuinely varying
commutative ring sheaf; nonidentity arrows between basis members; arbitrary
unbounded K; noninjective M in the degree-zero assertion. None is excluded by
an accidental boundedness or constant-ring assumption. The empty-basis case
makes the basis isomorphism claims vacuous, while the uniquely normalized raw
comparison and the single-sheaf identity remain meaningful.

Searches actually run:

- `msearch.py ... leanfinder "unbounded ringed site acyclic basis cohomology"`:
  8 hits, including `CategoryTheory.Sheaf.H`, `Sheaf.cohomologyPresheaf`,
  `CochainComplex.IsKInjective`, and derived-category support facts; no match
  for the unbounded, module-valued, canonical acyclic-basis comparison.
- `msearch.py ... loogle "SheafOfModules, CochainComplex.IsKInjective"`:
  0 hits.
- `msearch.py ... grep "acyclic.*basis|basis.*acyclic|derivedEvaluation|derivedSections"
  CategoryTheory`: 0 hits.
- `msearch.py ... grep "acyclic.*basis|basis.*acyclic|hypercohomology"`:
  0 hits.
- `rg` on the prescribed live `lean/WeilConjectures` and `lean/Sheaf` trees for
  acyclic/basis and derived-evaluation terms found the generic site limit
  infrastructure and scheme/affine-basis specializations. The upstream
  `AffineBasisKInjectiveSectionsPreservesHomology` and
  `KInjectiveSectionCycleComparison` were opened: the former is specific to
  scheme affine opens; the latter assumes a derived truncation is invertible,
  rather than proving this from a covering basis. Neither states this node.
- Searching the item id in upstream `lean/WeilConjectures` found no declaration.
  Searching all six proposed names in the existing site directories found no
  declaration with the proposed full namespace names.
- Reading Mathlib's module-sheaf, presheaf-module, homology-preservation and
  single-homology sources supplied the exact existing kernel, quotient,
  evaluation and restriction operations used here.

Validation: `scompile.py Q24 lem-sfb-ringed-site-acyclic-basis-cohomology
<module>` compiled both the sandbox and library module cleanly (3.8 s and
3.4 s respectively in the final direct compile). Initial diagnostics were
unresolved max-universe inference in helper applications, repaired by explicit
universe arguments, and then line wrapping, repaired without changing the
mathematical interfaces. No diagnostic commands remain. No statement dispute,
node correction, new node or dependency repair was needed.

## Second reading by Q24

This is the worker's final self-reading; the dispatcher explicitly forbids
starting another agent, and the maintainer supplies the independent review.
I reopened the node and module and checked the correspondence above. The main
checks were that sections retain their actual coefficient ring; that all
integer cohomology degrees and all K-injective representatives occur; that the
cover hypothesis uses a presieve rather than demanding a downward closed B;
that α is uniquely characterized by cycles, instead of an arbitrary family of
isomorphisms; that its presheaf type includes the semilinear restriction
squares; and that the actual derived lower truncation projections and the
identity for a noninjective sheaf M are both present. The additional explicit
truncation conjunct was added during this reading to make the stabilized-limit
clause directly reviewable. The only admitted proof is the named main theorem;
all helper data are explicit compositions or existing universal constructions.
