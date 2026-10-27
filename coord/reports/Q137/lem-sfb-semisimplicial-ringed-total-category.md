## Worker report

The delivery states `CategoryTheory.SemisimplicialRingedTotal.semisimplicial_ringed_total_category`
in `Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory`. Its sole postponed proof is
that theorem. All helper definitions contain real data. Structures package the input data
or the simultaneous witnesses of this node; none postulates a missing construction as an
extra theorem hypothesis. There are no statement changes, dependency repairs or new nodes.

Sources read: Stacks `spaces-simplicial.tex`, Case A and
`lemma-simplicial-site-site` (09WC), `lemma-describe-sheaves-simplicial-site-site`
(09WF), `lemma-restriction-to-components-site` (09WG),
`lemma-augmentation-site` (0D70), and
`lemma-restriction-module-to-components-site` (0D72). The semisimplicial adaptation
is the one in the accepted node, including the all-arrow equalizer for augmentation,
not the simplicial two-arrow equalizer. The current blueprint search found no imported
unit stating this supporting lemma. The accepted eight-step proof is reproduced in the
main theorem's docstring, including the K-flat representative argument for the canonical
composition maps.

Hypotheses and clauses, in order:

1. The finite nonempty ordinal index is Mathlib `SemiSimplexCategory`: its object
   `mk n` has underlying order `Fin (n+1)` and `homEquiv` identifies its arrows with
   order embeddings. There are no degeneracy maps. The input `F` and `D` use
   `CoherentSitePseudofunctor SemiSimplexCategoryᵒᵖ F`, exactly the recorded total-site
   dependency. That structure includes the covering axioms, continuity, preservation
   of covering pullbacks, and the actual pseudofunctor unitors and compositors.
   The `geometric` binder says that each recorded `D.inverseImage a` preserves finite
   limits, precisely the extra morphism-of-sites hypothesis of the systems dependency.
   Sites and coefficient sheaves are in universe `u`, with module/derived objects in
   the larger universe `u+1`. `Site.hasDerived` uses Mathlib's actual standard
   localization in that universe. No boundedness is imposed on complexes.
2. `RingDiagram.presheaf` records the given coherent ring data as a commutative-ring
   presheaf on the Grothendieck category, with only `fibre_sheaf` assumed. This is the
   adjoint presentation of the input: at `(i,U)` its value is `O_i(U)`; restriction
   along `(a,id)` is the adjoint structural ring map, and along `(a,f)` additionally
   restricts in the source fibre. Functoriality is exactly the identity/composition
   coherence, not an extra condition on the diagram. The theorem concludes the total
   sheaf condition `h`; it is not assumed. `R.total h` is consequently the specified
   ringed total site and `R.fibre i` is the given fibre ringed site.
3. `R.Systems` is the full subcategory of `PresheafOfModules` over that actual ring
   presheaf consisting of presheaves whose fibre restrictions are sheaves. Its
   objects are precisely module sheaves in each fibre with semilinear transitions.
   `PresheafOfModules` includes the semilinearity and composition equations on every
   arrow. Its morphisms are precisely linear natural maps, equivalently compatible
   component maps. `Presentation.equivalence` and `forget_eq` assert the equivalence
   with total module sheaves, fixed over the presheaf forgetful functor. Thus it
   cannot be an equivalence with an unrelated abstract system category.
4. `Presentation.face`, `face_inverse`, `face_direct`, `face_adjunction` and
   `face_ring` identify the ringed face morphisms with the dependency's actual sheaf
   adjunction and the ring restriction along the Cartesian lift. `Pullback.algebraic`,
   `ringMap`, `structural`, `object_eq` and `map_eq` identify ordinary module pullback
   with inverse image followed by the existing sheafified scalar extension
   `changeOfRings`, namely `O_i tensor_(f^-1 O_j) f^-1 M`. The adjunction is fixed on
   underlying sheaves and its insertion is explicitly `m ↦ 1 tensor m` via
   `ringedComparisonScalarSection` and `insertion_one`. `transition_restriction`
   says that the transpose of the linear transition is exactly the actual
   semilinear restriction, after forgetting to set sheaves. `transition_id` and
   `transition_comp` are its identity and cocycle with canonical comparisons inserted.
5. `evaluation_eq` fixes evaluations as component restriction under the equivalence.
   `Evaluation` carries additivity and preservation of finite limits and finite
   colimits; these structures are outputs. `conservative` expresses joint
   conservativity on every morphism. `Evaluation.derived` is definitionally the
   actual exact functor's `mapDerivedCategory`; its existing
   `mapDerivedCategoryFactors` computes it termwise. The exact-derived-functor
   dependency identifies this same functor with both left and right derived
   evaluation. The ringed fibre maps `fibreMap`, with their actual restriction
   formulas and identity structural map, have module inverse image equal to these
   evaluations (`fibre_evaluation`).
6. `derivedTransition` is a natural transformation for every face. Its
   `derived_representative` equation fixes it on every flat-term K-flat total
   complex by localizing the actual transition chain map, using the exact-evaluation
   and left-derived-pullback comparisons. `Pullback.flat_computation` and
   `preserves_flat` use the recorded flat/K-flat notions. `Composition.insertion`
   fixes ordinary tensor reassociation, and `Composition.representative` fixes the
   canonical derived compositor on those representatives. `Identity` fixes the
   identity comparison similarly. `derived_id` and `derived_comp` give the compatible
   derived system on every derived total object; no essential-surjectivity claim
   for arbitrary derived systems is introduced.
7. `Presentation.IsCartesian` is defined as invertibility of every constructed
   derived transition. `cohomology_criterion` assumes exactness of every face module
   pullback, expressed by preservation of finite limits and colimits, and gives the
   iff with invertibility of `transition a` on
   `DerivedCategory.homologyFunctor ... q` for every integer `q`. These are the actual
   cohomology total modules, not independent chosen component objects.
8. `Augmentation` quantifies over an arbitrary small ringed site `S` and arbitrary
   ringed-topos component morphisms `map i`. Its comparison, ring, identity and
   composition fields are exactly coherent augmentation data. They do not require
   morphisms of the presented sites. For every such datum the theorem supplies
   `AugmentationPresentation`: its `map` is the total ringed morphism, `sets` and
   `sets_ring` identify its fibre composites and structural maps, and
   `sets_transition` fixes the augmentation's set-sheaf transitions. Its
   `component` comparison identifies total ordinary module pullback followed by
   evaluation with the component pullback. `component_canonical` fixes it as the
   inverse of the ordinary normalized composition comparison. `derivedComponent`
   gives `(La* E)_i ≅ La_i* E`, and `derivedComponent_canonical` fixes the comparison
   using the canonical derived composition and exact evaluation. The final
   `component_transition` and `derivedComponent_transition` equations identify
   transitions with the corresponding ordinary and derived face-augmentation
   composition comparisons. They include identities and arbitrary composites
   through the already specified cocycle. No exactness of face or augmentation
   pullbacks is assumed for this conclusion.

Dependency declarations used (source signatures and docstrings read):

- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`:
  exactly `SheafOfModules` on the specified ring sheaf, with its existing abelian
  category. No new module category is introduced.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, `DerivedCategory.Q`, `Qh`:
  actual unbounded localization. The size-convention node is metatheoretic and
  has no declaration; explicit `u`, `u+1` implement it.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`, used through the recorded `D`.
- `Sheaf.CategoryTheory.TotalSitePseudofunctor`,
  `CoherentSitePseudofunctor`, `totalTopology`,
  `totalSite_of_coherent_pseudofunctor`; the total category is Mathlib's
  `Pseudofunctor.CoGrothendieck`, not a replacement.
- `Sheaf.CategoryTheory.TotalSiteSheafSystems`, `fibreSheaves`, `directImage`,
  `inverseImage`, `imageAdjunction`, `inverseImageId`, `inverseImageComp`,
  `SheafSystem`, `SheafSystemPresentation`, `totalSite_sheaf_systems`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
  `SheafOfModules.cochainModulesMonoidal`, and the imported existing
  `changeOfRings`, `changeOfRingsHom` from
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct`:
  sheafified sectionwise tensor/scalar extension.
- `Sheaf.CategoryTheory.RingedToposMorphism`, `CategoryTheory.RingedToposMorphism`:
  actual geometric morphisms with structural ring maps and their induced direct
  image on modules.
- The helpers reuse `SheafOfModules.AlgebraicInverseImage` and the existing
  `ringedComparisonScalarSection`, `derivedPullbackComplexComparison`,
  `CochainComplex.IsKFlatIndependentCoefficients`, `SheafOfModules.IsFlatOnSite`;
  these are the same notions already used by the recorded derived-pullback and
  tensor dependencies, not private substitutes.
- All stated proof-dependency modules are explicitly imported (ordinary imports
  for proof-only material): continuous/cocontinuous ringed restriction, native
  restriction/sheafification, K-flat resolution and pullback preservation,
  ringed derived pullback, exact derived functors, and ringed derived monoidal
  comparisons. Mathlib leaves use `PresheafOfModules.sheafification`,
  `GrothendieckTopology.W_iff_isLocallyBijective`, `sheafifyComposeIso`,
  `Functor.preservesFiniteLimits_of_preservesKernels`, its cokernel counterpart,
  `Functor.homologyFunctorIso`, `Functor.mapDerivedCategoryFactors`, and
  `Sheaf.createsLimitsOfShape`; their source modules are also imported.

Edge cases checked before writing and again against the final signature:

- Degree zero is `Fin 1`, not the empty ordinal; all natural degrees and all
  injective order maps, including identities, remain present.
- Empty fibre sites and empty covering families are allowed by the given site
  axioms and fibre sheaf conditions. No nonempty-site or terminal-object premise
  was added. The zero ring and zero module satisfy the same formulas.
- A nonflat face ring map such as `Z → Z/2` remains allowed. Exact evaluations and
  K-flat-based derived transitions are unconditional; only the cohomology iff
  requires exact ordinary face pullback. Thus the statement does not falsely
  identify ordinary and derived scalar extension in this example.
- Constant point-site diagrams recover ordinary semilinear module systems;
  a point-site augmentation by `R → A_i` recovers scalar extension in each degree.
  The inverse ordinary composition comparison inserts `1`, and its forward
  normalization follows multiplication of scalar factors, so the identity case
  and a chain of three faces have the prescribed orientation.
- Augmentation data are not forced by degree zero alone, and no degeneracy is
  required. The source's simplicial two-map equalizer was not copied into the
  face-only assertion.
- All integer cohomological degrees and unbounded complexes are quantified.
  There is no injectivity assumption on an evaluated resolution and no claim that
  every compatible derived system arises from a total complex.

Searches actually run:

- `msearch.py`, leanfinder: “The total site of a semisimplicial diagram of ringed
  sites has sheaves of modules given by systems, exact evaluation, derived
  transitions and augmentation pullback”. Eight hits, including
  `SheafOfModules.Presentation`, `PresheafOfModules.isSheaf_of_isLimit`, module
  limits and the abelian instance; none states this construction/theorem.
- `msearch.py`, loogle: `SheafOfModules, SemiSimplexCategory`. Zero hits.
- `msearch.py`, grep, Mathlib `CategoryTheory`:
  `semisimplicial|SemiSimplex|total.*[Mm]odule|[Mm]odule.*[Ss]ystem`. Zero hits.
- Direct `rg` of Mathlib `AlgebraicTopology` found the exact index
  `AlgebraicTopology/SimplexCategory/SemiSimplexCategory.lean`, lines 23–61;
  its full structure, category instance and Hom equivalence were read and reused.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf` for semisimplicial,
  SemiSimplex, module-system and total-module terminology found other integral
  towers/semilinear sequence systems but no instance of this general coherent
  semisimplicial total theorem. The sequence-site calculus imposes a different
  index and cannot replace this node. Exact node-ID grep of `lean/WeilConjectures`
  had no hit. Proposed namespace grep had no hit.
- `tools/blueprint_refs.py search 'semisimplicial ringed total'`: zero blueprint
  nodes. DAG searches found this item and consumers, not a duplicate definition
  or theorem. No new independent notion is needed; helper records belong to the
  one total-category construction and are all listed in `lean.declarations`.

Validation: the complete module compiled in both the isolated sandbox and its
actual library module path through `scompile.py`, with no errors or non-sorry
warnings. The source uses `autoImplicit false`, explicit universes, no local
notations or private definitions, and has maximum line length 98. During rereading,
I corrected the face-ring and semilinear transition comparison endpoints to use
explicit maps under the forgetful functors to set sheaves; this ensures their
`HEq` fields compare the actual same types, not ring/abelian-group morphisms with
set-sheaf morphisms. No mathematical statement fault or dispute was found.

## Second reading by Q137

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
