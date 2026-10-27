## Worker report

The delivery states `AlgebraicGeometry.AlgebraicSpace.fppf_face_total_qcoh_equivalence`
in `Sheaf.AlgebraicGeometry.FppfFaceTotalQCohEquivalence`. Its only theorem has proof
`sorry`. All accompanying definitions have real data. The original mathematical
statement, proof and source are unchanged. Two already landed definition nodes are
added to `stmt_deps`: `def-sfb-space-fppf-hypercover` and
`def-pur-cochain-coefficient-universe-transport`. No new DAG nodes or dependency
repairs are needed.

Source reading: `literature/stacks-project/spaces-simplicial.tex`, lines 2600ff
(`lemma-quasi-coherent-sheaf`, 0D7M), and 7459--7550
(`lemma-coh-descent-qcoh-unbounded-for-fppf-hypercovering`, 0DHF), including its
five-condition proof. The node explicitly requests the face-only adaptation.
The proof docstring records all seven DAG proof steps, with the affine localized-site
bridge, enough-injectives input, and exact free adjoint of evaluation included.

The hypothesis and clause correspondence is as follows.

* A scheme S and arbitrary algebraic space Z over S are `{S : Scheme.{u}}` and
  `{X : AlgebraicSpace S}`. There is no quasi-compactness, separatedness,
  representability or Noetherian assumption on X or any level.
* The augmented simplicial space is `U : SimplicialObject (Over X)`.
  `hU : IsSpaceFppfHypercover U` is the existing proper-face matching predicate:
  for every n a proper-face limiting matching arrow is flat, locally finitely
  presented and surjective. It includes X in degree zero and U_0 times_X U_0
  in degree one. It does not assert flatness of degeneracies.
* `fppfFaceSpace` is U after precomposition by
  `SemiSimplexCategory.toSimplexCategory.op`; `fppfFaceMap` is its actual map.
  The index is the opposite of finite nonempty ordinals with injective order maps.
* `fppfFaceSite X` uses `X.EnlargedEtaleSite`, `X.enlargedEtaleTopology`, and
  `X.enlargedCotangentStructure`, with the existing explicit
  `CochainUniverseTransport.ring` sectionwise ULift into the site/sheaf universe u+1.
  Its scalar down map is ULift.down. The module universe is u+1 and derived
  localization universe u+2, inherited from `SemisimplicialRingedTotal.Site`.
  All scheme universes u are allowed; no scheme/site universe equality is imposed.
* `FppfFaceTotalModel U` presents these precise data. `fibre` and `covering`
  identify its fibres and coverings with the enlarged sites. `baseChange` identifies
  each transition with the actual `enlargedBaseChange`. `unitor` and `compositor`
  fix projection-preserving comparisons. `fibreRing` fixes the extended rings.
  `presentation` uses the dependency's actual `Presentation`, never a private
  category of systems. `faceRing` pins the adjoint structural map to
  `chartNormalizedUnderlyingMap` of the unique regular-function map supplied by
  `cotangentStructuralMap_existsUnique`. HEq only transports through the displayed
  fibre equalities; it does not substitute arbitrary equivalent sites or rings.
* `augmentation` and `totalAugmentation` are the existing coherent augmentation
  and its total presentation. `augmentationDirect` fixes each component to actual
  base-change precomposition for u_n. `augmentationComparison` fixes the adjoint
  comparison to `enlargedDirectCompositionIso`. `augmentationRing` imposes the same
  regular-function normalization as `faceRing`.
* The conclusion supplies `Nonempty (FppfFaceTotalModel U)`, then applies to every
  such model. Model existence is a conclusion, never an additional hypothesis.
  No definition chooses data from this mere existence assertion.
* `M.qcoh` is componentwise Mathlib `SheafOfModules.IsQuasicoherent` AND invertibility
  of all ordinary transitions. The node's quasi-coherent total modules are rendered
  by this predicate, without replacing component quasi-coherence.
* Weak Serre is expanded into `IsClosedUnderKernels`, `IsClosedUnderCokernels`,
  `IsClosedUnderExtensions`, just as the node expands it. No stronger closure under
  arbitrary subobjects is asserted.
* `M.derivedQCoh = DerivedCategory.homologyProperty M.qcoh` tests all integer
  cohomology objects in the actual ambient unbounded derived category. Its iff
  identifies this with `M.presentation.IsCartesian B` and componentwise
  `DerivedCategory.homologyProperty (SheafOfModules.isQuasicoherent ...)` under
  every derived evaluation. Both directions of the criterion are stated.
* Downstairs is `DerivedCategory.homologyProperty (SheafOfModules.isQuasicoherent
  (fppfFaceSite X).rings)`. Both this and `M.derivedQCoh` are asserted triangulated.
* Ordinary total pullback is asserted exact. Derived pullback is the existing
  `M.totalAugmentation.pullback.derived`, with its left-derived universal comparison
  and its flat-term K-flat computation; no arbitrary left adjoint replaces it.
* The existential `(R, β)` is a universal right-derived pair for the actual
  `M.totalAugmentation.map.modules`, via `R.IsRightDerivedFunctor β ...`.
  `IsIso (fppfFaceRightComparison ... I)` for every K-injective I explicitly states
  computation by K-injective resolutions. The comparison includes the quotient
  isomorphisms between homotopy and cochain descriptions of that same localization.
* `a : M.totalAugmentation.pullback.derived ⊣ R` is normalized on every flat-term
  K-flat P and K-injective I: its derived Hom transpose equals the localized
  ordinary tensor/direct-image transpose followed by the specified right-derived
  comparison. These representatives compute the derived categories, so this pins
  the canonical adjunction rather than an unrelated adjunction.
* Every downstairs quasi-coherent K has quasi-coherent pullback and
  `IsIso (a.unit.app K)`. Every total quasi-coherent B has quasi-coherent R(B) and
  `IsIso (a.counit.app B)`. These preservation and actual unit/counit isomorphism
  clauses express mutually quasi-inverse equivalences of the full subcategories.
  Both ambient functors commute with shifts and are triangulated; together with
  the subcategory triangulated assertions this gives triangulated equivalences.
* All cochain complexes and cohomology conditions are indexed by Z. No boundedness
  or uniform global cohomological bound is introduced.

Dependency declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and morphisms.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  its full-subcategory morphisms, small etale site and structure sheaf.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `AlgebraicSpace.QCoh`
  specializes Mathlib `SheafOfModules.isQuasicoherent`; the same predicate is used
  for the component and base ring sheaves.
* `Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory`: `Site`, `Site.modules`,
  `Site.D`, `Site.flat`, `RingDiagram`, `Presentation`, `Presentation.IsCartesian`,
  `Augmentation`, `AugmentationPresentation`, `Pullback.alpha`, and the theorem
  `semisimplicial_ringed_total_category`.
* `Sheaf.AlgebraicGeometry.SpaceCotangentRingMap`: its public `EnlargedEtaleSite`,
  `enlargedEtaleTopology`, `enlargedBaseChange`, `enlargedDirectImage`,
  `enlargedCotangentStructure`, `cotangentStructuralMap_existsUnique`.
  Its recorded `cotangentRingMap` was read: it transports the same structural map
  to the affine small model. Here the enlarged form is required by the node.
* `Sheaf.AlgebraicGeometry.EnlargedRingedCompositionLocalization`:
  `enlargedIdentityIso`, `enlargedCompositionIso`, `enlargedDirectCompositionIso`,
  and the signature and chart-normalization clause of
  `enlargedRingedMorphism_composition`.
* `Sheaf.AlgebraicGeometry.SpaceFppfHypercover`: `SpaceMapIsFppf`,
  `IsSpaceFppfHypercover`, and the proper-face matching predicate.
* `Sheaf.CategoryTheory.CochainCoefficientUniverseTransport`:
  `SheafOfModules.CochainUniverseTransport.ring` and its explicit ringFunctor.

All already stated proof dependencies are imported with plain `import`; statement
objects use `public import`. Proof-only nodes currently lacking modules are
`lem-sfb-space-qcoh-kernels-colimits`, `lem-sfb-space-qcoh-extension-closed`,
`lem-sfb-fppf-face-heart-descent`, `lem-sfb-fppf-face-heart-derived-unit`, and
`lem-sfb-ringed-unbounded-descent-criterion`. They are documented in the proof;
no declaration is needed from them to state this item. No proof-import cycle is
needed. Enough injectives is imported from the recorded Mathlib match file.

Edge cases checked before writing: empty base and empty levels introduce no
nonemptiness assumption; zero modules and complexes are allowed; degree zero's
matching object is the base; degree one has its two proper faces; identity injective
operators have the projection unit law; every higher injection is included while
all degeneracies are absent from the total index. The Cech nerve of A^1 over a field
has a nonflat diagonal degeneracy and remains allowed. There are no finite-cover,
finite-rank, bounded-complex or separatedness restrictions. The u+1 site and explicit
coefficient transport compile without identifying scheme and enlarged-site universes.

Searches actually run (NW/item msearch logs):

* LeanFinder: "Unbounded derived quasi coherent descent on the face total site of
  an fppf hypercover of an algebraic space". Eight results, beginning with
  `Scheme.GlueData.oneHypercover` and ordinary one-hypercover sheaf lemmas; no
  result states the unbounded derived face-total equivalence.
* Loogle: "SheafOfModules.IsQuasicoherent, ObjectProperty.IsSerreClass". No hits;
  the second identifier was reported unknown. This is an unsuccessful name query,
  not evidence that the existing quasi-coherent predicate is absent.
* Mathlib grep via msearch: `IsSerreClass|IsWeakSerre|hypercover` in CategoryTheory.
  Twenty-five displayed ordinary-hypercover results. Direct rg of Mathlib
  ObjectProperty found the three closure predicates; those are reused.
* LeanSearch: "Unbounded derived quasi coherent descent on an fppf semisimplicial
  hypercover". Eight results: stack-to-descent-data equivalences and existing
  `SheafOfModules.QuasicoherentData`/`IsQuasicoherent` primitives, not this theorem.
* Direct rg of `lean/WeilConjectures` for
  `face.total|FaceTotal|semisimplicial|IsWeakSerre`, and exact-node-id grep: no existing
  theorem. Direct rg of `lean/Sheaf` for face total/weak Serre and
  `RingDiagram|AugmentationPresentation|SemiSimplexCategory` found the recorded
  dependencies and downstream proof docstrings, without a duplicate theorem.
  The existing coefficient ring lift and quasi-coherent predicates are reused.

No STATEMENT-DISPUTED finding and no statement correction.

## Second reading by NW

I reread the node and completed file in this worker session; no second agent was
started, as the dispatch brief forbids it. The maintainer supplies independent review.
The clause mapping above was checked against the final signature. During rereading
I added augmentation-comparison normalization, which fixes its composition comparison,
and explicit triangulated assertions on both full subcategories. The model is both
supplied in the conclusion and universally quantified, preventing vacuity from absence
of a model. Its HEq fields pin the existing site, ring and projection maps.
The representative Hom normalization fixes the canonical unit and counit. Each
preservation clause names the correct source/target cohomology predicate.
Every definition has data, every variable/universe is bound, and the only postponed
proof is the node's theorem. No node statement or proof changed.
