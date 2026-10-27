## Worker report

The delivery states the live stage-1 node in
`Sheaf.CategoryTheory.AlgebraDiagramEvaluationAdjunctionNormalization`.
The main declaration is
`CategoryTheory.AlgebraDiagramAdjunctionPresentation.evaluationAdjunctionNormalization`.
Its conclusion unfolds the public proposition
`AlgebraDiagramAdjunctionPresentation.EvaluationAdjunctionNormalization`, which spells out
all the comparisons and equations. Every mathematical theorem is postponed with `sorry`.
All definitions, ring maps, evaluations, transition maps, localization maps and presentation
structures have real data. There is no new axiom or arbitrary comparison hypothesis.

The previous worker's “already merged for Q17” observation concerns the stage-1 split:
the live node has `reviewed` and an eight-step proof, but has no `lean` or
`reviewed_lean` binding. Its proof and all stage-1 fields are preserved verbatim.
There is no released repair note for this item. This is its stage-2 statement delivery,
not another stage-1 split. The sandbox initially contained only dispatcher brief files.

### Hypotheses and objects

* Small sites and index category: `J C D : Type u`, their `SmallCategory` instances,
  `K : GrothendieckTopology C`, and `L : GrothendieckTopology D`. This is the node's
  common module-universe bound, not an equality between unrelated large-site universes.
  Every site small within that bound admits this presentation. The arbitrary morphism
  universe `w` of each `HasDerivedCategory` remains independent of `u`.
* The commutative coefficient ring is `A : CommRingCat.{u}`. The actual constant ring
  sheaves are `algebraDiagramConstantRing K A` and its `L` analogue, defined using the
  recorded `CategoryTheory.constantSheaf`, not a constant presheaf substitution.
* `AlgebraDiagramAdjunctionPresentation.s` is the geometric morphism on the constant
  rings. `RingedToposMorphism` includes the set-sheaf inverse/direct adjunction,
  finite-limit preservation of inverse image, and the induced module direct image with
  its generalized-element scalar-action normalization. `constantNormalization` fixes
  its ring map on every coefficient element using `algebraDiagramConstantSection`.
  This rules out a coefficient-ring automorphism in place of the canonical map.
* `BX` and `BY` are the actual ring sheaves on `diagramSiteTopology J C K` and its
  `D,L` analogue. `commX`, `commY` assert commutativity section by section; `aX`, `aY`
  give the constant-A algebra structures. This is the diagram-site realization of
  the node's diagram of commutative algebras, including every transition.
* `fB`, `fA`, and `fj` are the induced ringed-topos morphisms for algebra diagrams,
  constant diagrams and level rings. `inverseB`, `directB`, `adjB`, and their A/level
  analogues identify the *actual* componentwise geometric functors and adjunctions.
  `structuralB`, `structuralA` identify their structural maps at every vertex.
  `coefficientSquare` is compatibility with the algebra-structure morphisms.
* `cartesianA`, `cartesianB`, `cartesianDiagramA`, `cartesianLevel` say the structural
  coefficient maps are isomorphisms: these are the specified pulled-back rings,
  not an unrelated coefficient family. This presents `B_X = u^{-1} B_Y` up to its
  specified ring identification, naturally in all diagram arrows.
* `pullB`, `pullj` with `moduleAdjB`, `moduleAdjj` choose presentations of ordinary
  module inverse image as the left adjoints of the specified induced module direct
  images. Such choices are unique up to the adjunction-normalized isomorphism.
  Their additive/finite-limit/finite-colimit fields record the exact inverse-image
  property already stated in the node. No module-adjunction coherence is assumed:
  the ordinary mate equation is a conclusion of the theorem.
* The module categories are exactly `ringedSiteModules` / `SheafOfModules` of the
  specified ring sheaves. The derived categories are the recorded ordinary unbounded
  `DerivedCategory`, with explicit chosen localization instances. Neither diagram
  objects in a derived category nor a different completed derived category is used.
* `eBX`, `eBY`, `eAX`, `eAY` are the actual `algebraDiagramEvaluation` functors.
  Their objects use `PresheafOfModules.pushforward₀Obj` along the vertical slice;
  their maps are the actual sectionwise linear maps. `algebraDiagramRingAt` restricts
  the given ring sheaf to that slice. The named additive and finite-limit/colimit
  theorems state exactly the node's exact-evaluation clause. Their docstrings give
  the vertical kernel/cokernel proof. They make no assertion about K-injectives.
* `rX`, `rY`, `rXj`, `rYj` are the recorded `SheafOfModules.restrictScalars` on the
  actual algebra maps. The two named exactness theorems state its exactness clause.
  The derived scalar functors are their exact termwise `mapDerivedCategory` lifts.
* `PB`, `PA`, `Pj`, `P` use the existing unbounded `rightDerivedFunctor`; `GB`, `Gj`
  use exact `mapDerivedCategory`. `adjDB` and `adjDj` use the existing
  `Adjunction.mapDerivedCategoryRightDerivedAdjunction` of the ordinary module
  adjunctions. A derived adjunction with an arbitrary unit/counit is never supplied
  as input. `algebraDiagramKInjectives` merely assembles the existing small-site
  Grothendieck/K-injective instances; it does not posit an additional resolution
  hypothesis. Constant-slice instance transports use the definitionally identical
  coefficient ring and the very same chosen derived localization.

### Each conclusion

1. `lambda0 j` is the componentwise ordinary inverse-image isomorphism, normalized by
   its ordinary counit/mate equation with `cB j`. The displayed derived left comparison
   is exactly `Functor.mapDerivedCategorySquareIso (lambda0 j)`, localizing it.
2. `beta j` is `PB ⋙ eBY_D ≅ eBX_D ⋙ Pj`, and `delta j` is
   `PA ⋙ eAY_D ≅ eAX_D ⋙ P`. These are the node's beta/delta with Lean's functor
   composition order. `cB`, `cA` are their ordinary comparisons, characterized by
   `AlgebraDiagramOrdinaryEvaluationNormalized`. That normalization uses the given
   induced direct-image identifications and `algebraDiagramSetDirectEvaluation`,
   the actual counit of the concrete diagram-site equivalence.
3. `AlgebraDiagramDerivedSquareNormalized` fixes each comparison by the derived units
   `rightDerivedFunctorUnitQ` and the exact localization factorizations for every
   complex. It is the common-resolution/composition normalization, not a bare
   existence of natural isomorphisms. On K-injective diagrams it specializes to
   exactly the unit normalization in proof steps 2, 3 and 5.
4. The universal equality involving `p.adjDB.counit` and `p.adjDj j` is the displayed
   counit equality: evaluated diagram counit equals lambda, then the image of beta,
   then the level counit. Lean writes these composites from left to right.
5. The next universal equality quantifies every derived `M`, `N`, and
   `t : M ⟶ p.PB.obj N`. Its two `homEquiv.symm` terms are the actual diagram and level
   adjunction transposes. Its right side is lambda inverse followed by evaluated
   transpose, exactly the node's equivalent transpose equation.
6. `c` is the ordinary coefficient-restriction/direct-image comparison; `d` is its
   derived comparison. `cj j` and `dj j` are their level versions. Each ordinary
   comparison is fixed by `AlgebraDiagramOrdinaryRestrictionNormalized` on underlying
   sheaves; each derived comparison has the same explicit derived-unit normalization.
7. `algebraDiagramRestrictionEvaluation` is the ordinary, definitionally identical
   scalar-restriction/evaluation square. The coefficient equation in the assertion
   is precisely `delta * eAY(d) = dj * rYj(beta)` after the localized identifications
   for that square. Both routes are written with the necessary localization
   comparison maps, so they have exactly the same source and target.
8. Naturality in `N` is part of every natural isomorphism. The last two conjuncts
   quantify every actual arrow `a : j ⟶ k`, separately for B and A. The ring map is
   `algebraDiagramRingArrow`, and the map on modules is `algebraDiagramTransition`.
   Its localization is `algebraDiagramDerivedTransition`, which uses
   `Localization.liftNatTrans` and the exact composition isomorphism. The asserted
   squares commute with these actual transitions after the actual scalar
   restrictions, and the intervening `ca`, `qa` comparisons have the ordinary and
   common-derived-unit normalizations as well. Identity and composition behavior
   is inherited from the original sheaf restriction laws, not replaced by arbitrary
   transition arrows. The coefficient equation together with these two families
   gives the transition compatibility of coefficient restriction.
9. No coefficient flatness, perfection, completeness or preservation of K-injectives
   by varying-ring evaluation is an input. Exactness of evaluation is insufficient
   to assert the last property, and it is nowhere asserted here.

The public proposition defining the conclusion has internal `letI` bindings only
for already supplied exactness proofs on constant slices. These are proof-valued
instance transports in a definition, not `let` binders in a theorem signature or
chosen comparison maps. The proposition unfolds to the full explicit assertion.
All its data and every helper definition are supplied. The main theorem and the
five exactness component theorems are the only postponed proofs; all are clauses
of this same node and all are listed in `lean.declarations`.

### Dependency declarations

The statement uses the recorded `CategoryTheory.constantSheaf`
(`Mathlib.CategoryTheory.Sites.ConstantSheaf`), `CategoryTheory.ringedSiteModules`
(`Sheaf.CategoryTheory.RingedSiteModules`), `DerivedCategory` and `HasDerivedCategory`
(`Mathlib.Algebra.Homology.DerivedCategory.Basic`), and
`SheafOfModules.restrictScalars` (`Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`).
The size convention is metatheoretic and supplies no declaration; its bound is
expressed by the explicit universes and small-category hypotheses.

The diagram-site topology and realization are the existing `diagramSiteTopology`,
`diagramSiteRing`, `diagramSiteSheafEquivalence`, and `exists_diagramSite_realization`
from the `Sheaf.CategoryTheory.DiagramSite*` modules. Their constant-module
`diagramSiteModuleComponent` does not evaluate a varying ring, so this module
supplies the missing concrete varying-ring evaluation, not a replacement category.
The construction restricts the actual sheaf, rather than ignoring horizontal maps.

The proof imports retain the recorded `diagramRingRestrictionPushforward`
(`Sheaf.CategoryTheory.DiagramRingRestrictionPushforward`),
`ringedToposDerivedPushforwardComposition`
(`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`),
`ringedTopoiCanonicalDerivedTensorPullback`
(`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`),
`exactSquare_derived_counit` and `Adjunction.HasExactDerivedHomFormula`
(`Sheaf.CategoryTheory.ExactSquareDerivedCounit`),
`Functor.kInjectiveDerivedMapComputation`
(`Sheaf.CategoryTheory.KInjectiveDerivedMapComputation`),
`restrictionRingedToposModuleDirectImage_exists`
(`Sheaf.CategoryTheory.RestrictionRingedToposModuleDirectImage`),
`SheafOfModules.isGrothendieckAbelianOfUniverses`
(`Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`),
`module_pullback_pushforward_adjunction`
(`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`), and
`grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`
(`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`).
The Mathlib matches for proof-only nodes are `evaluationAdjunctionRight`,
`Functor.homologyFunctorIso`, `Functor.mapDerivedCategoryFactors`, and
`CochainComplex.IsKInjective.Qh_map_bijective`; their source modules are imported.
The existing upstream derived-adjunction and right-derived-unit constructions are
used directly. No dependency record is changed and no dependency is restated.

### Edge cases and mathematical audit

* Empty `J`: no `Nonempty` assumption and no chosen vertex. All vertex and arrow
  assertions are universally quantified and remain meaningful; the diagram-site
  ring and module category exist without a vertex.
* One-object or discrete category: evaluations give the expected ordinary single
  ring comparisons; in the discrete case there are no off-vertex transitions.
* Parallel arrows, nontrivial loops and compositions: each actual arrow is quantified,
  and both the ring arrow and semilinear module arrow come from that same restriction.
* Zero ring and zero objects: there is no nontriviality or nonzero-module hypothesis.
  All normalized formulas specialize to the unique maps when the category is zero.
* Non-flat ring transitions, for example Z -> Z/2: allowed. Neither the ring-arrow
  maps nor their scalar restrictions acquire a flatness premise. The proof uses
  resolution acyclicity and two-out-of-three, not preservation of K-injectives by
  varying-ring evaluation.
* Arbitrary unbounded complexes and derived morphisms: no boundedness or degree
  restriction, no restriction to chain maps in the final counit/transpose assertions.
* The node's source was read at `sites-cohomology.tex` lemma-adjoint (07A6),
  lemma-derived-pushforward-composition (0D6E), and lemma-derived-limit-is-ok (0941).
  The last addresses constant abelian towers and is not used to justify K-injective
  preservation for a varying-ring evaluation.

No statement correction, new independent notion, dependency repair or
STATEMENT-DISPUTED flag is needed. Presentation records and helper propositions
only package the very objects and canonical normalizations of this node.

### Searches

Searches were run through `batch2/msearch.py` with the sandbox override set to
this stage-2 sandbox; the wrapper receipts are in `searches.jsonl`.

* LeanFinder: “Evaluation of derived direct images on diagrams of ring sheaf modules
  commutes with adjunction counits and restriction of scalars.” Eight ordinary
  module pushforward/pullback and section-adjunction hits; no normalized unbounded
  varying-ring diagram comparison.
* Loogle: `"evaluation", "counit"`. The two hits were
  `evaluationAdjunctionLeft_counit_app` and
  `evaluationAdjunctionRight_counit_app_app`, ordinary functor-category statements.
* Mathlib grep: `evaluation.*(adjunction|counit|rightDerived)|((adjunction|counit|rightDerived).*[Ee]valuation)`
  in CategoryTheory. Nine hits, concerning ordinary evaluation adjunctions, constant
  sheaves and unrelated cartesian-closed constructions.
* LeanSearch: “Evaluation of a cartesian algebra diagram derived adjunction preserves
  counits and coefficient restriction.” Eight hits, including the two ordinary
  evaluation-counit lemmas, algebraic scalar adjunctions and generic adjunction data;
  no statement of this node.
* `rg` of `lean/WeilConjectures` and `lean/Sheaf` for algebra-diagram/semilinear-diagram
  evaluation and adjunction patterns found the constant diagram realization,
  `DiagramRingRestrictionPushforward`, and specialized quotient-system statements;
  none states the arbitrary-small-category normalized evaluation assertion.
* The exact blueprint id has no occurrence in upstream `lean/WeilConjectures`.
  A final exact-name search in Mathlib and both source trees found none of the new
  helper names or the new presentation structure. Existing definitions are used
  wherever available; the helpers add the missing actual slice maps and coherence.

Validation is through `scompile.py` only, followed by the prescribed `deliver2.py`
dry run and delivery. No library source, launcher script or live DAG was edited,
no direct Git command was run, no global build was started, and no agent was spawned.

## Second reading by NL

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
