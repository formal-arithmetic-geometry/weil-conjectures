## Worker report

The module `Sheaf.Paper.AugmentedDiagramProjectionMate` supplies the actual natural
transformation `CategoryTheory.StrictReduction.augmentedDiagramProjection`, constructed
by the tower-adjunction unit, the normalized tau, and reduction of the ambient counit.
Its theorem `augmentedDiagramProjectionMate` states the transpose, evaluation, and strict
augmentation identities. The only theorem proof is `sorry`; both data declarations have
complete bodies. No node statement was changed and no new DAG node was needed.

Source read: `literature/stacks-project/sites-cohomology.tex`,
`lemma-pullback-tensor-product` (Tag 07A4, lines 3684ff), and
`equation-projection-formula-map` (Tag 0B56, lines 13666ff) in
`section-projection-formula` (Tag 0943). The latter defines the map without any
perfectness assumption, by exactly the counit-tensor transpose used here.
The diagram-site refinement and the five proof steps of the item are in the theorem
docstring. The node explicitly allows this equivalent adjoint description.

Hypothesis and clause correspondence:

* The arbitrary ringed geometric morphism is `f : CochainPullback.RingedPullback R S`.
  This is the same interface used by the reduction dependency, not a site functor:
  `f.uInv`, `f.uPush`, `f.adj`, and `f.finiteLimits` give the geometric morphism;
  `f.I` is its algebraic inverse image and `f.coefficient` the structural ring map.
  The object and map equations `f.hobj`, `f.hmap` specify actual module scalar
  extension. `f.V` and `f.moduleAdj` give its module direct image and adjunction.
  A right adjoint to this actual pullback is canonically the usual direct image;
  it is not an arbitrary unrelated additive functor.
* `R` and `S` are sheaves of commutative rings; `[IsIso f.coefficient]` is the specified
  ring isomorphism. The actual inverse arrow is available through `asIso`.
  `[PreservesFiniteLimits f.L]` and `[PreservesFiniteColimits f.L]` state exactness;
  additivity of f.L is inherited from RingedPullback. `[f.V.Additive]` records the
  ordinary additive direct image, already part of the ringed-topos convention.
* The sites have independently bound object and morphism universes and are
  `EssentiallySmall.{r}`. This includes small sites without forcing their universes
  equal, and permits equivalent essentially small presentations. Modules are precisely
  `CochainPullback.Modules R`, transparently the dependency's `ringedSiteModules`
  abbreviation of Mathlib `SheafOfModules`. All four derived-category morphism
  universes are independent explicit `HasDerivedCategory` parameters.
* `Q : CommMon (ℕᵒᵖ ⥤ Modules R)` is a strict tower of unital commutative R-algebras.
  Its multiplication/unit maps are natural transformations, hence all transitions
  are unital algebra maps. Positive paper level n+1 is Lean n. The pulled-back
  tower is exactly `Q.X ⋙ f.L`, and its unit is the dependency's `pulledUnit`.
* `MY` and `MX` are exactly the dependency's `RingedModel` records for these two
  coefficient towers and their units. Thus `MY.B` and `MX.B` are B_Y and B_X,
  with universal left-derived counits computing flat-term K-flat representatives;
  `MY.i` and `MX.i` are the canonical coefficient-unit augmentations. They are
  not arbitrary functors with unconstrained augmentations.
* `tau` has the dependency's precise functor type, and `htau : IsNormalized ...`
  fixes it on every flat-term K-flat representative by the ordinary pure-tensor
  map `k.mu`, conjugated by the two universal counits. `k : Comparison f` has the
  existing scalar-extension generator normalization; it is not a bare tensor iso.
* `P : AugmentedProjectionDirectImage f.L f.V f.moduleAdj` groups the operations
  already supplied by the normalization dependencies. `P.RG`, `P.RT`, their
  `eta`/`etaT` and `universal`/`universalT` are the total right-derived functors.
  `P.d`, `P.dT` are their canonical adjunctions, fixed by the ordinary Hom formulas
  `hom_normalization` and `tower_hom_normalization`. `P.chi` and `P.beta` have
  exactly the constant and evaluation comparison types. Their `chi_counit` and
  `beta_counit` equations are verbatim the respective dependency conclusions.
  These equations uniquely specify the comparisons: transpose along P.dT for chi,
  and along P.d for each beta component. They therefore encode the canonical
  comparisons, rather than imposing an additional geometric hypothesis.
* The definition's type `P.RG ⋙ MY.B ⟶ MX.B ⋙ P.RT` makes h natural in K and
  a morphism in D(strict towers), retaining all coefficient transitions.
  Its data are the explicit composite of natural transformations, not maps chosen
  from existence and not a sequence of evaluated morphisms.
* The first theorem conjunct is `FT.map h ≫ P.dT.counit = tau ≫ MX.B.map counit`:
  exactly the equivalent adjoint description in the node. On the diagram sites the
  ringed projection mate precomposed with chi has this same transpose, using
  `chi_counit`; equality follows by the Hom bijection. This describes the specified
  diagram-site mate without creating a second derived tensor presentation.
* The second conjunct says `evY.map h ≫ beta = P.d.homEquiv ... (...)` for every
  n and K. The argument of the Hom equivalence is the inverse exact-pullback/
  evaluation interchange, followed by evaluation of tau and of MX.B(counit).
  Evaluated reduction is B followed by exact evaluation, with precisely the universal
  reduction counit `StrictReduction.evaluationCounit`. The reduction dependency states
  that this computes derived tensor with Q_n and that evaluated tau is the normalized
  tensor/pullback comparison. Thus this is exactly the ambient counit-tensor projection
  arrow, with the canonical evaluation identifications included explicitly. No separate,
  arbitrary tensor functor or comparison was substituted.
* The third conjunct is `MY.i.app (P.RG.obj M) ≫ h.app M =
  P.chi.hom.app M ≫ P.RT.map (MX.i.app M)`. This is the displayed augmentation
  equality in Lean's left-to-right composition order. Both sides lie in
  `DerivedCategory (ℕᵒᵖ ⥤ Modules R)`, before evaluation or any Rlim operation.
* There is no perfectness, flatness of Q_n, completeness, boundedness, or IsIso(h)
  assumption. The construction uses the node's equivalent adjoint description;
  it does not use the perfect-projection-formula isomorphism theorem.

Dependency declarations read and used:

* `Sheaf.Paper.ReductionPullbackDerivedTower`: `StrictReduction.RingedModel`,
  `IsNormalized`, `pulledUnit`, `flatRepresentatives`, `termwise`, and
  `reductionPullbackDerivedTower`; its public interface
  `Sheaf.SecSmoothPurity.CochainTensorCoherenceData` supplies
  `CochainPullback.Modules`, `RingedPullback`, `Comparison`, and `moduleUnit`.
* `Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization`:
  `ringedConstantTowerPullback`, `ringedConstantTowerPushforwardNormalization`.
* `Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization`:
  `towerDerivedEvaluationInterchange`, `exists_unique_towerDerivedEvaluation_normalized`.
* `Sheaf.CategoryTheory.RingedToposMorphism`: `RingedToposMorphism` (the geometric
  convention, represented for tensor operations by the reduction dependency's
  RingedPullback presentation).
* `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules` and Mathlib's
  `SheafOfModules`; `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`.
* Proof imports: `Sheaf.Paper.ProjectionMateExact`:
  `SheafOfModules.ringedProjectionMateExact`;
  `Sheaf.CategoryTheory.DiagramSiteRealization`: `exists_diagramSite_realization`;
  `Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck` and
  `Mathlib.CategoryTheory.Abelian.FunctorCategory` (levelwise abelian structure).
  These imports preserve the dependency proof plan for stage 3.

Edge checks: zero module and zero coefficient algebra are allowed; no nonzero or faithful
unit is assumed. The constant unit-algebra tower gives the unit case. Identity f and
identity transitions are included. Arbitrary nonflat coefficient algebras (e.g. a quotient
of a constant ring sheaf) are retained by the K-flat resolution model. The first positive
level is not omitted: it is op 0. Strict transitions and the augmentation are natural
transformations before localization; the proof does not infer equality of derived-tower
maps from equality after evaluation. Independent site sizes and derived morphism sizes
were retained from the reduction dependency.

Searches actually run, with the launcher msearch wrapper:

* leanfinder: `Projection formula morphism for derived strict towers of sheaves respects
  the coefficient unit augmentation and evaluates to the counit tensor mate` — 8 hits,
  including `SheafOfModules.unitToPushforwardObjUnit`, presentation maps and ordinary
  sheaf adjunction facts; none states the derived strict-tower identity.
* loogle: `CategoryTheory.Adjunction.homEquiv, SheafOfModules.pullbackPushforwardAdjunction`
  — two ordinary pullback-unit Hom-equivalence equations, neither the required statement.
* grep: `projectionFormula|projection_formula|ProjectionFormula|augmentedDiagram`
  — 0 Mathlib hits.
* leansearch: `Derived projection formula for an augmented inverse sequence of sheaves
  of modules commutes with the coefficient unit` — 8 hits, ordinary unit and pullback
  maps and a projective-resolution comparison; none gives the tower statement.
* rg of `lean/WeilConjectures` and `lean/Sheaf` with the projection names and the item id:
  found the generic `derivedProjectionFormulaMate` in ProjectionFormulaArrows and the
  upstream rightAdjointProjectionMap. Read their declarations and transpose descriptions;
  they supply the general mate operation, not the normalized reduction/augmentation
  theorem for arbitrary coefficient towers. The exact item id has no existing declaration.
* Read the current server source of `Sheaf.Paper.RingedStrictTowerProjectionMorphism`
  using `scompile.py --source`. Its coefficient property requires bounded finite-free
  complexes at every level, unlike the arbitrary algebra sheaves of this item, so its
  theorem cannot serve as an existing match. No duplicate of its coefficient notion
  or of the project's derived tensor was introduced.

Validation: `scompile.py NI lem-weil-pbc-augmented-diagram-projection-mate <module>`
compiled the sandbox and the final module, exit 0, with no warnings. The first attempt
had a nonexistent proof-import path for levelwise exactness; replaced it with the actual
Mathlib functor-category module. No declaration or theorem statement needed repair.

## Second reading by NI

The worker reread the node, dependency signatures, source, and final file after the
successful compile. This is a second pass by the same worker; the dispatcher brief
assigns independent review to the maintainer and forbids starting other agents.
The hypotheses above cover every object in the node. In particular, the final map is
constructed as a natural transformation in D(Tow), tau is representative-normalized,
chi and beta are pinned down by the actual canonical counits, and the last equality is
not replaced by its evaluations or by an equality after Rlim. The evaluation formula
uses B followed by evaluation, exactly the normalized tensor model supplied by the
reduction dependency. Checked the orientations of every Hom and of the inverse
interchange. No statement change, disputed clause, new node, or dependency repair.
