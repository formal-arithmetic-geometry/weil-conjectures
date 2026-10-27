## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceQcqsDerivedProjectionFormula` states
`AlgebraicGeometry.AlgebraicSpace.isIso_qcqs_derived_projection_mate`, with one
`sorry` and no other declaration. Source read: Stacks `spaces-perfect.tex`, Tag
08IN, `lemma-cohomology-base-change`, statement and complete proof, lines
4666–4722. The node agrees with that source; no statement correction is needed.

Hypothesis and clause correspondence:

- The size convention is represented by explicit universes `u w` and the two
  explicit `HasDerivedCategory.{w}` binders. The sites use their existing small
  affine étale models, with the specified module equivalence to the original
  small étale ringed sites. There is no assumption choosing arbitrary models.
  A common arbitrary localization universe is the fixed larger universe of the
  node's convention; it imposes no equality between the site and localization
  universes, and there is no all-spaces localization-family hypothesis.
- The base scheme is `{S : Scheme.{u}}`; the spaces and their structure sheaves
  are `{Y Z : AlgebraicSpace S}`. The morphism is `(g : Y ⟶ Z)`.
- Quasi-compactness is `(hqc : MapIsQuasiCompact g.hom.hom)`.
  This existing definition tests compactness of the point space of every affine
  scheme pullback; the affine-test criterion gives the equivalent formulation
  with arbitrary quasi-compact test spaces used by the node.
- Quasi-separatedness is
  `(hqs : MapIsQuasiCompact (pullback.diagonal g.hom.hom))`.
  The node additionally says that this diagonal is quasi-separated. For a map
  of algebraic spaces its representable diagonal is a monomorphism, whose own
  diagonal is an isomorphism. Thus that additional property is automatic
  (as noted already in the node's stage-1 review, Stacks 03KL); it requires no
  additional hypothesis and has not been silently assumed for general maps.
- The unbounded objects are `(F : Y.DerivedModules)` and
  `(L : Z.DerivedModules)`. These are ambient derived-category objects, with
  hypotheses `(hF : Y.derivedQCohProperty F)` and
  `(hL : Z.derivedQCohProperty L)`. The property requires every integer-degree
  cohomology module, transported back by the actual restriction equivalence, to
  satisfy Mathlib's `SheafOfModules.IsQuasicoherent`. This is D_QCoh inside
  D(Mod), rather than the derived category of the abelian category QCoh.
- `derivedDirectImage g` is the fixed K-injective right derived functor of the
  compatible-chart direct image transported through the small-model equivalences.
  `derivedTensorPullback g` is the fixed total left derived tensor pullback,
  computed by K-flat resolutions. `derivedDualityModel.closed.tensor` is the
  existing K-flat derived tensor, with its existing representative comparison.
  No alternative functor or tensor is defined here.
- The arrow inside `IsIso` is `(spaceDerivedAdjunction g).homEquiv _ _` of
  `(moduleDerivedPullbackTensor g).hom.app ((derivedDirectImage g).obj F, L)`
  followed by the tensor map of
  `((spaceDerivedAdjunction g).counit.app F)` and the identity on `Lg^* L`.
  Consequently its actual source is `Rg_*F tensor^L L`, its actual target is
  `Rg_*(F tensor^L Lg^*L)`, and its adjoint is precisely the counit map on the
  first factor after canonical tensor pullback. `IsIso` asserts invertibility
  of this specified map, not existence of an unrelated isomorphism.
- There are no flatness, properness, Noetherian, boundedness, perfection, or
  global quasi-compactness assumptions on either space. The seven-step source
  proof with its DAG dependencies is included in the theorem docstring.

Dependency declarations used (signatures and docstrings read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, the structure sheaf and `Modules`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`,
  exactly Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, localization `Q`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, with
  Mathlib's `SheafOfModules.IsQuasicoherent` and its slice instances unchanged.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback`,
  `moduleTensorAdjunction`. The full chart-projection universal property and
  ordinary scalar-one unit are retained downstream.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients` and its resolution predicate;
  used by the existing normalized tensor and pullback interfaces.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, used by the recorded derived direct image.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedQCohProperty`, `derivedDirectImage`, `derivedDualityModel`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback`: `derivedTensorPullback`.
- `Sheaf.AlgebraicGeometry.SpaceAffineHomComparison`: `spaceDerivedAdjunction`,
  uniquely normalized by the ordinary unit and the derived computation maps.
- `Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations`:
  `moduleDerivedPullbackTensor`, uniquely normalized on flat-term K-flat
  representatives by the existing total-tensor and computation comparisons.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapIsQuasiCompact`, tested on
  affine scheme pullbacks. Only this general predicate is used; no curve
  condition is imposed.

The last five owning definition nodes have been added to `stmt_deps` under the
rule permitting already landed definitions. No new nodes or dependency repairs
are needed. Every recorded statement-dependency module is publicly imported.
Every proof dependency with a usable module or Mathlib match is imported for
stage 3. The two presently unstated proof dependencies
`lem-sfb-space-etale-conservative-geometric-points` and
`lem-sfb-space-derived-pushforward-coproducts` have no recorded module to import;
neither is needed to type the statement, and neither is restated here.

Edge cases checked before writing:

- Identity `g`: its counit-mate gives the usual tensor identity.
- `L = O_Z[k]`, including degree zero: normalized tensor comparison and
  adjunction produce the shifted identity case used by the source proof.
- Zero `F` or zero `L`: the map has zero source and target; no nonzero-object
  assumption has entered.
- Empty source or target: the existing sheaf and derived categories allow them;
  neither nonempty points nor a nonempty covering family is required.
- Nonflat maps, for instance `Spec(A/I) → Spec(A)`, remain allowed. The tensor
  and pullback are derived, so this case is not changed to ordinary tensor.
- Unbounded inputs in both directions remain allowed, as do non-Noetherian
  bases and targets that are not globally quasi-compact.

Searches actually run:

1. `msearch.py ... leanfinder "Unbounded derived projection formula for quasi
   compact quasi separated algebraic spaces and quasi coherent complexes"`:
   eight hits, concerning affine transition limits, restrictions on qcqs schemes
   and derived fractions. None states this formula.
2. `msearch.py ... loogle "SheafOfModules, IsIso, Adjunction"`: zero hits with
   unknown identifier `IsIso`; this lookup did not establish absence.
3. `msearch.py ... grep "projectionFormula|projection_formula|derivedProjection"
   AlgebraicGeometry`: zero Mathlib hits.
4. `msearch.py ... leansearch "Unbounded derived projection formula for quasi
   compact quasi separated morphisms of algebraic spaces"`: eight hits on
   scheme quasi-separatedness, quasi-compact base change and restrictions;
   none states a derived projection formula.
5. `rg` of the same projection-name patterns in `lean/WeilConjectures` and
   `lean/Sheaf`: generic projection-mate constructions, étale constant-coefficient
   results, proper results, and `space_affine_derived_projection_formula` were
   found. The latter assumes flatness and an affine base and uses a degree-zero
   module on that base, so is not this arbitrary qcqs/unbounded statement.
6. `grep -rn "lem-sfb-space-qcqs-derived-projection-formula"
   lean/WeilConjectures`: no hit. A direct declaration-name search in both source
   trees found no `isIso_qcqs_derived_projection_mate`.
7. Read the existing algebraic-space derived calculus, pullback, adjunction,
   tensor-comparison and quasi-coherence modules. All required notions already
   have owners; they are reused without auxiliary definitions.

Validation: the prescribed `scompile.py Q20
lem-sfb-space-qcqs-derived-projection-formula` accepted the theorem in sandbox
mode (29.8 seconds) and its final library module path (27.0 seconds), with no
reported errors or unexpected warnings. The final import/docstring update is
validated again by the required delivery dry run. The dry run returned
`OK`: preflight and final-file compilation both passed (commit f2ac3fffb26; nothing pushed). Every variable and universe is
explicitly bound; `autoImplicit` is disabled. No STATEMENT-DISPUTED flag or node
fault was found.

## Second reading by Q20

This is a same-worker second pass; the dispatcher prohibits starting other
agents, and the maintainer supplies the independent delivery review. I reopened
the node, Stacks 08IN and the completed module. I checked the direction of
`homEquiv` (from the pulled-back tensor to the tensor on Y), the order of the
factors and the counit on F, and both actual endpoints. I also checked that the
normalized adjunction is for the same `derivedTensorPullback` and
`derivedDirectImage`, that its tensor comparison uses the same
`derivedDualityModel.closed.tensor`, and that no all-spaces localization family
or flatness hypothesis entered. The automatic quasi-separatedness of the
diagonal explains the node's redundant clause without adding a hypothesis.
No mathematical mismatch was found. I added explicit imports for every
statement dependency and cited each proof step's DAG inputs in the docstring.
