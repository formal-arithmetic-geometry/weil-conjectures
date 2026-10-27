## Worker report

Stage 2, Q93, 2026-10-22. The delivery states the accepted node in
`Sheaf.Paper.RetaggingCoordinateOrientations`, with the sole postponed theorem
`WeilConjectures.PurityFiniteSetting.retagging_coordinate_orientations`.
Three Prop-valued definitions package its clauses using the published objects;
none chooses geometric data, a comparison map, or an orientation. The node changes
only in `lean`. No split, source, statement, dependency or target is changed.

The previous BLOCKED ending concerned an unchanged stage-1 delivery. I read the
2026-10-22 stage-handoff paragraph of coord/brief-stage2.md, checked the live node
(no Lean record), the stage-2 queue row, and the accepted Q150 report. There is no
released repair note for this item. This delivery preserves that split and uses
`deliver2.py`, as the current stage brief directs.

Source read: current main-20261015 equivariance proof Step 1, together with the
accepted item's seven explicit steps and the recorded orientation, DNC and vector
integration interfaces. Retagging means postcomposition with Spec(sigma), never
pullback along a fictitious k-linear identity between the two presentations.

Hypothesis and clause correspondence:

- The finite-field datum, algebraic closure, coefficient prime different from the
  characteristic and positive level m are the fields of `P : PurityFiniteSetting`.
  `_hE : P.extension = ⊥` is exactly E = Q_l. Thus P.Ring is its existing
  O_E/(varpi^m), the canonical Z/ell^m coefficient presentation used by both
  recorded orientation statements. P.Coefficient is only its standard universe
  lift; there is no new coefficient ring or scalar action.
- `σ : P.field.k ≃ₐ[P.field.k₀] P.field.k` is the field automorphism fixing k0.
  `aX`, `aY` name the structural maps. IsSeparated, LocallyOfFiniteType and
  QuasiCompact on each express separated finite type over k. `_hf` expresses
  that f is a k-morphism. IsSeparated f and SmoothOfRelativeDimension d f give
  exactly the smooth separated pure-dimension map, with `d : ℕ` including zero.
  LocallyOfFiniteType f and QuasiCompact f are the source's finite-type domain;
  they follow from the stated finite-type k-domain and do not restrict it.
- `V : Y.Opens`, `hV : IsAffineOpen V`, `U : X.Opens`, and `e` with `[Etale e]`
  give the affine target open, open source chart and etale coordinate map.
  `w` says its projection to Y is U.ι followed by f, hence also expresses
  U contained in f inverse V. No nonemptiness or affineness of U is required.
- `aYσ` is aY followed by Spec(sigma). The first conjunct is literally equality
  of the two `leftDerivedFunctor.map` images of
  `(P.diagonalDualizingObject d f aYσ).hom` and
  `(P.diagonalDualizingObject d f aY).hom` under U.ι. These are the recorded
  Pi orientations, not the oppositely directed tensor smooth-purity gamma and
  not an equality merely on cohomology. Their source and Tate target are in the
  same fixed-ring derived category on the small pro-etale site. The published
  diagonal orientation is specified by coordinate-adjunction normalization on
  every chart (DiagonalOrientationNormalization and diagonalOrientationCharts).
- There is one underlying f, pullback f f and pullback.diagonal f. Consequently
  the diagonal ideal, normal cone, its projection and zero section are the same
  actual constructions. `RetaggingSectionConclusion` is applied specifically
  to g = pullback.fst f f, s = pullback.diagonal f, with aX and the published
  section identity. It compares the underlying actual DNC source, projection
  and augmentation section; the intrinsic Ls* Rg! R section object, the actual
  DNC family, normal-section object, and canonical fibre comparisons at 1 and 0.
  `HEq` only accounts for dependent object presentations; it does not insert
  an unspecified isomorphism. The geometric fibre maps, punctured trivialization
  and etale coordinate substitutions are those of the same extended-Rees ideal
  and maps g,s; they have no k-structure-map argument and are thus literally
  shared terms, not new isomorphisms to choose or extra equations to assume.
- The final conjunct of RetaggingSectionConclusion compares the actual unique
  normalized comparisons selected from existsUnique_dncInvariance on the two
  structural presentations. This is a unique choice with its entire published
  coordinate identity condition; it is not a choice from bare Nonempty.
- The vector clause ranges over presentations of that same normal cone by a
  rank-d finite locally free F and an isomorphism over X. It asserts equality
  of the actual diagonal orientations on the presentation, retaining
  VectorBundleDiagonalOrientationConclusion on both presentations. Unfolding
  that predicate gives precisely inverse orientation = transported adjunct of
  the actual vectorBundleIntegration, for every normalized twist transport t.
  This retains the integration/counit normalization, not an arbitrary endpoint iso.
- The root clause compares the actual proEtaleRootsOfUnityTower on the unchanged
  underlying scheme after retagging. The entire functor includes all positive
  levels and its power transitions. diagonalTwist is the recorded ordered
  root-line tensor-power presentation A(d)[2d]; no generator is introduced.
  The coefficient constants, tensor powers, and Tate pullback identifications
  have only the underlying scheme as geometric input. Likewise the exceptional
  functor uses the same underlying chosen compactification (HasCompactification
  is Prop); its comparison and counit are the published ones. Thus no extra
  adjoint choice or equality of independently chosen adjoints is assumed.

Dependency declarations read and reused (names below lie in their usual namespaces):

| Node | Module and declaration |
| --- | --- |
| def-pur-conventions | Sheaf.Paper.PurityFiniteSetting: WeilConjectures.PurityFiniteSetting, Ring, Coefficient |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType / QuasiCompact: LocallyOfFiniteType, QuasiCompact |
| def-weil-proper-morphism | Mathlib.AlgebraicGeometry.Morphisms.Proper: IsSeparated (no IsProper hypothesis) |
| def-sbc-smooth-morphisms | Mathlib.AlgebraicGeometry.Morphisms.Smooth: SmoothOfRelativeDimension |
| def-coefficient-twists-detailed | Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted, with FixedFinitePositiveCoefficientTwist reexported via the diagonal interface: diagonalTwist, diagonalTwistEtale; Scheme.proEtaleRootsOfUnityTower |
| def-weil-exceptional-inverse-image | Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients: ConstructibleExceptionalCoefficients.System and its fixed finite realization, used by diagonalDualizing |
| def-weil-etale-morphism | Mathlib.AlgebraicGeometry.Morphisms.Etale: Etale |
| def-sbc-affine-space | mathlib_match Mathlib.AlgebraicGeometry.AffineSpace: AffineSpace, with ULift (Fin d) |
| def-pur-smooth-purity-map | Sheaf.Paper.SmoothPurityMap reuses the same normalized diagonalDualizingObject; no copy of gamma or Pi |
| def-pur-dnc-section-family | Sheaf.Paper.PurityDncFamilyIntrinsic: purityDncIntrinsicSource, Map, Section, Family |
| def-pur-section-invariant | Sheaf.Paper.PuritySectionInvariantIntrinsic: sectionInvariantFinite |
| thm-pur-dnc-invariance | Sheaf.Paper.PurityDncInvariance: Dnc.existsUnique_dncInvariance, with Dnc.normalSection, fibreOne, fibreZero from the recorded geometry realization |
| det-sp-orientation-vector-bundle | Sheaf.Paper.VectorBundleDiagonalOrientation: VectorBundleDiagonalOrientationConclusion |
| det-sp-orientation-charts | Sheaf.Paper.DiagonalOrientationCharts: DiagonalOrientationChartsConclusion and diagonalOrientationCharts |
| def-pur-normal-bundle | Sheaf.Paper.PurityNormalProjection: Scheme.Hom.purityNormalProjection, canonical normalConeProj and the actual ideal normalCone |
| def-pc-fibre-product | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback: pullback, fst, diagonal |
| def-weil-abstract-derived-category | Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory, HasDerivedCategory |

Every recorded statement-dependency module is publicly imported (FiniteType and
QuasiCompact are reexported by Proper). The proof-only trace, integration, affine
trace, regular diagonal, site-comparison, composite-adjunction and Noetherian
modules are plain imports. DNC geometry is already public through DNC invariance.
The seven-step proof docstring follows the accepted proof without new theorem
obligations or unsupported sorry inside definitions.

Edge cases checked: sigma = identity, d = 0 (empty coordinate type and identity
ordered trace), f = identity, empty U or V, empty schemes and disconnected schemes.
There is no positive-dimension binder, selected root, selected basis, selected
orientation, extra exceptional-adjoint admissibility or ramification-divisibility
hypothesis. The small site retains object universe u+1 and morphism universe u;
coefficients are the published u+1 lift. The source and target structural maps are
explicit because the statement compares two presentations of them.

Searches actually run with batch2/msearch.py and recorded in searches.jsonl:
LeanFinder, “Retagging a smooth scheme morphism by a ground field automorphism
preserves normalized diagonal purity orientations on etale coordinate charts”
returned eight ordinary scheme smoothness, etaleness, diagonal and standard-etale
presentation hits; none gives this derived normalized comparison. Loogle query
`"orientation", "Scheme"` and grep query
`retag|diagonalOrientation|smoothPurity|integrationOrientation` each returned zero.
The interrupted LeanFinder process was checked through its completed JSONL log,
not rerun. Direct rg of lean/WeilConjectures and lean/Sheaf for the same concepts
found generic smoothPurityIso, the existing diagonal/DNC interfaces and the tower
operations retagging theorem. The latter concerns operations and coefficients,
not this normalized diagonal comparison. Direct rg for the item id and the proposed
names in WeilConjectures, Sheaf and dag/lean_names_upstream.json found no duplicate.
No missing notion or unusable dependency required a new or repaired DAG node.

No STATEMENT-DISPUTED issue or statement correction was found. The normal bundle
at d=0 is interpreted by the actual cone/zero-section construction, not by the
positive-codimension auxiliary predicate in the regular-diagonal proof module.

Validation: the prescribed scompile.py compiled this one module separately in
sandbox mode and its actual library module mode with no errors or warnings.
The only theorem proof is sorry, as required by stage 2.

## Second reading by Q93

I reread the node and the completed file in a separate pass. This is an in-session
second reading; the dispatcher forbids starting another agent, and the maintainer's
independent review remains external to this delivery.

I checked in particular the direction Pi: exceptional coefficient unit to shifted
Tate line, the restriction by U.ι, and the positive shift 2d. I checked `_hE` against
the fixed-ring vector and chart statements and used the bottom subextension,
not an arbitrary coefficient field or ZMod with an unrecorded coefficient bridge.
The Kummer line is intrinsic: the whole published roots tower is compared, so
power transitions are retained and an automorphism of a chosen generator cannot
silently enter. The unique DNC arrow is selected from a uniqueness theorem, whose
normalization and base-change condition were read in full. Neither its input nor
its conclusion assumes the retagging equality being stated here.

The accepted split is not reopened. In the first pass only reexported statement
imports were present; this pass made the recorded statement-dependency imports
explicit. The server compile remains the check for all explicit universes,
instances and dependent equalities. No mathematical hypothesis or clause was
changed in the node. The geometry is shared constructed data, while the selected
normalized DNC and diagonal arrows are explicitly compared. The normal-cone
presentation clause compares normalized vector orientations on both presentations,
not a conditional comparison of arbitrary input orientations. I found no remaining
signature mismatch in the rereading.
