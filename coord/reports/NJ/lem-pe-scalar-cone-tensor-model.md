## Worker report

Item: `lem-pe-scalar-cone-tensor-model`, group NJ, stage 2.
Module: `Sheaf.Algebra.Homology.ScalarConeTensorModel`.
Primary declaration: `DerivedCategory.scalarCone_totalTensor_model`.
Helper: `DerivedCategory.scalarConeCochainFunctor`.

The theorem states the entire node, including its final compatible descent clause.
It has one `sorry`; its docstring gives all six proof steps from the DAG. The helper
has real data: objects are Mathlib mapping cones and maps are the mapping-cone maps
of the scalar-commuting diagonal squares. Its functor laws use the existing
`CochainComplex.mappingCone.map_id` and `map_comp` lemmas. No new notion is copied.
The node copy changes only `lean`; no statement correction or dependency repair was needed.

Hypotheses, matched individually:

* The arbitrary category is `A : Type u` with `Category.{v} A`. Abelian is
  `[Abelian A]`; Grothendieck is `[IsGrothendieckAbelian.{v} A]`.
* Monoidal, closed, braided, and additive tensor are respectively
  `[MonoidalCategory A]`, `[MonoidalClosed A]`, `[BraidedCategory A]`, and
  `[MonoidalPreadditive A]`.
* Functorial flat resolutions are `[Abelian.HasFunctorialFlatResolution A]`.
* The commutative scalar ring is `B : Type r` with `[CommRing B]`. Its linear
  action is `[Linear B A]`; the two tensor scalar identities are
  `[MonoidalLinear B A]`, whose two whiskering axioms are exactly linearity in
  either factor. The scalar itself is the explicit argument `(b : B)`.
* `[HasDerivedCategory.{v} A]` specifies the chosen localization, as in the
  source module's binder context at lines 37–42. This is the usual morphism
  universe for a Grothendieck category; it does not equate the category's object
  universe `u`, morphism universe `v`, or scalar universe `r`.

Clauses, matched individually:

* `P_b = Cone(b : 1[0] → 1[0])` is the existing `DerivedCategory.scalarCone b`,
  read at TensorMappingCone.lean:55–57. It uses `HomologicalComplex.single`
  and the existing Mathlib `CochainComplex.mappingCone` convention. Mathlib's
  biproduct construction orders the shifted source first; swapping the two
  summands identifies this with the node's target-first matrix convention.
* Two-sided K-flatness is literally the dependency's
  `CochainComplex.IsKFlatForTotalTensor (scalarCone b)` as the first conjunct.
  Its definition tests every quasi-isomorphism under both `tensorHom (𝟙 P) s`
  and `tensorHom s (𝟙 P)`, without boundedness restrictions.
* The cochain model is `Φ : tensorRight (scalarCone b) ≅ scalarConeCochainFunctor b`.
  `tensorRight` here is the cochain monoidal structure's binary direct-sum total
  tensor. Its underlying objects/maps are Mathlib `tensorObj`/`tensorHom`, the
  same construction used by the recorded K-flat predicate. The helper's object
  is exactly `mappingCone (b • 𝟙 C)` and its map is the diagonal cone map.
* Naturality in every chain map is part of `Φ` being a natural isomorphism,
  rather than merely a separate family of objectwise isomorphisms.
* The localized model is the natural isomorphism
  `θ : Q ⋙ tensorRight (Q.obj (scalarCone b)) ≅ scalarConeCochainFunctor b ⋙ Q`.
  The tensor on the derived category is the recorded K-flat derived structure.
* The formula `θ.hom.app C = Functor.LaxMonoidal.μ Q C (scalarCone b) ≫
  Q.map (Φ.hom.app C)` explicitly requires the canonical K-flat tensor
  comparison followed by the localized cochain model. Thus the statement does
  not replace that comparison by an unspecified map.
* Inversion of quasi-isomorphisms after localization is the exact
  `IsInvertedBy (scalarConeCochainFunctor b ⋙ Q)` conjunct, for
  `HomologicalComplex.quasiIso A (.up ℤ)`.
* The descended functor is the existential `F : DerivedCategory A ⥤ DerivedCategory A`,
  with `η : Q ⋙ F ≅ scalarConeCochainFunctor b ⋙ Q`.
* Its natural identification with right derived tensor is
  `δ : tensorRight (Q.obj (scalarCone b)) ≅ F`. The equation
  `δ.hom.app (Q.obj C) ≫ η.hom.app C = θ.hom.app C` retains the node's
  compatibility with the displayed localized isomorphisms on all representatives.

Dependency declarations read and used:

* `def-sp-grothendieck-abelian`: Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic,
  `CategoryTheory.IsGrothendieckAbelian`, including its small-colimit instance.
* `def-sfb-monoidal-category`: Mathlib.CategoryTheory.Monoidal.Category,
  `CategoryTheory.MonoidalCategory`, its tensor, unitors, associator and laws.
* `lem-sfb-derived-monoidal`:
  WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory,
  `DerivedCategory.hasDerivedMonoidalCategory`, with its enclosing assumptions.
  It is imported through TensorMappingCone and supplies the derived monoidal structure.
* `def-weil-abstract-derived-category`: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`, and its localization
  instance; Mathlib's cochain cone and diagonal maps supply the stated cone conventions.
* `def-sfb-preserves-kflat-quasi-iso`:
  Sheaf.Algebra.Homology.PreservesTotalTensorKFlatQuasiIso,
  `CochainComplex.IsKFlatForTotalTensor`. This is used directly, not the upstream
  homotopy-category `MorphismProperty.kFlat` predicate.

All stated proof dependencies are imported: Mathlib HomologySequence,
HomologySequenceLemmas, Abelian.DiagramLemmas.Four, and Localization.Predicate.
Their recorded declarations were read: `ShortComplex.ShortExact.homology_exact₂`,
`HomologicalComplex.HomologySequence.δ_naturality`,
`Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`, and `Localization.lift`/`fac`.

Sources read: the complete upstream TensorMappingCone.lean, the dependency modules,
and main-20261015 `sk-lem-pe-derived-nakayama-resolution.md` with its proof. The
latter's paragraph “On X” is the scalar-cone calculation served by this node.

Edge cases checked before writing:

* `b = 0`: the cone is the two-term zero-differential unit complex; tensoring
  gives the direct sum of C and C[1]. There is no nonzero-scalar assumption.
* `b` a unit (including `b = 1`): the scalar cone is contractible. The theorem
  permits it and the localized model is zero, as it should be.
* A zero scalar ring or a zero category is not excluded. Linearity then forces
  the appropriate identities to vanish; no nontriviality assumption is present.
* `C = 0`, arbitrary unbounded C, and arbitrary chain maps are included.
* Neither a domain assumption nor regularity of `b`, exact tensoring of arbitrary
  objects, an injective scalar map, or boundedness is introduced.
* Object, morphism, and scalar universes are bound explicitly and independently.
  Countable coproducts and the cochain tensor structure are obtained from the
  given Grothendieck/closed braided hypotheses; no extra tensor structure is assumed.

Searches actually run (2026-10-21):

* msearch leanfinder: “The cone of a scalar on the tensor unit is K-flat and total
  tensor with it is naturally the scalar mapping cone on an unbounded cochain
  complex”. Eight hits, including mappingCone, mappingCone.triangle,
  cm5b.i/p, and mapHomologicalComplexXIso; none states this full result.
* msearch loogle: `CochainComplex.mappingCone, HomologicalComplex.tensorObj`.
  Zero hits.
* msearch grep: `scalarCone|tensorScalarCone|mappingConeFunctor`. Zero Mathlib hits.
* msearch leansearch: “Tensoring with the cone of scalar multiplication gives the
  mapping cone of scalar multiplication naturally”. Eight hits, including
  mappingCone and ordinary module tensor scalar identities; no full match.
* Direct rg in lean/WeilConjectures and lean/Sheaf for scalarCone,
  tensorScalarCone, and mappingConeFunctor found the upstream TensorMappingCone
  declarations and the bounded-below arrow cone functor. Direct rg for this
  node id in WeilConjectures found no match. The former are reused through
  their module; the latter is a different domain (bounded-below arrows).
* Read upstream tensorScalarConeIso' and its naturality, isIso_μ_scalarCone,
  tensorScalarConeIso and its naturality. They provide the cochain/localized
  isomorphisms individually, but upstream kFlat_scalarCone uses the
  homotopy-category predicate and no declaration packages the node's final
  descent with compatibility. Therefore an existing-only attachment would miss
  clauses of this node; this delivery states that whole result on their objects.

Validation: scompile.py compiled the delivered file both as a sandbox module and
with its intended library name, cleanly (2.3 s and 2.6 s). No errors or warnings.
There are no STATEMENT-DISPUTED findings or node faults.

## Second reading by NJ

Worker's second pass; the maintainer supplies the independent delivery review.
Reopened the node and the final Lean file and matched the assumptions and each
clause as above. Checked that Φ and θ are natural isomorphisms of the actual
cochain and derived functors, that the equality uses localization's μ, that the
K-flat predicate is the recorded two-sided predicate, and that δ and η recover
θ on every representative. The whole node is retained without correction.
The cone functor uses the actual diagonal square, so no arbitrary cone map is
assumed. All theorem proofs remain `sorry`; the only helper has full functor data.
