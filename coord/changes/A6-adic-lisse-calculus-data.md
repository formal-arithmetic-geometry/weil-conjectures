# AlgebraicGeometry.Scheme.AdicLisseCalculusModels and companion data

## Reason

Independent realization, tensor and dual source lemmas need the same normalized models.
Keeping those definitions in the theorem module would force an import cycle. Move them
verbatim into `Sheaf.Paper.AdicLisseCalculusData`, and publicly reexport that module from
`Sheaf.Paper.AdicLisseCohomologyCalculus`. The data below are textually identical before
and after the move, including all proof arguments, fields and normalizations. No data
is chosen from any new existence theorem. The three new comparison theorems are used only
inside the original theorem's proof.

All original public imports are retained through the public data reexport. Private
proof imports that none of these data declarations uses are removed. Existing public
names, signatures, attributes, structure fields and definition bodies are unchanged.
No theorem of Challenge.lean changes. Because target-dependent definition ownership is
moved, the independent statement reader should verify this literal equality as required
by AGENTS.md; the actual mathematical definitions remain identical.

No adopted-source file changes. No module held by another group is adapted. The old
rework quarantine path is preserved; no path is withdrawn or listed for deletion.

Reviewer correction (cc review, 2026-10-25): the structure `AdicLisseCohomologyCalculus`
is the statement of the theorem node `lem-per-adic-lisse-cohomology-calculus`, not model
data, and none of the three new lemmas uses it. It therefore stays, byte for byte, in
`Sheaf.Paper.AdicLisseCohomologyCalculus` and in that node's `lean.declarations`; only the
model definitions and `adicCalculusTensor` (listed under Old up to `AdicLisseCalculusModels`)
move to `Sheaf.Paper.AdicLisseCalculusData`, owned by `def-zl-adic-lisse-calculus-models`.

## Old

The following declarations were in `Sheaf.Paper.AdicLisseCohomologyCalculus`:

```lean
/-- The coefficient prime is invertible in residue fields because it is a unit in each
stalk. This supplies the interface used by the recorded lisse and completed operations.
Source: scheme coefficient conventions
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
noncomputable instance adicCalculusPrimeInvertible (x : X) :
    Invertible (l : X.residueField x) :=
  (Eq.mp (congrArg IsUnit (map_natCast (X.residue x).hom l))
    ((hInv.out x).map (X.residue x).hom)).invertible

/-- Integral localization followed by the recorded common-stage inclusion.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralInclusion (E : Padic.FiniteCoefficientFields l Qbar) :
    pbcIntegralStage.{u, u + 1} l Qbar X E ⥤ pbcQbarCategory.{u + 1, u} l Qbar X :=
  pbcStageLocalization.{u, u + 1} l Qbar X E ⋙ (pbcScalarSystem l Qbar X hDim.out hInv.out).ι E

/-- Integral cohomology, retained as a degree-zero object of the completed category.
Source: Bhatt--Scholze 6.8.11; localized t-structure
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralCohomology (E : Padic.FiniteCoefficientFields l Qbar) (a : ℤ) :
    pbcIntegralStage.{u, u + 1} l Qbar X E ⥤ pbcIntegralStage.{u, u + 1} l Qbar X E :=
  shiftFunctor _ a ⋙ (pbcIntegralTStructure.{u} X l (pbcFiniteField.{u} l Qbar E)).homology₀ ⋙
    ObjectProperty.ι _

/-- The actual inverse-limit realization; the identity direct image in the existing
level functor identifies the étale site with itself before passage to the pro-étale site.
Source: Bhatt--Scholze 6.8.4(1),(4)
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralRealization (E : Padic.FiniteCoefficientFields l Qbar) :
    LisseIntegralSheaf l E.val X ⥤ pbcAmbientStage.{u, u + 1} l Qbar X E :=
  ObjectProperty.ι _ ⋙
    (Functor.whiskeringRight _ _ _).obj (middleExtensionLevelFunctor l Qbar E (𝟙 X)) ⋙
    lim ⋙ DerivedCategory.singleFunctor
      (pbcModules X (pbcAdicCompletion X (pbcStageDatum.{u} l Qbar E))) 0

/-- Restriction to the exact bounded constructible complete category. The argument is
only the membership proof; all object and map data are the specified inverse limit.
Source: Bhatt--Scholze 6.8.4,6.8.11
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralRealizationLift (E : Padic.FiniteCoefficientFields l Qbar)
    (h : ∀ F : LisseIntegralSheaf l E.val X,
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Qbar E)
        ((adicCalculusIntegralRealization l Qbar X E).obj F)) :
    LisseIntegralSheaf l E.val X ⥤ pbcIntegralStage.{u, u + 1} l Qbar X E :=
  ObjectProperty.lift _ (adicCalculusIntegralRealization l Qbar X E) h

/-- The canonical integral coefficient-presentation transport, restricted by a membership
proof. There is no independent choice of a coefficient model or of a map.
Source: Bhatt--Scholze 6.8.11; completed coefficient presentation transport
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralModel (E : Padic.FiniteCoefficientFields l Qbar)
    (h : ∀ K : pbcIntegralStage.{u, u + 1} l Qbar X E,
      sfIntegralConstructible l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X
        ((purCoefficientModel.{u} l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X).functor.obj K.obj)) :
    pbcIntegralStage.{u, u + 1} l Qbar X E ⥤
      sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X :=
  ObjectProperty.lift _
    (pbcStageInclusion.{u, u + 1} l Qbar X E ⋙
      (purCoefficientModel.{u} l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X).functor) h

/-- Geometric fibres use completed derived pullback, degree-zero cohomology, and sections
on the geometric point; only then are coefficients extended to the algebraic closure.
In particular this definition does not commute an ordinary stalk with an inverse limit.
Source: Bhatt--Scholze 6.8.4 and the normalized point-sections construction
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralFiber (E : Padic.FiniteCoefficientFields l Qbar)
    (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X) :
    pbcIntegralStage.{u, u + 1} l Qbar X E ⥤ ModuleCat.{u + 1} Qbar :=
  pbcStageInclusion.{u, u + 1} l Qbar X E ⋙
    pbcActualCompletedPull x (pbcStageDatum.{u} l Qbar E) ⋙
    (purCoefficientModel.{u} l (pbcFiniteField.{u} l Qbar E) (Spec (.of k))).functor ⋙
    DerivedCategory.homologyFunctor
      (integralTowerModules.{u, u} l (pbcFiniteField.{u} l Qbar E) (Spec (.of k))) 0 ⋙
    pointCompletedSections k l (pbcFiniteField.{u} l Qbar E) ⋙
    ModuleCat.extendScalars
      (E.val.subtype.comp ((Shrink.algEquiv ℚ_[l] E.val).toRingHom.comp
        (Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Qbar E)).subtype))

/-- Transport of the recorded completed common-stage tensor to the exact pbc presentation.
Source: Bhatt--Scholze 6.8.15
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusTensor
    (C : pbcQbarCategory.{u + 1, u} l Qbar X ≌
      generalAlgebraicallyClosedConstructibleCategory l Qbar X) :
    pbcQbarCategory.{u + 1, u} l Qbar X × pbcQbarCategory.{u + 1, u} l Qbar X ⥤
      pbcQbarCategory.{u + 1, u} l Qbar X :=
  (C.functor.prod C.functor) ⋙ commonStageDerivedTensor l Qbar X ⋙ C.inverse

/-- Normalized models for the adic lisse calculation.
The integral normalization fixes the coefficient presentation, cohomology, realization,
and fibres; global functoriality expresses independence of representatives and finite
coefficient extension in the recorded common-stage localizations.
Source: Bhatt--Scholze 6.8.1--6.8.15 and the lisse tensor argument in the blueprint
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
structure AdicLisseCalculusModels where
  /-- The existing coefficient model preserves the exact integral predicate. -/
  model_mem : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (K : pbcIntegralStage.{u, u + 1} l Qbar X E),
    sfIntegralConstructible l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X
      ((purCoefficientModel.{u} l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X).functor.obj K.obj)
  /-- The equivalence of the two recorded coefficient presentations. -/
  comparison : pbcQbarCategory.{u + 1, u} l Qbar X ≌
    generalAlgebraicallyClosedConstructibleCategory l Qbar X
  /-- At every integral stage the equivalence is the specified coefficient transport. -/
  comparison_integral : ∀ E : Padic.FiniteCoefficientFields l Qbar,
    adicCalculusIntegralInclusion l Qbar X E ⋙ comparison.functor ≅
      adicCalculusIntegralModel l Qbar X E (model_mem E) ⋙
        sfRationalConstructibleLocalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X ⋙
          (GeneralAlgebraicallyClosedCoefficients.stageSystem.{u, u + 1} l Qbar X).ι E
  /-- Inverse-limit lisse realizations have uniform constructible reduction towers. -/
  realization_mem : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : LisseIntegralSheaf l E.val X),
    PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Qbar E)
      ((adicCalculusIntegralRealization l Qbar X E).obj F)
  /-- Realization on the coefficient-localized adic lisse category. -/
  realization : LisseAlgebraicSheaf l X Qbar ⥤ pbcQbarCategory.{u + 1, u} l Qbar X
  /-- Its values are the integral inverse-limit realizations, rationalized. -/
  realization_integral : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : LisseIntegralSheaf l E.val X),
    realization.obj (lisseAlgebraicOfModel l X Qbar E ⟨F⟩) ≅
      (adicCalculusIntegralInclusion l Qbar X E).obj
        ((adicCalculusIntegralRealizationLift l Qbar X E (realization_mem E)).obj F)
  /-- Morphisms are the prescribed rationalization of integral morphisms. -/
  realization_map : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F G : LisseIntegralSheaf l E.val X) (a : E.val) (f : F ⟶ G),
    realization.map (lisseAlgebraicModelMap l X Qbar E
        (F := ⟨F⟩) (H := ⟨G⟩) (TensorProduct.tmul _ a f)) =
      (realization_integral E F).hom ≫
        pbcQbarScalarAction l Qbar X (E.val.subtype a)
          ((adicCalculusIntegralInclusion l Qbar X E).map
            ((adicCalculusIntegralRealizationLift l Qbar X E (realization_mem E)).map f)) ≫
        (realization_integral E G).inv
  /-- Adic cohomology is defined on the coefficient quotient, in every integer degree. -/
  cohomology : ℤ → pbcQbarCategory.{u + 1, u} l Qbar X ⥤ pbcQbarCategory.{u + 1, u} l Qbar X
  /-- It is exactly integral cohomology followed by rationalization at each finite field. -/
  cohomology_integral : ∀ (E : Padic.FiniteCoefficientFields l Qbar) (a : ℤ),
    adicCalculusIntegralInclusion l Qbar X E ⋙ cohomology a ≅
      adicCalculusIntegralCohomology l Qbar X E a ⋙
        adicCalculusIntegralInclusion l Qbar X E
  /-- Lisse realization is in degree zero, including the zero-rank case. -/
  realization_cohomology : ∀ (L : LisseAlgebraicSheaf l X Qbar),
    (cohomology 0).obj (realization.obj L) ≅ realization.obj L
  /-- All other cohomology of a lisse realization vanishes. -/
  realization_vanishing : ∀ (L : LisseAlgebraicSheaf l X Qbar) (a : ℤ), a ≠ 0 →
    IsZero ((cohomology a).obj (realization.obj L))
  /-- The geometric fibre on the coefficient quotient. -/
  fiber : ∀ (k : Type u) [Field k] [IsAlgClosed k] (_x : Spec (.of k) ⟶ X),
    pbcQbarCategory.{u + 1, u} l Qbar X ⥤ ModuleCat.{u + 1} Qbar
  /-- At each finite stage this is completed pullback followed by point sections. -/
  fiber_integral : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X)
    (E : Padic.FiniteCoefficientFields l Qbar),
    adicCalculusIntegralInclusion l Qbar X E ⋙ fiber k x ≅
      adicCalculusIntegralFiber l Qbar X E k x
  /-- On lisse sheaves it agrees with the already recorded adic fibre functor. -/
  fiber_lisse : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X),
    realization ⋙ fiber k x ≅ lisseAlgebraicFiberFunctor l X x Qbar

/-- The tensor, cohomology, fibre and linear-dual calculations for the normalized models.
Source: Bhatt--Scholze 6.8.4, 6.8.14--6.8.15; blueprint lisse tensor permanence
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
structure AdicLisseCohomologyCalculus extends AdicLisseCalculusModels l Qbar X where
  /-- Natural cohomology/tensor comparison, with values still in the exact pbc category. -/
  tensor_cohomology : ∀ a : ℤ,
    ((𝟭 (pbcQbarCategory.{u + 1, u} l Qbar X)).prod realization) ⋙
        adicCalculusTensor l Qbar X comparison ⋙ cohomology a ≅
      ((cohomology a).prod realization) ⋙ adicCalculusTensor l Qbar X comparison
  /-- Fibrewise tensor with a lisse realization is ordinary coefficient tensor. -/
  ordinary_tensor_fiber : ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (x : Spec (.of k) ⟶ X),
    ((𝟭 (pbcQbarCategory.{u + 1, u} l Qbar X)).prod realization) ⋙
        adicCalculusTensor l Qbar X comparison ⋙ fiber k x ≅
      ((fiber k x).prod (lisseAlgebraicFiberFunctor l X x Qbar)) ⋙
        MonoidalCategory.tensor (ModuleCat.{u + 1} Qbar)
  /-- The tensor comparison on geometric fibres, natural in both arguments. -/
  tensor_fiber : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X)
    (a : ℤ),
    ((𝟭 (pbcQbarCategory.{u + 1, u} l Qbar X)).prod realization) ⋙
        adicCalculusTensor l Qbar X comparison ⋙ cohomology a ⋙ fiber k x ≅
      (((cohomology a ⋙ fiber k x).prod (lisseAlgebraicFiberFunctor l X x Qbar)) ⋙
        (MonoidalCategory.tensor (ModuleCat.{u + 1} Qbar)))
  /-- The displayed fibre calculation is induced by the cohomology comparison. -/
  tensor_fiber_induced : ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (x : Spec (.of k) ⟶ X) (a : ℤ) (K : pbcQbarCategory.{u + 1, u} l Qbar X)
    (L : LisseAlgebraicSheaf l X Qbar),
    (tensor_fiber k x a).hom.app (K, L) =
      (fiber k x).map ((tensor_cohomology a).hom.app (K, L)) ≫
        (ordinary_tensor_fiber k x).hom.app ((cohomology a).obj K, L)
  /-- The contravariant linear dual remains a finite-rank adic lisse sheaf. -/
  dual : (LisseAlgebraicSheaf l X Qbar)ᵒᵖ ⥤ LisseAlgebraicSheaf l X Qbar
  /-- Its fibre is the ordinary coefficient-linear dual. -/
  dual_fiber : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X)
    (L : LisseAlgebraicSheaf l X Qbar),
    (lisseAlgebraicFiberFunctor l X x Qbar).obj (dual.obj (op L)) ≅
      ModuleCat.of Qbar (Module.Dual Qbar ((lisseAlgebraicFiberFunctor l X x Qbar).obj L))
  /-- Naturality of fibre duality is precomposition with the original fibre map. -/
  dual_fiber_naturality : ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (x : Spec (.of k) ⟶ X) (L M : LisseAlgebraicSheaf l X Qbar) (f : L ⟶ M),
    (lisseAlgebraicFiberFunctor l X x Qbar).map (dual.map f.op) ≫
        (dual_fiber k x L).hom =
      (dual_fiber k x M).hom ≫ ModuleCat.ofHom
        (LinearMap.dualMap ((lisseAlgebraicFiberFunctor l X x Qbar).map f).hom)
  /-- The internal dual belongs to the constructible-Hom domain. -/
  dual_permitted : ∀ L : LisseAlgebraicSheaf l X Qbar,
    commonStageHomPairs l Qbar X
      (op (comparison.functor.obj (realization.obj L)),
        comparison.functor.obj (realization.obj (lisseAlgebraicUnit l X Qbar)))
  /-- The degree-zero linear dual realizes the recorded coefficient derived dual. -/
  dual_realization : ∀ L : LisseAlgebraicSheaf l X Qbar,
    realization.obj (dual.obj (op L)) ≅ comparison.inverse.obj
      ((commonStageDerivedInternalHom l Qbar X).obj
        ⟨(op (comparison.functor.obj (realization.obj L)),
          comparison.functor.obj (realization.obj (lisseAlgebraicUnit l X Qbar))),
          dual_permitted L⟩)

  /-- Naturality of the derived-dual identification, including coefficient-change isomorphisms. -/
  dual_realization_naturality : ∀ (L M : LisseAlgebraicSheaf l X Qbar) (f : L ⟶ M),
    realization.map (dual.map f.op) ≫ (dual_realization L).hom =
      (dual_realization M).hom ≫ comparison.inverse.map
        ((commonStageDerivedInternalHom l Qbar X).map
          (ObjectProperty.homMk
            ((comparison.functor.map (realization.map f)).op,
              𝟙 (comparison.functor.obj (realization.obj (lisseAlgebraicUnit l X Qbar))))))
```

## New

The same declarations, except `AdicLisseCohomologyCalculus` (unchanged in the theorem
module), are in `Sheaf.Paper.AdicLisseCalculusData`:

```lean
/-- The coefficient prime is invertible in residue fields because it is a unit in each
stalk. This supplies the interface used by the recorded lisse and completed operations.
Source: scheme coefficient conventions
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
noncomputable instance adicCalculusPrimeInvertible (x : X) :
    Invertible (l : X.residueField x) :=
  (Eq.mp (congrArg IsUnit (map_natCast (X.residue x).hom l))
    ((hInv.out x).map (X.residue x).hom)).invertible

/-- Integral localization followed by the recorded common-stage inclusion.
Source: Bhatt--Scholze 6.8.14 (blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralInclusion (E : Padic.FiniteCoefficientFields l Qbar) :
    pbcIntegralStage.{u, u + 1} l Qbar X E ⥤ pbcQbarCategory.{u + 1, u} l Qbar X :=
  pbcStageLocalization.{u, u + 1} l Qbar X E ⋙ (pbcScalarSystem l Qbar X hDim.out hInv.out).ι E

/-- Integral cohomology, retained as a degree-zero object of the completed category.
Source: Bhatt--Scholze 6.8.11; localized t-structure
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralCohomology (E : Padic.FiniteCoefficientFields l Qbar) (a : ℤ) :
    pbcIntegralStage.{u, u + 1} l Qbar X E ⥤ pbcIntegralStage.{u, u + 1} l Qbar X E :=
  shiftFunctor _ a ⋙ (pbcIntegralTStructure.{u} X l (pbcFiniteField.{u} l Qbar E)).homology₀ ⋙
    ObjectProperty.ι _

/-- The actual inverse-limit realization; the identity direct image in the existing
level functor identifies the étale site with itself before passage to the pro-étale site.
Source: Bhatt--Scholze 6.8.4(1),(4)
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralRealization (E : Padic.FiniteCoefficientFields l Qbar) :
    LisseIntegralSheaf l E.val X ⥤ pbcAmbientStage.{u, u + 1} l Qbar X E :=
  ObjectProperty.ι _ ⋙
    (Functor.whiskeringRight _ _ _).obj (middleExtensionLevelFunctor l Qbar E (𝟙 X)) ⋙
    lim ⋙ DerivedCategory.singleFunctor
      (pbcModules X (pbcAdicCompletion X (pbcStageDatum.{u} l Qbar E))) 0

/-- Restriction to the exact bounded constructible complete category. The argument is
only the membership proof; all object and map data are the specified inverse limit.
Source: Bhatt--Scholze 6.8.4,6.8.11
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralRealizationLift (E : Padic.FiniteCoefficientFields l Qbar)
    (h : ∀ F : LisseIntegralSheaf l E.val X,
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Qbar E)
        ((adicCalculusIntegralRealization l Qbar X E).obj F)) :
    LisseIntegralSheaf l E.val X ⥤ pbcIntegralStage.{u, u + 1} l Qbar X E :=
  ObjectProperty.lift _ (adicCalculusIntegralRealization l Qbar X E) h

/-- The canonical integral coefficient-presentation transport, restricted by a membership
proof. There is no independent choice of a coefficient model or of a map.
Source: Bhatt--Scholze 6.8.11; completed coefficient presentation transport
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralModel (E : Padic.FiniteCoefficientFields l Qbar)
    (h : ∀ K : pbcIntegralStage.{u, u + 1} l Qbar X E,
      sfIntegralConstructible l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X
        ((purCoefficientModel.{u} l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X).functor.obj K.obj)) :
    pbcIntegralStage.{u, u + 1} l Qbar X E ⥤
      sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X :=
  ObjectProperty.lift _
    (pbcStageInclusion.{u, u + 1} l Qbar X E ⋙
      (purCoefficientModel.{u} l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X).functor) h

/-- Geometric fibres use completed derived pullback, degree-zero cohomology, and sections
on the geometric point; only then are coefficients extended to the algebraic closure.
In particular this definition does not commute an ordinary stalk with an inverse limit.
Source: Bhatt--Scholze 6.8.4 and the normalized point-sections construction
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusIntegralFiber (E : Padic.FiniteCoefficientFields l Qbar)
    (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X) :
    pbcIntegralStage.{u, u + 1} l Qbar X E ⥤ ModuleCat.{u + 1} Qbar :=
  pbcStageInclusion.{u, u + 1} l Qbar X E ⋙
    pbcActualCompletedPull x (pbcStageDatum.{u} l Qbar E) ⋙
    (purCoefficientModel.{u} l (pbcFiniteField.{u} l Qbar E) (Spec (.of k))).functor ⋙
    DerivedCategory.homologyFunctor
      (integralTowerModules.{u, u} l (pbcFiniteField.{u} l Qbar E) (Spec (.of k))) 0 ⋙
    pointCompletedSections k l (pbcFiniteField.{u} l Qbar E) ⋙
    ModuleCat.extendScalars
      (E.val.subtype.comp ((Shrink.algEquiv ℚ_[l] E.val).toRingHom.comp
        (Padic.coefficientExtensionIntegers l (pbcFiniteField.{u} l Qbar E)).subtype))

/-- Transport of the recorded completed common-stage tensor to the exact pbc presentation.
Source: Bhatt--Scholze 6.8.15
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
def adicCalculusTensor
    (C : pbcQbarCategory.{u + 1, u} l Qbar X ≌
      generalAlgebraicallyClosedConstructibleCategory l Qbar X) :
    pbcQbarCategory.{u + 1, u} l Qbar X × pbcQbarCategory.{u + 1, u} l Qbar X ⥤
      pbcQbarCategory.{u + 1, u} l Qbar X :=
  (C.functor.prod C.functor) ⋙ commonStageDerivedTensor l Qbar X ⋙ C.inverse

/-- Normalized models for the adic lisse calculation.
The integral normalization fixes the coefficient presentation, cohomology, realization,
and fibres; global functoriality expresses independence of representatives and finite
coefficient extension in the recorded common-stage localizations.
Source: Bhatt--Scholze 6.8.1--6.8.15 and the lisse tensor argument in the blueprint
(blueprint: lem-per-adic-lisse-cohomology-calculus). -/
structure AdicLisseCalculusModels where
  /-- The existing coefficient model preserves the exact integral predicate. -/
  model_mem : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (K : pbcIntegralStage.{u, u + 1} l Qbar X E),
    sfIntegralConstructible l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X
      ((purCoefficientModel.{u} l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X).functor.obj K.obj)
  /-- The equivalence of the two recorded coefficient presentations. -/
  comparison : pbcQbarCategory.{u + 1, u} l Qbar X ≌
    generalAlgebraicallyClosedConstructibleCategory l Qbar X
  /-- At every integral stage the equivalence is the specified coefficient transport. -/
  comparison_integral : ∀ E : Padic.FiniteCoefficientFields l Qbar,
    adicCalculusIntegralInclusion l Qbar X E ⋙ comparison.functor ≅
      adicCalculusIntegralModel l Qbar X E (model_mem E) ⋙
        sfRationalConstructibleLocalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Qbar E) X ⋙
          (GeneralAlgebraicallyClosedCoefficients.stageSystem.{u, u + 1} l Qbar X).ι E
  /-- Inverse-limit lisse realizations have uniform constructible reduction towers. -/
  realization_mem : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : LisseIntegralSheaf l E.val X),
    PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Qbar E)
      ((adicCalculusIntegralRealization l Qbar X E).obj F)
  /-- Realization on the coefficient-localized adic lisse category. -/
  realization : LisseAlgebraicSheaf l X Qbar ⥤ pbcQbarCategory.{u + 1, u} l Qbar X
  /-- Its values are the integral inverse-limit realizations, rationalized. -/
  realization_integral : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F : LisseIntegralSheaf l E.val X),
    realization.obj (lisseAlgebraicOfModel l X Qbar E ⟨F⟩) ≅
      (adicCalculusIntegralInclusion l Qbar X E).obj
        ((adicCalculusIntegralRealizationLift l Qbar X E (realization_mem E)).obj F)
  /-- Morphisms are the prescribed rationalization of integral morphisms. -/
  realization_map : ∀ (E : Padic.FiniteCoefficientFields l Qbar)
    (F G : LisseIntegralSheaf l E.val X) (a : E.val) (f : F ⟶ G),
    realization.map (lisseAlgebraicModelMap l X Qbar E
        (F := ⟨F⟩) (H := ⟨G⟩) (TensorProduct.tmul _ a f)) =
      (realization_integral E F).hom ≫
        pbcQbarScalarAction l Qbar X (E.val.subtype a)
          ((adicCalculusIntegralInclusion l Qbar X E).map
            ((adicCalculusIntegralRealizationLift l Qbar X E (realization_mem E)).map f)) ≫
        (realization_integral E G).inv
  /-- Adic cohomology is defined on the coefficient quotient, in every integer degree. -/
  cohomology : ℤ → pbcQbarCategory.{u + 1, u} l Qbar X ⥤ pbcQbarCategory.{u + 1, u} l Qbar X
  /-- It is exactly integral cohomology followed by rationalization at each finite field. -/
  cohomology_integral : ∀ (E : Padic.FiniteCoefficientFields l Qbar) (a : ℤ),
    adicCalculusIntegralInclusion l Qbar X E ⋙ cohomology a ≅
      adicCalculusIntegralCohomology l Qbar X E a ⋙
        adicCalculusIntegralInclusion l Qbar X E
  /-- Lisse realization is in degree zero, including the zero-rank case. -/
  realization_cohomology : ∀ (L : LisseAlgebraicSheaf l X Qbar),
    (cohomology 0).obj (realization.obj L) ≅ realization.obj L
  /-- All other cohomology of a lisse realization vanishes. -/
  realization_vanishing : ∀ (L : LisseAlgebraicSheaf l X Qbar) (a : ℤ), a ≠ 0 →
    IsZero ((cohomology a).obj (realization.obj L))
  /-- The geometric fibre on the coefficient quotient. -/
  fiber : ∀ (k : Type u) [Field k] [IsAlgClosed k] (_x : Spec (.of k) ⟶ X),
    pbcQbarCategory.{u + 1, u} l Qbar X ⥤ ModuleCat.{u + 1} Qbar
  /-- At each finite stage this is completed pullback followed by point sections. -/
  fiber_integral : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X)
    (E : Padic.FiniteCoefficientFields l Qbar),
    adicCalculusIntegralInclusion l Qbar X E ⋙ fiber k x ≅
      adicCalculusIntegralFiber l Qbar X E k x
  /-- On lisse sheaves it agrees with the already recorded adic fibre functor. -/
  fiber_lisse : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (.of k) ⟶ X),
    realization ⋙ fiber k x ≅ lisseAlgebraicFiberFunctor l X x Qbar
```

The original theorem module now publicly imports that shared module:

```lean
public import Sheaf.Paper.AdicLisseCalculusData
```

## Users

Read-only query: `python3 tools/downstream.py Sheaf.Paper.AdicLisseCohomologyCalculus
--uses adicCalculusPrimeInvertible adicCalculusIntegralInclusion
adicCalculusIntegralCohomology adicCalculusIntegralRealization
adicCalculusIntegralRealizationLift adicCalculusIntegralModel adicCalculusIntegralFiber
adicCalculusTensor AdicLisseCalculusModels AdicLisseCohomologyCalculus`.
All five downstream modules are listed, including transitive importers. The only
external textual uses of the moved names are the prime-invertibility instance and
normalized model structure in NormalizedClassicalWeilRealization. Their definitions,
instances and typeclass behavior are unchanged. The other users retain identical
public imports and declarations. The target definitions therefore have the same
mathematical meanings, with no strengthened hypothesis or weakened conclusion.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.AnchoredPureCurveCriterion` | unclaimed in shared snapshot | Same public declarations through reexport; no adaptation. |
| `Sheaf.Paper.ClassicalWeilFiltrationHeartTransport` | unclaimed in shared snapshot | Same public declarations through reexport; no adaptation. |
| `Sheaf.Paper.GeometricQuotientWeilCompositionSeries` | unclaimed in shared snapshot | Same public declarations through reexport; no adaptation. |
| `Sheaf.Paper.NormalizedClassicalWeilRealization` | unclaimed in shared snapshot | Same public declarations through reexport; no adaptation. |
| `Sheaf.Paper.TateTwistSupportCondition` | unclaimed in shared snapshot | Same public declarations through reexport; no adaptation. |
| `Sheaf.Paper.AdicLisseCohomologyCalculus` | A6 (assigned item) | Public reexport and completed proof assembly. |
| `Sheaf.Paper.AdicLisseCalculusData` | A6 (new data module) | Verbatim relocated definitions. |
| `Sheaf.Paper.AdicLisseNormalizedModels` | A6 (new source lemma) | Uses shared normalized model structure. |
| `Sheaf.Paper.AdicLisseExactTensorComparisons` | A6 (new source lemma) | Uses shared tensor and model definitions. |
| `Sheaf.Paper.AdicLisseLinearDualComparisons` | A6 (new source lemma) | Uses shared normalized model structure. |

## Status

landed 20261025T003304-L-3225711 2026-10-25 (merge of deliver/A6/Sheaf.Paper.AdicLisseCohomologyCalculus)
