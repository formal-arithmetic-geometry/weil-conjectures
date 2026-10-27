# ArithmeticSystemRightAdjoint data records

## Reason

The ordinary floor-extension construction and the common-coefficient derived-limit
comparison are separate steps of the existing proof. Their public theorem statements
need the original records. Extract the records to a definition module so both steps
can be stated without importing the theorem that combines them, which would create
an import cycle. The existing three structures, their fields, universes, options,
visibility and instance attributes are unchanged. Add only an ordinary-data record
containing the eleven non-derived fields; the item itself proves the remaining four.
No existing definition or target changes meaning, so no target statement review is
reopened by this relocation.

## Old

In `lean/Sheaf/CategoryTheory/ArithmeticSystemRightAdjoint.lean`:

```lean
structure ArithmeticSystemScalarForgetting
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B) where
  functor : StrictRingSystem B ⥤ ℕᵒᵖ ⥤
    SheafOfModules.{w} (derivedChangeRingIndependentCoefficients J A)
  level : ∀ (M : StrictRingSystem B) (n : ℕ),
    (functor.obj M).obj (op n) =
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
        (α.app (op n)))).obj (M.level n)
  map : ∀ {M N : StrictRingSystem B} (f : M ⟶ N) (n : ℕ),
    eqToHom (level M n).symm ≫ (functor.map f).app (op n) ≫ eqToHom (level N n) =
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
        (α.app (op n)))).map (f.app n)
  transition : ∀ (M : StrictRingSystem B) {m n : ℕ} (h : m ≤ n)
    (V : Cᵒᵖ) (x : (M.level n).val.obj V),
    (eqToHom (level M m)).val.app V
      (((functor.obj M).map (homOfLE h).op).val.app V
        ((eqToHom (level M n).symm).val.app V x)) =
      (M.transition h).val.app V x
  additive : functor.Additive
  limits : PreservesFiniteLimits functor
  colimits : PreservesFiniteColimits functor

attribute [instance] ArithmeticSystemScalarForgetting.additive
  ArithmeticSystemScalarForgetting.limits ArithmeticSystemScalarForgetting.colimits

/-- The floor extension and its specified adjunction, including all component formulas.
Equality of presentations at selected levels expresses `UJ = id`; the counit is the
identity under that equality. The localized adjunction below is the specified exact
adjunction, not a separately chosen derived adjunction.
Source: arithmetic restriction in the normalization paragraph; Bhatt--Scholze,
Lemma 3.5.7 (blueprint: lem-sp-arithmetic-system-right-adjoint). -/
structure ArithmeticSystemFloorData (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (e : ℕ) (r : ℕ ↪o ℕ)
    (hf : ∀ k : ℕ, e ≤ k + 1 → r ((k + 1) / e - 1) ≤ k)
    (R : StrictRingSystem (selectedSystemRings B r) ⥤ StrictRingSystem B)
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R] where
  adjunction : systemSubsequence B r ⊣ R
  level : ∀ (N : StrictRingSystem (selectedSystemRings B r)) (k : ℕ) (h : e ≤ k + 1),
    (R.obj N).level k = (systemRestriction B (hf k h)).obj (N.level ((k + 1) / e - 1))
  prefix_zero : ∀ (N : StrictRingSystem (selectedSystemRings B r)) (k : ℕ),
    k + 1 < e → IsZero ((R.obj N).level k)
  selected : ∀ (N : StrictRingSystem (selectedSystemRings B r)) (n : ℕ),
    (R.obj N).level (r n) = N.level n
  transition : ∀ (N : StrictRingSystem (selectedSystemRings B r))
    {m n : ℕ} (h : m ≤ n) (hm : e ≤ m + 1) (hn : e ≤ n + 1)
    (V : Cᵒᵖ) (x : ((R.obj N).level n).val.obj V),
    (eqToHom (level N m hm)).val.app V (((R.obj N).transition h).val.app V x) =
      (N.transition (Nat.sub_le_sub_right
        (Nat.div_le_div_right (Nat.add_le_add_right h 1)) 1)).val.app V
          ((eqToHom (level N n hn)).val.app V x)
  map : ∀ {N P : StrictRingSystem (selectedSystemRings B r)} (f : N ⟶ P)
    (k : ℕ) (h : e ≤ k + 1),
    (R.map f).app k ≫ eqToHom (level P k h) = eqToHom (level N k h) ≫
      (systemRestriction B (hf k h)).map (f.app ((k + 1) / e - 1))
  counit : ∀ (N : StrictRingSystem (selectedSystemRings B r)) (n : ℕ),
    (adjunction.counit.app N).app n = eqToHom (selected N n)
  hom_selection : ∀ (D : StrictRingSystem B)
    (N : StrictRingSystem (selectedSystemRings B r)) (f : D ⟶ R.obj N) (n : ℕ),
    ((adjunction.homEquiv D N).symm f).app n = f.app (r n) ≫ eqToHom (selected N n)
  hom_extension : ∀ (D : StrictRingSystem B)
    (N : StrictRingSystem (selectedSystemRings B r))
    (g : (systemSubsequence B r).obj D ⟶ N) (k : ℕ) (h : e ≤ k + 1),
    (adjunction.homEquiv D N g).app k ≫ eqToHom (level N k h) =
      D.transition (hf k h) ≫ (systemRestriction B (hf k h)).map
        (g.app ((k + 1) / e - 1))
  hom_prefix : ∀ (D : StrictRingSystem B)
    (N : StrictRingSystem (selectedSystemRings B r))
    (g : (systemSubsequence B r).obj D ⟶ N) (k : ℕ),
    k + 1 < e → (adjunction.homEquiv D N g).app k = 0
  unit_selected : ∀ (D : StrictRingSystem B) (n : ℕ),
    (adjunction.unit.app D).app (r n) ≫
      eqToHom (selected ((systemSubsequence B r).obj D) n) = 𝟙 (D.level (r n))
  quasiIso_restriction : ∀ {K L : CochainComplex (StrictRingSystem B) ℤ} (f : K ⟶ L),
    QuasiIso f → QuasiIso (((systemSubsequence B r).mapHomologicalComplex (.up ℤ)).map f)
  quasiIso_extension : ∀ {K L :
    CochainComplex (StrictRingSystem (selectedSystemRings B r)) ℤ} (f : K ⟶ L),
    QuasiIso f → QuasiIso ((R.mapHomologicalComplex (.up ℤ)).map f)
  derived_unit : ∀ (K : CochainComplex (StrictRingSystem B) ℤ),
    adjunction.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map ((systemSubsequence B r).mapDerivedCategoryFactors.hom.app K) ≫
      R.mapDerivedCategoryFactors.hom.app
        (((systemSubsequence B r).mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((adjunction.mapHomologicalComplex (.up ℤ)).unit.app K)
  derived_counit : ∀ (K :
    CochainComplex (StrictRingSystem (selectedSystemRings B r)) ℤ),
    (systemSubsequence B r).mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      (systemSubsequence B r).mapDerivedCategoryFactors.hom.app
        ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((adjunction.mapHomologicalComplex (.up ℤ)).counit.app K) =
      adjunction.mapExactDerivedCategory.counit.app (DerivedCategory.Q.obj K)

/-- The common-coefficient limit comparison, normalized by ordinary limit restriction.
The normalization is an equality of maps from the localized ordinary limit, so it
specifies all selected projections on K-injective representatives and hence the
canonical derived projections. No exactness of countable products is required.
Source: Stacks Tags 0940, 0941 and 0H9K; arithmetic restriction in the integral
adjunction (blueprint: lem-sp-arithmetic-system-right-adjoint). -/
structure ArithmeticSystemLimitData
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (e : ℕ) (r : ℕ ↪o ℕ)
    (R : StrictRingSystem (selectedSystemRings B r) ⥤ StrictRingSystem B)
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    (β : (Functor.const ℕᵒᵖ).obj A ⟶ selectedSystemRings B r)
    (F : ArithmeticSystemScalarForgetting B A α)
    (G : ArithmeticSystemScalarForgetting (selectedSystemRings B r) A β)
    [HasDerivedCategory.{z} (SheafOfModules.{w}
      (derivedChangeRingIndependentCoefficients J A))]
    [HasDerivedCategory.{z} (ℕᵒᵖ ⥤ SheafOfModules.{w}
      (derivedChangeRingIndependentCoefficients J A))]
    (RF : DerivedCategory.{z} (ℕᵒᵖ ⥤ SheafOfModules.{w}
      (derivedChangeRingIndependentCoefficients J A)) ⥤
      DerivedCategory.{z} (SheafOfModules.{w}
        (derivedChangeRingIndependentCoefficients J A)))
    (η : (CategoryTheory.StrictTowerArithmetic.limitComplex _ ⋙ DerivedCategory.Q) ⟶
      DerivedCategory.Q ⋙ RF) where
  selection : R ⋙ F.functor ⋙ CategoryTheory.StrictTowerArithmetic.restriction _ e ≅ G.functor
  selection_sections : ∀ (N : StrictRingSystem (selectedSystemRings B r)) (n : ℕ)
    (V : Cᵒᵖ) (x : ((R.obj N).level (e * (n + 1) - 1)).val.obj V),
    HEq ((eqToHom (G.level N n)).val.app V
      (((selection.hom.app N).app (op n)).val.app V
        ((eqToHom (F.level (R.obj N) (e * (n + 1) - 1)).symm).val.app V x))) x
  comparison : (R ⋙ F.functor).mapDerivedCategory ⋙ RF ≅ G.functor.mapDerivedCategory ⋙ RF
  normalization : ∀ (K :
      CochainComplex (StrictRingSystem (selectedSystemRings B r)) ℤ),
    η.app (((R ⋙ F.functor).mapHomologicalComplex (.up ℤ)).obj K) ≫
      RF.map ((R ⋙ F.functor).mapDerivedCategoryFactors.inv.app K) ≫
      comparison.hom.app (DerivedCategory.Q.obj K) ≫
      RF.map (G.functor.mapDerivedCategoryFactors.hom.app K) =
    DerivedCategory.Q.map
      (CategoryTheory.StrictTowerArithmetic.limitMap e
          (((R ⋙ F.functor).mapHomologicalComplex (.up ℤ)).obj K) ≫
        (CategoryTheory.StrictTowerArithmetic.limitComplex _).map
          ((NatTrans.mapHomologicalComplex selection.hom (.up ℤ)).app K)) ≫
      η.app ((G.functor.mapHomologicalComplex (.up ℤ)).obj K)
```

## New

In `lean/Sheaf/CategoryTheory/ArithmeticSystemRightAdjointData.lean`, publicly
reexported by the original module:

```lean
structure ArithmeticSystemScalarForgetting
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B) where
  functor : StrictRingSystem B ⥤ ℕᵒᵖ ⥤
    SheafOfModules.{w} (derivedChangeRingIndependentCoefficients J A)
  level : ∀ (M : StrictRingSystem B) (n : ℕ),
    (functor.obj M).obj (op n) =
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
        (α.app (op n)))).obj (M.level n)
  map : ∀ {M N : StrictRingSystem B} (f : M ⟶ N) (n : ℕ),
    eqToHom (level M n).symm ≫ (functor.map f).app (op n) ≫ eqToHom (level N n) =
      (restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map
        (α.app (op n)))).map (f.app n)
  transition : ∀ (M : StrictRingSystem B) {m n : ℕ} (h : m ≤ n)
    (V : Cᵒᵖ) (x : (M.level n).val.obj V),
    (eqToHom (level M m)).val.app V
      (((functor.obj M).map (homOfLE h).op).val.app V
        ((eqToHom (level M n).symm).val.app V x)) =
      (M.transition h).val.app V x
  additive : functor.Additive
  limits : PreservesFiniteLimits functor
  colimits : PreservesFiniteColimits functor

attribute [instance] ArithmeticSystemScalarForgetting.additive
  ArithmeticSystemScalarForgetting.limits ArithmeticSystemScalarForgetting.colimits

/-- The floor extension and its specified adjunction, including all component formulas.
Equality of presentations at selected levels expresses `UJ = id`; the counit is the
identity under that equality. The localized adjunction below is the specified exact
adjunction, not a separately chosen derived adjunction.
Source: arithmetic restriction in the normalization paragraph; Bhatt--Scholze,
Lemma 3.5.7 (blueprint: lem-sp-arithmetic-system-right-adjoint). -/
structure ArithmeticSystemFloorData (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (e : ℕ) (r : ℕ ↪o ℕ)
    (hf : ∀ k : ℕ, e ≤ k + 1 → r ((k + 1) / e - 1) ≤ k)
    (R : StrictRingSystem (selectedSystemRings B r) ⥤ StrictRingSystem B)
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R] where
  adjunction : systemSubsequence B r ⊣ R
  level : ∀ (N : StrictRingSystem (selectedSystemRings B r)) (k : ℕ) (h : e ≤ k + 1),
    (R.obj N).level k = (systemRestriction B (hf k h)).obj (N.level ((k + 1) / e - 1))
  prefix_zero : ∀ (N : StrictRingSystem (selectedSystemRings B r)) (k : ℕ),
    k + 1 < e → IsZero ((R.obj N).level k)
  selected : ∀ (N : StrictRingSystem (selectedSystemRings B r)) (n : ℕ),
    (R.obj N).level (r n) = N.level n
  transition : ∀ (N : StrictRingSystem (selectedSystemRings B r))
    {m n : ℕ} (h : m ≤ n) (hm : e ≤ m + 1) (hn : e ≤ n + 1)
    (V : Cᵒᵖ) (x : ((R.obj N).level n).val.obj V),
    (eqToHom (level N m hm)).val.app V (((R.obj N).transition h).val.app V x) =
      (N.transition (Nat.sub_le_sub_right
        (Nat.div_le_div_right (Nat.add_le_add_right h 1)) 1)).val.app V
          ((eqToHom (level N n hn)).val.app V x)
  map : ∀ {N P : StrictRingSystem (selectedSystemRings B r)} (f : N ⟶ P)
    (k : ℕ) (h : e ≤ k + 1),
    (R.map f).app k ≫ eqToHom (level P k h) = eqToHom (level N k h) ≫
      (systemRestriction B (hf k h)).map (f.app ((k + 1) / e - 1))
  counit : ∀ (N : StrictRingSystem (selectedSystemRings B r)) (n : ℕ),
    (adjunction.counit.app N).app n = eqToHom (selected N n)
  hom_selection : ∀ (D : StrictRingSystem B)
    (N : StrictRingSystem (selectedSystemRings B r)) (f : D ⟶ R.obj N) (n : ℕ),
    ((adjunction.homEquiv D N).symm f).app n = f.app (r n) ≫ eqToHom (selected N n)
  hom_extension : ∀ (D : StrictRingSystem B)
    (N : StrictRingSystem (selectedSystemRings B r))
    (g : (systemSubsequence B r).obj D ⟶ N) (k : ℕ) (h : e ≤ k + 1),
    (adjunction.homEquiv D N g).app k ≫ eqToHom (level N k h) =
      D.transition (hf k h) ≫ (systemRestriction B (hf k h)).map
        (g.app ((k + 1) / e - 1))
  hom_prefix : ∀ (D : StrictRingSystem B)
    (N : StrictRingSystem (selectedSystemRings B r))
    (g : (systemSubsequence B r).obj D ⟶ N) (k : ℕ),
    k + 1 < e → (adjunction.homEquiv D N g).app k = 0
  unit_selected : ∀ (D : StrictRingSystem B) (n : ℕ),
    (adjunction.unit.app D).app (r n) ≫
      eqToHom (selected ((systemSubsequence B r).obj D) n) = 𝟙 (D.level (r n))
  quasiIso_restriction : ∀ {K L : CochainComplex (StrictRingSystem B) ℤ} (f : K ⟶ L),
    QuasiIso f → QuasiIso (((systemSubsequence B r).mapHomologicalComplex (.up ℤ)).map f)
  quasiIso_extension : ∀ {K L :
    CochainComplex (StrictRingSystem (selectedSystemRings B r)) ℤ} (f : K ⟶ L),
    QuasiIso f → QuasiIso ((R.mapHomologicalComplex (.up ℤ)).map f)
  derived_unit : ∀ (K : CochainComplex (StrictRingSystem B) ℤ),
    adjunction.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
      R.mapDerivedCategory.map ((systemSubsequence B r).mapDerivedCategoryFactors.hom.app K) ≫
      R.mapDerivedCategoryFactors.hom.app
        (((systemSubsequence B r).mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((adjunction.mapHomologicalComplex (.up ℤ)).unit.app K)
  derived_counit : ∀ (K :
    CochainComplex (StrictRingSystem (selectedSystemRings B r)) ℤ),
    (systemSubsequence B r).mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      (systemSubsequence B r).mapDerivedCategoryFactors.hom.app
        ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((adjunction.mapHomologicalComplex (.up ℤ)).counit.app K) =
      adjunction.mapExactDerivedCategory.counit.app (DerivedCategory.Q.obj K)

/-- The common-coefficient limit comparison, normalized by ordinary limit restriction.
The normalization is an equality of maps from the localized ordinary limit, so it
specifies all selected projections on K-injective representatives and hence the
canonical derived projections. No exactness of countable products is required.
Source: Stacks Tags 0940, 0941 and 0H9K; arithmetic restriction in the integral
adjunction (blueprint: lem-sp-arithmetic-system-right-adjoint). -/
structure ArithmeticSystemLimitData
    (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (e : ℕ) (r : ℕ ↪o ℕ)
    (R : StrictRingSystem (selectedSystemRings B r) ⥤ StrictRingSystem B)
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (A : Sheaf J CommRingCat.{w})
    (α : (Functor.const ℕᵒᵖ).obj A ⟶ B)
    (β : (Functor.const ℕᵒᵖ).obj A ⟶ selectedSystemRings B r)
    (F : ArithmeticSystemScalarForgetting B A α)
    (G : ArithmeticSystemScalarForgetting (selectedSystemRings B r) A β)
    [HasDerivedCategory.{z} (SheafOfModules.{w}
      (derivedChangeRingIndependentCoefficients J A))]
    [HasDerivedCategory.{z} (ℕᵒᵖ ⥤ SheafOfModules.{w}
      (derivedChangeRingIndependentCoefficients J A))]
    (RF : DerivedCategory.{z} (ℕᵒᵖ ⥤ SheafOfModules.{w}
      (derivedChangeRingIndependentCoefficients J A)) ⥤
      DerivedCategory.{z} (SheafOfModules.{w}
        (derivedChangeRingIndependentCoefficients J A)))
    (η : (CategoryTheory.StrictTowerArithmetic.limitComplex _ ⋙ DerivedCategory.Q) ⟶
      DerivedCategory.Q ⋙ RF) where
  selection : R ⋙ F.functor ⋙ CategoryTheory.StrictTowerArithmetic.restriction _ e ≅ G.functor
  selection_sections : ∀ (N : StrictRingSystem (selectedSystemRings B r)) (n : ℕ)
    (V : Cᵒᵖ) (x : ((R.obj N).level (e * (n + 1) - 1)).val.obj V),
    HEq ((eqToHom (G.level N n)).val.app V
      (((selection.hom.app N).app (op n)).val.app V
        ((eqToHom (F.level (R.obj N) (e * (n + 1) - 1)).symm).val.app V x))) x
  comparison : (R ⋙ F.functor).mapDerivedCategory ⋙ RF ≅ G.functor.mapDerivedCategory ⋙ RF
  normalization : ∀ (K :
      CochainComplex (StrictRingSystem (selectedSystemRings B r)) ℤ),
    η.app (((R ⋙ F.functor).mapHomologicalComplex (.up ℤ)).obj K) ≫
      RF.map ((R ⋙ F.functor).mapDerivedCategoryFactors.inv.app K) ≫
      comparison.hom.app (DerivedCategory.Q.obj K) ≫
      RF.map (G.functor.mapDerivedCategoryFactors.hom.app K) =
    DerivedCategory.Q.map
      (CategoryTheory.StrictTowerArithmetic.limitMap e
          (((R ⋙ F.functor).mapHomologicalComplex (.up ℤ)).obj K) ≫
        (CategoryTheory.StrictTowerArithmetic.limitComplex _).map
          ((NatTrans.mapHomologicalComplex selection.hom (.up ℤ)).app K)) ≫
      η.app ((G.functor.mapHomologicalComplex (.up ℤ)).obj K)

/-- The ordinary part of the arithmetic floor-extension construction. It records the
specified Hom bijection, selected-level identities, and all strict component formulas.
The four localization conclusions of `ArithmeticSystemFloorData` are deliberately absent:
they follow from exact-functor localization, without any further construction.
Source: arithmetic restriction in the normalization paragraph of the integral adjunction;
Bhatt--Scholze, Lemma 3.5.7 (blueprint: def-sp-arithmetic-system-adjunction-data). -/
structure ArithmeticSystemOrdinaryFloorData (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})
    (e : ℕ) (r : ℕ ↪o ℕ)
    (hf : ∀ k : ℕ, e ≤ k + 1 → r ((k + 1) / e - 1) ≤ k)
    (R : StrictRingSystem (selectedSystemRings B r) ⥤ StrictRingSystem B)
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R] where
  adjunction : systemSubsequence B r ⊣ R
  level : ∀ (N : StrictRingSystem (selectedSystemRings B r)) (k : ℕ) (h : e ≤ k + 1),
    (R.obj N).level k = (systemRestriction B (hf k h)).obj (N.level ((k + 1) / e - 1))
  prefix_zero : ∀ (N : StrictRingSystem (selectedSystemRings B r)) (k : ℕ),
    k + 1 < e → IsZero ((R.obj N).level k)
  selected : ∀ (N : StrictRingSystem (selectedSystemRings B r)) (n : ℕ),
    (R.obj N).level (r n) = N.level n
  transition : ∀ (N : StrictRingSystem (selectedSystemRings B r))
    {m n : ℕ} (h : m ≤ n) (hm : e ≤ m + 1) (hn : e ≤ n + 1)
    (V : Cᵒᵖ) (x : ((R.obj N).level n).val.obj V),
    (eqToHom (level N m hm)).val.app V (((R.obj N).transition h).val.app V x) =
      (N.transition (Nat.sub_le_sub_right
        (Nat.div_le_div_right (Nat.add_le_add_right h 1)) 1)).val.app V
          ((eqToHom (level N n hn)).val.app V x)
  map : ∀ {N P : StrictRingSystem (selectedSystemRings B r)} (f : N ⟶ P)
    (k : ℕ) (h : e ≤ k + 1),
    (R.map f).app k ≫ eqToHom (level P k h) = eqToHom (level N k h) ≫
      (systemRestriction B (hf k h)).map (f.app ((k + 1) / e - 1))
  counit : ∀ (N : StrictRingSystem (selectedSystemRings B r)) (n : ℕ),
    (adjunction.counit.app N).app n = eqToHom (selected N n)
  hom_selection : ∀ (D : StrictRingSystem B)
    (N : StrictRingSystem (selectedSystemRings B r)) (f : D ⟶ R.obj N) (n : ℕ),
    ((adjunction.homEquiv D N).symm f).app n = f.app (r n) ≫ eqToHom (selected N n)
  hom_extension : ∀ (D : StrictRingSystem B)
    (N : StrictRingSystem (selectedSystemRings B r))
    (g : (systemSubsequence B r).obj D ⟶ N) (k : ℕ) (h : e ≤ k + 1),
    (adjunction.homEquiv D N g).app k ≫ eqToHom (level N k h) =
      D.transition (hf k h) ≫ (systemRestriction B (hf k h)).map
        (g.app ((k + 1) / e - 1))
  hom_prefix : ∀ (D : StrictRingSystem B)
    (N : StrictRingSystem (selectedSystemRings B r))
    (g : (systemSubsequence B r).obj D ⟶ N) (k : ℕ),
    k + 1 < e → (adjunction.homEquiv D N g).app k = 0
  unit_selected : ∀ (D : StrictRingSystem B) (n : ℕ),
    (adjunction.unit.app D).app (r n) ≫
      eqToHom (selected ((systemSubsequence B r).obj D) n) = 𝟙 (D.level (r n))
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.ArithmeticSystemRightAdjoint --uses NAME`
was checked for all three original structure names. There are zero downstream
modules and no external textual users; the only original uses are in this item.
The newly introduced modules are part of this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ArithmeticSystemRightAdjoint | B6 | Publicly reexports unchanged records and assembles the proof from two strictly smaller steps. |
| Sheaf.CategoryTheory.ArithmeticSystemRightAdjointData | new, B6 | Owns the unchanged original records and the new ordinary-data record. |
| Sheaf.CategoryTheory.ArithmeticSystemFloorExtension | new, B6 | States the ordinary exact construction, using the data module. |
| Sheaf.CategoryTheory.ArithmeticSystemFloorLimitComparison | new, B6 | States the limit comparison for an already specified ordinary floor extension. |

## Status

landed 20261025T094857-L-3269256 2026-10-25 (merge of deliver/B6/Sheaf.CategoryTheory.ArithmeticSystemRightAdjoint)
