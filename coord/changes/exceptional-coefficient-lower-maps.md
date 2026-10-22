# ExceptionalCoefficients normalized coefficient maps

## Reason

The tensor and Cartesian comparison proof needs `EtaleCompactScalarCoherence`, which
publicly imported `ExceptionalCoefficientComparison` for its normalized maps.
Extracting those same maps to `ExceptionalCoefficientMaps` removes this import cycle.
All existing public declaration names and signatures are preserved. The lower
normalized maps keep their data verbatim; the tensor-domain composite is
reassociated as documented below.
No file under `lean/WeilConjectures` changes. No target changes meaning.

## Old

The following namespace contents were in
`Sheaf.Paper.ExceptionalCoefficientComparison`, verbatim (including the proofs that
construct the unique normalized tensor and unit isomorphisms):

```lean
namespace ExceptionalCoefficients

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)

/-- Scalar extension and open extension by zero are left adjoint to canonically
identified right adjoints; uniqueness gives the identity/zero comparison.
Source: Stacks 0GL6 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def openIso {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        scalarExtension φ Z ≅
      scalarExtension φ X ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory :=
  (conjugateIsoEquiv
    (((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j).ofNatIsoRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm).comp
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)))
    ((Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).comp
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j).ofNatIsoRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).symm))).symm
    (scalarRestrictionPullbackIso φ j) |>.symm

/-- The canonical compact-support coefficient arrow, on a fixed compactification: the
recorded proper coefficient mate `scalarMate` at the open extension, followed by
proper direct image of the open comparison.
Source: Stacks 0GL6 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def compactSupportMap {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) :
    (scalarExtension φ Y).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ⟶
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((scalarExtension φ X).obj M) :=
  (scalarMate φ c.g).app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M) ≫
    (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor.map
      ((openIso φ c.i).hom.app M)

/-- Inverse of the canonical comparison on its isomorphism domain, extended by zero.
This extension only makes the term total; every theorem use is on the domain where
b is an isomorphism. Source: Stacks 0GL6
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def comparisonInverse {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).obj
        ((scalarExtension φ X).obj M) ⟶
      (scalarExtension φ Y).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) :=
  open Classical in
  if h : IsIso (compactSupportMap φ c M) then
    @inv _ _ _ _ (compactSupportMap φ c M) h
  else 0

/-- A total extension of the counit-transpose construction; its zero fallback is
irrelevant on the stated domain, where the theorem proves invertibility of b.
Source: blueprint compatibilities (2)
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def mateMap [Finite A] [Finite B] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (K : DerivedCategoryModule A Y) :
    (scalarExtension φ X).obj ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K) ⟶
      (rightDerivedUpperShriek (ModuleCat.{u + 1} B) f).obj ((scalarExtension φ Y).obj K) :=
  (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} B) f).homEquiv _ _
    (comparisonInverse φ (HasCompactification.compactification f)
      ((rightDerivedUpperShriek (ModuleCat.{u + 1} A) f).obj K) ≫
      (scalarExtension φ Y).map
        ((rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} A) f).counit.app K))

/-- The ordinary extension has its actual scalar-restriction adjunction.
Source: Stacks 06YY (blueprint: lem-pur-exceptional-coefficient-comparison). -/
instance ordinaryIsLeftAdjoint (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ T).IsLeftAdjoint :=
  (ProEtale.etaleSheafExtendScalarsAdjunction φ T).isLeftAdjoint

/-- The ordinary tensorator is the sheafified scalar balancing map.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
instance ordinaryOplax (T : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ T).OplaxMonoidal :=
  composeAndSheafifyOplaxMonoidal T.smallEtaleTopology
    (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)

/-- Representative normalization for a scalar tensor comparison, with monoidal data
kept shared in both categories. Source: Stacks 07A4
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def TensorNormalizationAux
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E ≅
      E.prod E ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory D))) : Prop :=
  ∀ P Q : CochainComplex C ℤ,
    δ.hom.app (_root_.DerivedCategory.Q.obj P, _root_.DerivedCategory.Q.obj Q) ≫
        (rep P ⊗ₘ rep Q) ≫ Functor.LaxMonoidal.μ _root_.DerivedCategory.Q
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) =
      E.map (Functor.LaxMonoidal.μ _root_.DerivedCategory.Q P Q) ≫ rep (P ⊗ Q) ≫
        _root_.DerivedCategory.Q.map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q)

/-- The all-complex normalization with site tensor functors kept as shared constants.
This is exactly `TensorNormalizationAux` on the small etale sheaf categories.
Keeping its monoidal arguments inside this generic body avoids repeated comparison
of the nested sheafification and derived-monoidal proofs in specialized theorem types.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def SiteTensorNormalizationAux
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (D : Type w) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    [Abelian.HasFunctorialFlatResolution D] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology C ⥤ Sheaf T.smallEtaleTopology D)
    [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (S : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology D))
    (r : ∀ P : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ,
      S.obj (_root_.DerivedCategory.Q.obj P) ⟶
        _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : Functor.uncurry.obj (derivedTensor C T) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (derivedTensor D T)) : Prop :=
  TensorNormalizationAux F S r δ

/-- Small-etale specialization of the shared all-complex tensor normalization.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
abbrev TensorNormalization (T : Scheme.{u}) :=
  SiteTensorNormalizationAux (ModuleCat.{u + 1} A) (ModuleCat.{u + 1} B) T
    (ProEtale.etaleSheafExtendScalars φ T)
    (scalarExtension φ T) (scalarExtensionRepresentative φ T)

private theorem mapComplex_unit_formula
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {E : C ⥤ D} {U : D ⥤ C} [E.Additive] [U.Additive] (adj : E ⊣ U)
    (P : CochainComplex C ℤ) :
    (adj.mapHomologicalComplex (.up ℤ)).unit.app P =
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
        (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P := by
  ext i
  simp only [Functor.id_obj, Functor.comp_obj, Adjunction.mapHomologicalComplex_unit_app_f,
    HomologicalComplex.comp_f, Functor.mapHomologicalComplexIdIso_inv_app_f,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp]
  exact (Category.comp_id _).symm

open AlgebraicGeometry AlgebraicGeometry.Etale
open MonoidalCategory Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ u₂
private def productLaxTensorator
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] :
    F.prod F ⋙ Functor.uncurry.obj (curriedTensor D) ⟶
      Functor.uncurry.obj (curriedTensor C) ⋙ F where
  app X := Functor.LaxMonoidal.μ F X.1 X.2
  naturality X Y f := by
    have h := Functor.LaxMonoidal.μ_natural F f.1 f.2
    rw [MonoidalCategory.tensorHom_def (F.map f.1) (F.map f.2),
      MonoidalCategory.tensorHom_def f.1 f.2] at h
    simpa only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
      Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map] using h

private def productOplaxTensorator
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (F : C ⥤ D)
    (τ : (Functor.postcompose₂.obj F).obj T ⟶
      (((Functor.whiskeringLeft₂ D).obj F).obj F).obj U) :
    Functor.uncurry.obj T ⋙ F ⟶ F.prod F ⋙ Functor.uncurry.obj U where
  app X := (τ.app X.1).app X.2
  naturality X Y f := by
    change F.map ((T.map f.1).app X.2 ≫ (T.obj Y.1).map f.2) ≫ _ =
      _ ≫ ((U.map (F.map f.1)).app (F.obj X.2) ≫ (U.obj (F.obj Y.1)).map (F.map f.2))
    rw [F.map_comp, Category.assoc]
    have h₁ := congr_app (τ.naturality f.1) X.2
    have h₂ := (τ.app Y.1).naturality f.2
    change F.map ((T.map f.1).app X.2) ≫ (τ.app Y.1).app X.2 =
      (τ.app X.1).app X.2 ≫ (U.map (F.map f.1)).app (F.obj X.2) at h₁
    change F.map ((T.obj Y.1).map f.2) ≫ (τ.app Y.1).app Y.2 =
      (τ.app Y.1).app X.2 ≫ (U.obj (F.obj Y.1)).map (F.map f.2) at h₂
    rw [h₂, ← Category.assoc, h₁, Category.assoc]

private def productIsoOfFamily
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (F : C ⥤ D)
    (μ : ∀ K L : C, (U.obj (F.obj K)).obj (F.obj L) ≅ F.obj ((T.obj K).obj L))
    (h₁ : ∀ {K K'} (f : K ⟶ K') L,
      (U.map (F.map f)).app (F.obj L) ≫ (μ K' L).hom =
        (μ K L).hom ≫ F.map ((T.map f).app L))
    (h₂ : ∀ K {L L'} (f : L ⟶ L'),
      (U.obj (F.obj K)).map (F.map f) ≫ (μ K L').hom =
        (μ K L).hom ≫ F.map ((T.obj K).map f)) :
    Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj U :=
  (NatIso.ofComponents (fun X ↦ μ X.1 X.2) (by
    intro X Y f
    change ((U.map (F.map f.1)).app (F.obj X.2) ≫
      (U.obj (F.obj Y.1)).map (F.map f.2)) ≫ (μ Y.1 Y.2).hom =
      (μ X.1 X.2).hom ≫ F.map ((T.map f.1).app X.2 ≫ (T.obj Y.1).map f.2)
    rw [Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc, ← F.map_comp])).symm

private theorem productIso_natural₁
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (F : C ⥤ D)
    (δ : Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj U)
    {K K' : C} (f : K ⟶ K') (L : C) :
    (U.map (F.map f)).app (F.obj L) ≫ (δ.app (K', L)).inv =
      (δ.app (K, L)).inv ≫ F.map ((T.map f).app L) := by
  have h := δ.inv.naturality (show (K, L) ⟶ (K', L) from (f, 𝟙 L))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map] at h
  simpa only [_root_.CategoryTheory.Functor.map_id, Functor.comp_obj, Functor.uncurry_obj_obj,
    Functor.prod_obj, Iso.app_inv, Category.comp_id] using h

private theorem productIso_natural₂
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D) (F : C ⥤ D)
    (δ : Functor.uncurry.obj T ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj U)
    (K : C) {L L' : C} (f : L ⟶ L') :
    (U.obj (F.obj K)).map (F.map f) ≫ (δ.app (K, L')).inv =
      (δ.app (K, L)).inv ≫ F.map ((T.obj K).map f) := by
  have h := δ.inv.naturality (show (K, L) ⟶ (K, L') from (𝟙 K, f))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map] at h
  simpa only [_root_.CategoryTheory.Functor.map_id, Functor.comp_obj, Functor.uncurry_obj_obj,
    Functor.prod_obj, Iso.app_inv, NatTrans.id_app, Category.id_comp] using h

private theorem tensor_normalization_all_of_flat
    {C : Type u₁} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type u₂} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (r : _root_.DerivedCategory.Q ⋙ E ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q)
    (δ : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E ≅
      E.prod E ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory D)))
    (hflat : Functor.rightExactTensorModelNormalization F E r.app
      (fun K L ↦ (δ.app (K, L)).symm)) :
    AlgebraicGeometry.Etale.ExceptionalCoefficients.TensorNormalizationAux F E r.app δ := by
  let QC := _root_.DerivedCategory.Q (C := C)
  let QD := _root_.DerivedCategory.Q (C := D)
  let FC := F.mapHomologicalComplex (.up ℤ)
  let α : QC.prod QC ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E ⟶
      FC.prod FC ⋙ Functor.uncurry.obj (curriedTensor (CochainComplex D ℤ)) ⋙ QD :=
    Functor.whiskerLeft (QC.prod QC) δ.hom ≫
      Functor.whiskerRight (r.prod r)
        (Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory D))) ≫
      Functor.whiskerLeft (FC.prod FC)
        (productLaxTensorator QD)
  let β : QC.prod QC ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E ⟶
      FC.prod FC ⋙ Functor.uncurry.obj (curriedTensor (CochainComplex D ℤ)) ⋙ QD :=
    Functor.whiskerRight (productLaxTensorator QC) E ≫
      Functor.whiskerLeft (Functor.uncurry.obj (curriedTensor (CochainComplex C ℤ))) r ≫
      Functor.whiskerRight
        (productOplaxTensorator (curriedTensor (CochainComplex C ℤ))
          (curriedTensor (CochainComplex D ℤ)) FC
          (Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F)) QD
  intro P Q
  have hab : α.app (P, Q) = β.app (P, Q) := by
    obtain ⟨P', π, hπ, hPflat, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat P
    obtain ⟨Q', ρ, hρ, hQflat, hQ⟩ := CochainComplex.exists_quasiIso_flat_kFlat Q
    have : IsIso (QC.map π) := by
      exact Localization.inverts QC (HomologicalComplex.quasiIso C (.up ℤ)) π hπ
    have : IsIso (QC.map ρ) := by
      exact Localization.inverts QC (HomologicalComplex.quasiIso C (.up ℤ)) ρ hρ
    have hi : IsIso
        ((QC.prod QC ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E).map
          (show (P', Q') ⟶ (P, Q) from (π, ρ))) := by
      dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj, Functor.uncurry_obj_map,
        curriedTensor_map_app, curriedTensor_obj_map]
      rw [← MonoidalCategory.tensorHom_def (QC.map π) (QC.map ρ)]
      infer_instance
    apply (cancel_epi
      ((QC.prod QC ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ E).map
        (show (P', Q') ⟶ (P, Q) from (π, ρ)))).1
    rw [α.naturality, β.naturality]
    have h : α.app (P', Q') = β.app (P', Q') := by
      simpa only [α, β, QC, QD, FC, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.prod_obj, Functor.uncurry_obj_obj,
        Functor.uncurry_obj_map, NatTrans.prod_app_fst, NatTrans.prod_app_snd, Functor.comp_obj,
        productLaxTensorator,
        productOplaxTensorator, curriedTensor_map_app, curriedTensor_obj_map,
        MonoidalCategory.tensorHom_def, curriedTensor_obj_obj,
        Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, Iso.symm_inv, Iso.app_hom,
        Category.assoc] using (hflat P' Q' hP hQ hPflat hQflat).symm
    rw [h]
  simpa only [α, β, QC, QD, FC, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.prod_obj, Functor.uncurry_obj_obj,
    Functor.uncurry_obj_map, NatTrans.prod_app_fst, NatTrans.prod_app_snd, Functor.comp_obj,
        productLaxTensorator,
    productOplaxTensorator, curriedTensor_map_app, curriedTensor_obj_map,
    MonoidalCategory.tensorHom_def, curriedTensor_obj_obj,
        Functor.whiskeringLeft₂_obj_obj_obj_obj_obj, Iso.symm_inv, Iso.app_hom,
    Category.assoc] using hab


private theorem tensor_normalization_all_onSite
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (D : Type w) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    [Abelian.HasFunctorialFlatResolution D] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology C ⥤ Sheaf T.smallEtaleTopology D)
    [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (S : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology D))
    (r : _root_.DerivedCategory.Q ⋙ S ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q)
    (δ : Functor.uncurry.obj (derivedTensor C T) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (derivedTensor D T))
    (hflat : AlgebraicGeometry.Etale.EtaleHomTensorModelNormalization C D T F S r.app
      (fun K L ↦ (δ.app (K, L)).symm)) :
    AlgebraicGeometry.Etale.ExceptionalCoefficients.SiteTensorNormalizationAux C D T F S
      r.app δ := by
  exact tensor_normalization_all_of_flat F S r δ hflat


private theorem site_normalization_flat
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    (D : Type w) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [SymmetricCategory D]
    [Abelian.HasFunctorialFlatResolution D] (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology C ⥤ Sheaf T.smallEtaleTopology D)
    [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (S : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C) ⥤
      _root_.DerivedCategory (Sheaf T.smallEtaleTopology D))
    (r : ∀ P : CochainComplex (Sheaf T.smallEtaleTopology C) ℤ,
      S.obj (_root_.DerivedCategory.Q.obj P) ⟶
        _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (δ : Functor.uncurry.obj (derivedTensor C T) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (derivedTensor D T))
    (hn : AlgebraicGeometry.Etale.ExceptionalCoefficients.SiteTensorNormalizationAux
      C D T F S r δ) :
    EtaleHomTensorModelNormalization C D T F S r
      (fun K L ↦ (δ.app (K, L)).symm) := by
  intro P Q _ _ _ _
  exact (hn P Q).symm

private def adjointRepresentative
    {C D V W : Type*} [Category C] [Category D] [Category V] [Category W]
    (QC : C ⥤ V) (QD : D ⥤ W) (FC : C ⥤ D) (UC : D ⥤ C)
    (E : V ⥤ W) (U : W ⥤ V) (adj : E ⊣ U)
    (a : FC ⊣ UC) (fac : UC ⋙ QC ≅ QD ⋙ U) : QC ⋙ E ⟶ FC ⋙ QD := by
  let t : QC ⟶ FC ⋙ QD ⋙ U :=
    Functor.whiskerRight a.unit QC ≫ Functor.whiskerLeft FC fac.hom
  exact {
    app P := (adj.homEquiv _ _).symm (t.app P)
    naturality P Q f := by
      change E.map (QC.map f) ≫ _ = _ ≫ QD.map (FC.map f)
      calc
        _ = (adj.homEquiv _ _).symm (QC.map f ≫ t.app Q) :=
          (adj.homEquiv_naturality_left_symm (QC.map f) (t.app Q)).symm
        _ = (adj.homEquiv _ _).symm (t.app P ≫ U.map (QD.map (FC.map f))) :=
          congrArg (adj.homEquiv _ _).symm (t.naturality f)
        _ = _ := adj.homEquiv_naturality_right_symm _ _ }


/-- The canonical scalar tensor isomorphism is determined by ordinary balancing.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison).
Proof: on flat-term K-flat pairs the counits and the localization tensorators
are invertible. Ordinary balancing therefore defines δ by the displayed equation.
It commutes with resolutions and differentials. Localize in both variables to obtain
a natural isomorphism. Every pair admits such resolutions, proving uniqueness;
naturality with respect to a resolution proves the equation for all complexes. -/
theorem tensorIso_existsUnique (T : Scheme.{u}) :
    ∃! δ, TensorNormalization φ T δ := by
  let E := ProEtale.etaleSheafExtendScalars φ T
  let U := Sheaf.restrictScalars T.smallEtaleTopology φ
  let ad : scalarExtension φ T ⊣ U.mapDerivedCategory := Adjunction.ofIsRightAdjoint _
  let r := adjointRepresentative _root_.DerivedCategory.Q
    _root_.DerivedCategory.Q (E.mapHomologicalComplex (.up ℤ))
    (U.mapHomologicalComplex (.up ℤ)) (scalarExtension φ T) U.mapDerivedCategory ad
    ((ProEtale.etaleSheafExtendScalarsAdjunction φ T).mapHomologicalComplex (.up ℤ))
    U.mapDerivedCategoryFactors.symm
  have hr' : r.app = scalarExtensionRepresentative φ T := by
    funext P
    unfold scalarExtensionRepresentative
    rw [← mapComplex_unit_formula]
    rfl
  obtain ⟨μ, hμ, hμuniq⟩ := etaleHomTensorComparison_existsUnique T φ
  let δ := productIsoOfFamily
    (derivedTensor (ModuleCat.{u + 1} A) T) (derivedTensor (ModuleCat.{u + 1} B) T)
    (scalarExtension φ T) μ hμ.1 hμ.2.1
  have hflat : EtaleHomTensorModelNormalization (ModuleCat.{u + 1} A)
      (ModuleCat.{u + 1} B) T E (scalarExtension φ T) r.app
      (fun K L ↦ (δ.app (K, L)).symm) := by
    rw [hr']
    exact hμ.2.2
  have hδ : TensorNormalization φ T δ := by
    have h := tensor_normalization_all_onSite (ModuleCat.{u + 1} A)
      (ModuleCat.{u + 1} B) T E (scalarExtension φ T) r δ hflat
    rw [hr'] at h
    exact h
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  have hεcanonical : IsEtaleHomTensorCanonical T φ
      (fun K L ↦ (ε.app (K, L)).symm) := by
    refine ⟨productIso_natural₁ _ _ _ ε,
      productIso_natural₂ _ _ _ ε, ?_⟩
    exact site_normalization_flat (ModuleCat.{u + 1} A)
      (ModuleCat.{u + 1} B) T E (scalarExtension φ T)
      (scalarExtensionRepresentative φ T) ε hε
  have hεμ := hμuniq _ hεcanonical
  apply Iso.ext
  apply NatTrans.ext
  funext ⟨K, L⟩
  have h := congrFun (congrFun hεμ K) L
  exact congrArg Iso.inv h

/-- The same normalized tensor comparison, expressed using the site's tensor functor.
The heterogeneous equality asserts equality of the very same natural isomorphism,
including its endpoints, rather than choosing an unrelated comparison.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison).
Proof: unfold derivedTensor, which is curriedTensor of the canonical derived
monoidal structure. The normalized isomorphism from tensorIso_existsUnique
therefore has exactly this type. Reflexive heterogeneous equality supplies the
witness, and heterogeneous equality to that fixed witness implies uniqueness.
Keeping the transport opaque prevents expansion of the full monoidal structure. -/
theorem siteTensorIso_existsUnique (T : Scheme.{u}) :
    ∃! e : Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) T) ⋙
        scalarExtension φ T ≅
      (scalarExtension φ T).prod (scalarExtension φ T) ⋙
        Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} B) T),
      HEq e (tensorIso_existsUnique φ T).choose := by
  exact ⟨(tensorIso_existsUnique φ T).choose, HEq.rfl, fun _ h ↦ eq_of_heq h⟩

/-- The site's tensor comparison, uniquely equal to the representative-normalized one.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def tensorIso (T : Scheme.{u}) :
    Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) T) ⋙ scalarExtension φ T ≅
      (scalarExtension φ T).prod (scalarExtension φ T) ⋙
        Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} B) T) :=
  (siteTensorIso_existsUnique φ T).choose

/-- Unit normalization using shared monoidal data for the ordinary scalar functor.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def UnitNormalizationAux
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (e : E.obj (𝟙_ _) ≅ 𝟙_ _) : Prop :=
  E.map (Functor.LaxMonoidal.ε _root_.DerivedCategory.Q) ≫ rep (𝟙_ _) ≫
      _root_.DerivedCategory.Q.map (Functor.OplaxMonoidal.mapHomologicalComplexη (.up ℤ) F) =
    e.hom ≫ Functor.LaxMonoidal.ε _root_.DerivedCategory.Q

/-- Specialization of scalar-unit normalization to the ordinary small-etale site.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
abbrev UnitNormalization (T : Scheme.{u}) :=
  UnitNormalizationAux (ProEtale.etaleSheafExtendScalars φ T)
    (scalarExtension φ T) (scalarExtensionRepresentative φ T)

private theorem extension_preservesKFlatQuasiIso {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) (X : Scheme.{u}) :
    (ProEtale.etaleSheafExtendScalars φ X).PreservesKFlatQuasiIso := by
  classical
  let E : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R) ⥤ Sheaf X.smallEtaleTopology
    (ModuleCat.{u + 1} S) :=
    Sheaf.composeAndSheafify X.smallEtaleTopology (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  let U := Sheaf.restrictScalars X.smallEtaleTopology φ
  let adj : E ⊣ U :=
    Sheaf.adjunction X.smallEtaleTopology (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u +
      1} φ)
  have : E.Additive := adj.left_adjoint_additive
  let B := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of S S)
  let coeff := (Functor.const X.Etaleᵒᵖ).obj B
  let a := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)
  let a' := presheafToSheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)
  let F := sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)
  let W := (Functor.whiskeringRight X.Etaleᵒᵖ _ _).obj
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  have : X.smallEtaleTopology.PreservesSheafification (ModuleCat.restrictScalars.{u + 1, u + 1, u
    + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction X.smallEtaleTopology
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let e : E ⋙ U ≅ MonoidalCategory.tensorRight (a.obj coeff) :=
    Functor.associator F (W ⋙ a') U ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W a' U) ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft W
        (sheafComposeNatIso X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)
          (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} S))
          (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} R))).symm) ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W _ a).symm ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerRight
        (Functor.whiskeringRightObjCompIso _ _ ≪≫
          (Functor.whiskeringRight _ _ _).mapIso
            (ModuleCat.extendScalarsCompRestrictScalarsIso.{u + 1} φ) ≪≫
          whiskeringRightTensorRightIso _) a) ≪≫
      Functor.isoWhiskerLeft F (Sheaf.presheafToSheafCompTensorRightIso coeff).symm ≪≫
      (Functor.associator F a (MonoidalCategory.tensorRight (a.obj coeff))).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (sheafificationAdjunction X.smallEtaleTopology (ModuleCat.{u + 1} R)).counit)
        (MonoidalCategory.tensorRight (a.obj coeff)) ≪≫ Functor.leftUnitor _
  have hU : U.Faithful := inferInstance
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{0, 0} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have : HasCountableCoproducts (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
    ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩
  have hE : E.PreservesKFlatQuasiIso := by
    apply CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'
    intro K hK hKa
    have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa (a.obj coeff)
    have hEU := ht.of_iso
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app K).symm
    have hUK : ((U.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
      hEU.of_iso ((CategoryTheory.Functor.mapHomologicalComplexCompIso
        (Iso.refl (E ⋙ U)) (.up ℤ)).app K)
    intro n
    exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (hUK n)
  exact hE



private theorem unitNormalizationAux_existsUnique
    {C : Type v} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    {D : Type w} [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [F.OplaxMonoidal] [F.IsLeftAdjoint]
    [IsIso (Functor.OplaxMonoidal.η F)]
    (E : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (rep : ∀ P : CochainComplex C ℤ, E.obj (_root_.DerivedCategory.Q.obj P) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))
    [IsIso (rep (𝟙_ _))] : ∃! e, UnitNormalizationAux F E rep e := by
  have hC : IsIso (Functor.LaxMonoidal.ε (_root_.DerivedCategory.Q (C := C))) := by
    have := _root_.DerivedCategory.isIso_ε_Qh C
    change IsIso ((Functor.LaxMonoidal.ε _root_.DerivedCategory.Qh ≫
      _root_.DerivedCategory.Qh.map
        (Functor.LaxMonoidal.ε (HomotopyCategory.quotient _ _))) ≫ _)
    infer_instance
  have hD : IsIso (Functor.LaxMonoidal.ε (_root_.DerivedCategory.Q (C := D))) := by
    have := _root_.DerivedCategory.isIso_ε_Qh D
    change IsIso ((Functor.LaxMonoidal.ε _root_.DerivedCategory.Qh ≫
      _root_.DerivedCategory.Qh.map
        (Functor.LaxMonoidal.ε (HomotopyCategory.quotient _ _))) ≫ _)
    infer_instance
  have hη : IsIso (Functor.OplaxMonoidal.mapHomologicalComplexη (.up ℤ) F) := by
    unfold Functor.OplaxMonoidal.mapHomologicalComplexη
    infer_instance
  let a := E.map (Functor.LaxMonoidal.ε _root_.DerivedCategory.Q) ≫ rep (𝟙_ _) ≫
    _root_.DerivedCategory.Q.map
      (Functor.OplaxMonoidal.mapHomologicalComplexη (.up ℤ) F)
  let b := Functor.LaxMonoidal.ε (_root_.DerivedCategory.Q (C := D))
  have : IsIso a := by dsimp only [a]; infer_instance
  refine ⟨asIso a ≪≫ (asIso b).symm, ?_, ?_⟩
  · change a = (a ≫ inv b) ≫ b
    simp
  · intro e he
    apply Iso.ext
    apply (cancel_mono b).1
    change e.hom ≫ b = (a ≫ inv b) ≫ b
    change a = e.hom ≫ b at he
    rw [← he]
    simp

/-- The scalar unit comparison is uniquely normalized by multiplication B tensor_A A -> B.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison).
Proof: the unit complex is flat and K-flat. Its derived counit, the localization
unit comparison and ordinary scalar unit are invertible. Solve the normalization
equation for e; cancellation gives uniqueness. -/
theorem unitIso_existsUnique (T : Scheme.{u}) :
    ∃! e, UnitNormalization φ T e := by
  have h := extension_preservesKFlatQuasiIso φ T
  have hrep : IsIso (scalarExtensionRepresentative φ T
      (𝟙_ (CochainComplex (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ))) := by
    unfold scalarExtensionRepresentative
    rw [← mapComplex_unit_formula]
    exact Adjunction.isIso_cochainTranspose_of_kFlat _ _
      (ProEtale.etaleSheafExtendScalarsAdjunction φ T) (Adjunction.ofIsRightAdjoint _) _
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat.prop_unit
  have hη : IsIso (Functor.OplaxMonoidal.η (ProEtale.etaleSheafExtendScalars φ T)) := by
    exact isIso_η_composeAndSheafify T.smallEtaleTopology
      (ModuleCat.extendRestrictScalarsAdj.{u + 1} φ)
  exact unitNormalizationAux_existsUnique (ProEtale.etaleSheafExtendScalars φ T)
    (scalarExtension φ T) (scalarExtensionRepresentative φ T)


/-- Canonical scalar unit identification, selected by its unique normalization.
Source: Stacks 07A4 (blueprint: lem-pur-exceptional-coefficient-comparison). -/
def unitIso (T : Scheme.{u}) :
    (scalarExtension φ T).obj (𝟙_ (DerivedCategoryModule A T)) ≅
      𝟙_ (DerivedCategoryModule B T) :=
  (unitIso_existsUnique φ T).choose
```

## New

All public signatures and all bodies of definitions above are verbatim in
`Sheaf.Paper.ExceptionalCoefficientMaps`. The private K-flat preservation helper
now applies the identical proved helper from `EtaleHomComparisonModels`, opened
through a private `import all`; its signature is unchanged. The reverse flat-model
normalization implication is proved in the abstract categories before site
specialization. The unit-existence proof solves the same normalization equation
through a site-level specialization of its original generic construction, with
unit-representative invertibility proved separately. Its unique object and the `unitIso` definition stay the
same. These proof changes avoid repeated expansion of monoidal instance data.
The original module also uses a private componentwise compact-support isomorphism
with proved component equations, sealed for the later mate proofs. No consumer
uses that private construction. For the extracted declarations, the old module adds:

```lean
public import Sheaf.Paper.ExceptionalCoefficientMaps
```

`Sheaf.Paper.EtaleCompactScalarCoherence` replaces its old public import
`Sheaf.Paper.ExceptionalCoefficientComparison` by
`Sheaf.Paper.ExceptionalCoefficientMaps`. Its declarations and four unproved theorem
bodies are unchanged. Only normalized maps were used from the old import.


## Canonical tensor-domain component interface

The additional definition repair is in the held item module
`Sheaf.Paper.ExceptionalCoefficientComparison` (holder T1).
The old `tensorDomainMap` body was `δ ≫ κ ≫ v`, where `δ` is the normalized tensor
comparison, `κ` is the tensor image of inverse scalar pullback, and `v` is the
tensor image of `mateMap` at the coefficient unit followed by `G_B(unitIso)`.
The new body is `compactScalarProjectionTarget φ f K ω ≫ v`.
The published definition of `compactScalarProjectionTarget` is exactly `δ ≫ κ`.
Thus the old body is `δ ≫ (κ ≫ v)` and the new is `(δ ≫ κ) ≫ v`.
`Category.assoc δ κ v` proves their equality. No component arrow or endpoint changes.

This changes the parenthesization of the definition, so the independent statement
review must check that equality; it is not claimed to be a verbatim body change.
The definition's signature and the entire `TensorCompatibility` statement remain
verbatim. The old expanded private API is replaced by a definitional component
API. The main module publicly imports `EtaleCompactScalarCoherence` for this
published definition. The tensor-definition node adds this dependency; no path
from that dependency back to the tensor-definition node exists.

A search of all live `lean/Sheaf`, `lean/WeilConjectures` and archived
`quarantine/Sheaf` sources finds
`tensorDomainMap` only in its defining module and its `TensorCompatibility` body.
There are no external direct uses to adapt. Every other existing public definition
body is unchanged. The right-unit module also provides a proved private generic component
accessor for its normalization predicate, used by a proof-only `import all` in the
main module; it introduces no assumption or new hole. The coefficient unit is
written literally as `𝟙_ (DerivedCategoryModule A Y)` in the repaired body and
private calculations. `constantComplex A Y` is defined as this very unit in
`WeilConjectures.SixFunctors.Etale.Derived.Coefficients`, so this notational
replacement is definitionally equal. It avoids repeated normalization of the
stored monoidal instance. The public signature does not change.


The unit-mate composite is additionally named `dualizingScalarMap`, a public
construction in the original item module with the already required finite
coefficient instances. Its body is literally the original `mateMap` at the unit
followed by the upper-shriek image of `unitIso`. Its private defining-equation lemma
is proved by reflexivity. `tensorDomainMap` now tensors this named arrow. Unfolding
the added definition and applying `Category.assoc` recovers the old body. No existing
signature changes and no consumer adaptation is needed.

The private proof API also records ordered projections as isomorphisms with explicit
forward and inverse fields. A private compact-support isomorphism is typed with the
native chosen lower-shriek functors. These interfaces share the constructions used
by the tensor square and adjunction, avoiding repeated normalization of inverse
choices and chosen compactifications. All these constructions and equations are
proved in the packet; they add no assumptions.
The tensor proof locally restores `backward.isDefEq.respectTransparency` and its
`types` counterpart to `true`. Its data interfaces then retain their intended
irreducibility during elaboration. This changes elaboration only; the full proof
is checked in the original module with the unchanged 60-second limit.

## Users

`tools/downstream.py` with `--uses openIso compactSupportMap comparisonInverse
mateMap tensorIso unitIso UnitNormalization TensorNormalization` listed the live consumers
below. Archived consumers were also searched for those names and `import all`.
There is no live or archived `import all ExceptionalCoefficientComparison` consumer.
The 24 existing public declaration signatures were compared textually against the
union of the two new files; all match. Named map definitions and normalization
predicates are moved verbatim, so their definitional behavior also stays the same.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ExceptionalCoefficientComparison | T1 | Reexports the lower maps; fills the tensor/base-change proof. |
| Sheaf.Paper.EtaleCompactScalarCoherence | unclaimed | Public import redirected to the lower maps module; signatures and proofs unchanged. |
| Sheaf.Paper.EtaleFiniteCoefficientHomArrow | Y5 | No adaptation: the original module publicly reexports the same declarations. |
| Sheaf.Paper.FiniteCoefficientSiteChainTensor | A4 | No adaptation: the original module publicly reexports the same declarations. |
| Sheaf.Paper.FiniteCoefficientSiteHomArrow | Y7 | No adaptation: the original module publicly reexports the same declarations. |
| Sheaf.Paper.FiniteCoefficientSiteScalarArrow | Y8 | No adaptation: the original module publicly reexports the same declarations. |
| Sheaf.Paper.FiniteSmoothAdjunctionData | unclaimed | No adaptation: the original module publicly reexports the same declarations. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | unclaimed | No adaptation: the original module publicly reexports the same declarations. |
| Sheaf.Paper.FiniteSmoothCoefficientArrows | unclaimed | No adaptation: the original module publicly reexports the same declarations. |
| Sheaf.Paper.FiniteSmoothIntrinsicLevelProperties | unclaimed | No adaptation: the original module publicly reexports the same declarations. |
| Sheaf.Paper.FiniteSmoothLevelOfOrientation | unclaimed | No adaptation: the original module publicly reexports the same declarations. |
| Sheaf.Paper.FiniteSmoothPurityMaps | unclaimed | No adaptation: the original module publicly reexports the same declarations. |
| Sheaf.Paper.FiniteSmoothQuotientCoherence | unclaimed | No adaptation: the original module publicly reexports the same declarations. |
| Sheaf.Paper.FiniteSmoothSiteRealizations | unclaimed | No adaptation: the original module publicly reexports the same declarations. |
| Sheaf.Paper.FiniteSmoothTwoLevelReduction | unclaimed | No adaptation: the original module publicly reexports the same declarations. |
| Sheaf.Paper.VectorBundlePurity | unclaimed | No adaptation: the original module publicly reexports the same declarations. |
| Sheaf.Paper.VectorPurityFiniteReduction | unclaimed | No adaptation: the original module publicly reexports the same declarations. |
| Sheaf.Paper.VectorPurityScalarSingle | unclaimed | No adaptation: the original module publicly reexports the same declarations. |
| Sheaf.Paper.FiniteFreeCoefficientExtension (rework archive also checked) | unclaimed | Preserved interface; live and archived consumers not edited. |
| Sheaf.Paper.EtaleProEtaleCoefficientCompatibility (rework archive also checked) | unclaimed | Preserved interface; live and archived consumers not edited. |
| Sheaf.SixFunctors.FiniteCoefficientVerdier (rework archive also checked) | unclaimed | Preserved normalization interface; live and archived consumers not edited. |
| Sheaf.AlgebraicGeometry.FiniteOrdinaryPullback | unclaimed | Lexical homonym only: its unitIso occurrences are equivalence units. No exceptional coefficient map is used; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | unclaimed | Lexical homonym only: tensorIso is the ordinary monoidal tensor of two isomorphisms. No adaptation. |
| Sheaf.Paper.AffineSpacePurityComparison | unclaimed | Lexical homonym only: it defines its own tensorIso for the affine-space comparison coordinates. No adaptation. |
| Sheaf.Paper.AffineSpacePurityComposition | unclaimed | Lexical homonym only: tensorIso is the affine-space comparison tensor of isomorphisms, not scalar normalization. No adaptation. |
| Sheaf.Paper.AffineSpaceZeroSectionPurity | unclaimed | Lexical homonym only: its explicit AffineSpacePurity.tensorIso is the affine-space comparison tensor of isomorphisms, not ExceptionalCoefficients.tensorIso. No adaptation. |
| Sheaf.Paper.AmbientDiagonalPurityBaseChange | unclaimed | Lexical homonym only: tensorIso tensors isomorphisms in its generic monoidal construction. No adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | unclaimed | Lexical homonym only: unitIso is a derived equivalence or RingedSiteDualityModel unit field. No adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | unclaimed | Lexical homonym only: unitIso is the intrinsic equivalence unit. No adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | unclaimed | Lexical homonym only: unitIso is the intrinsic derived equivalence unit. No adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Lexical homonym only: unitIso is the intrinsic derived equivalence unit. No adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Lexical homonym only: unitIso is an intrinsic derived equivalence unit or RingedSiteDualityModel field. No adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Lexical homonym only: unitIso is the derived equivalence unit, not ExceptionalCoefficients.unitIso. No adaptation. |
| Sheaf.Paper.TraceGraphCorrespondence | unclaimed | Lexical homonym only: unitIso is the intrinsic derived equivalence unit. No adaptation. |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | Lexical homonym only: unitIso is an equivalence structure field. No adaptation. |

| Sheaf.Paper.VectorIntegrationSiteComparison | unclaimed | Lexical homonym only: its TensorCompatibility has coefficient-prime, level and integration data parameters, and is its independent integration predicate. No adaptation. |

The additional fifteen rows are lexical matches from the downstream checker.
Their occurrences were inspected in their own source namespaces and structure fields;
they do not refer to the extracted exceptional coefficient normalizations.

The two live direct importers of `EtaleCompactScalarCoherence`,
`VectorBundlePurity` and `EtaleProEtaleCoefficientCompatibility`, use none of the
public declarations retained in the old main module. Redirecting the coherence
module's import therefore removes no declaration that either consumer uses.
The omitted public dependencies `FiniteReductionConstructibility` and
`SmoothExceptionalBaseChange` remain visible to `VectorBundlePurity` through its
other imports. `EtaleProEtaleCoefficientCompatibility` uses neither their finite
reduction declarations nor their smooth exceptional comparison declarations.

## Status

landed 20261022T022048-L-433470 2026-10-22 (merge of deliver/T1/Sheaf.Paper.ExceptionalCoefficientComparison)

The coherence node now explicitly cites the lower normalization and compact-support
map definition owners in its statement text. Its statement-change record archives
the previous text and dependencies and audits all six existing citers. This only
clarifies ownership of the same normalized arrows; the four Lean theorem signatures,
inputs, equations and proof bodies remain unchanged. The tensor-map definition node
also carries its complete statement-change archive and sole-citer audit.
