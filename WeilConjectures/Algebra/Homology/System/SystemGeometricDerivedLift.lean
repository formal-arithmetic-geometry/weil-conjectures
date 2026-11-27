/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.GeometricSystemOrdinaryData.SystemGeometricOrdinaryComparison
public import WeilConjectures.Algebra.Homology.SmoothPurity.ExtensionEvaluationComparison
import WeilConjectures.Algebra.Homology.System.SystemDerivedEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose
import WeilConjectures.Algebra.Homology.System.DerivedExtensionEvaluationPasting
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
import WeilConjectures.Algebra.Homology.System.SystemScalarCoherence
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Normalized derived lift of the geometric singleton comparison

## References

* Stacks Project, Tag 0FND
* Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1
-/

set_option Elab.async false

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace SheafOfModules
open MonoidalCategory
open scoped TensorProduct ChangeOfRings

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
  (BY : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (BX : ℕᵒᵖ ⥤ Sheaf K CommRingCat.{w})
  (u : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w)))
  (I : ∀ n : ℕ, AlgebraicInverseImage u.inverse (BY.obj (op n)) (BX.obj (op n)))

variable {BY BX u I}
variable (SY : SystemScalarAssignment (J := J)) (TY : SystemTensorCoherence SY)
  (SX : SystemScalarAssignment (J := K)) (TX : SystemTensorCoherence SX)

/-- Level inverse images preserve flat-term K-flat complexes. -/
theorem GeometricSystemOrdinaryData.levelInverseImage_kFlat
    (F : GeometricSystemOrdinaryData BY BX u I) (n : ℕ)
    (Q : CochainComplex (systemLevel BY n) ℤ) (hQ : systemLevelKFlat BY n Q) :
    systemLevelKFlat BX n (((F.levelInverseImage n).mapHomologicalComplex (.up ℤ)).obj Q) := by
  let A := Classical.choice (nonempty_systemScalarModel (𝟙 (BX.obj (op n))))
  let G := (I n).modules
  have : G.Additive := F.levelAdditive n
  have : PreservesFiniteLimits u.inverse := u.leftExact
  have ht := isKFlat_ringedToposPullback u.inverse u.direct u.adj (I n)
    (𝟙 (BX.obj (op n))) (G ⋙ A.model.E)
    (fun P ↦ A.model.obj_eq (G.obj P))
    (fun f ↦ A.model.map_eq (G.map f)) Q hQ.1 hQ.2
  let e : G ⋙ A.model.E ≅ G :=
    isoWhiskerLeft G (systemScalarModelUnit rfl A) ≪≫ G.rightUnitor
  let ec := (NatIso.mapHomologicalComplex e (.up ℤ)).app Q
  exact ⟨kFlat_iso_independent (BX.obj (op n)) ec ht.1,
    fun i ↦ flatOnSite_of_iso (BX.obj (op n))
      ((HomologicalComplex.eval _ (.up ℤ) i).mapIso ec) (ht.2 i)⟩

/-- The unit of the ordinary singleton adjunction is the inverse multiplication isomorphism
at the selected level. -/
theorem systemSingleAdjunction_unit_app (S : SystemScalarAssignment (J := J))
    (T : SystemTensorCoherence S) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ)
    (P : systemLevel B n) :
    (systemSingleAdjunction S T B n).unit.app P =
      (systemSingleBelow S T B n (Nat.le_refl n) ≪≫ T.ordinaryUnit B n).inv.app P :=
  Category.comp_id (systemSingleUnit S T B n P)

/-- The derived evaluation square of a geometric system is computed by the ordinary
evaluation square. -/
theorem GeometricSystemOrdinaryData.derivedEvaluation_inv_model
    (F : GeometricSystemOrdinaryData BY BX u I) (n : ℕ)
    (K : CochainComplex (StrictRingSystem BY) ℤ) :
    (F.derivedEvaluation n).inv.app (DerivedCategory.Q.obj K) ≫
        (derivedSystemEvaluation BX n).map (F.functor.mapDerivedCategoryFactors.hom.app K) ≫
        (systemEvaluation BX n).mapDerivedCategoryFactors.hom.app
          ((F.functor.mapHomologicalComplex (.up ℤ)).obj K) =
      (F.levelInverseImage n).mapDerivedCategory.map
          ((systemEvaluation BY n).mapDerivedCategoryFactors.hom.app K) ≫
        (F.levelInverseImage n).mapDerivedCategoryFactors.hom.app
          (((systemEvaluation BY n).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (F := systemEvaluation BY n ⋙ F.levelInverseImage n) (F.evaluation n).inv
            (.up ℤ)).app K) :=
  mapDerivedCategorySquareIso_inv_model (F₁ := F.functor) (F₂ := systemEvaluation BX n)
    (G₁ := systemEvaluation BY n) (G₂ := F.levelInverseImage n) (F.evaluation n) K

/-- The ordinary singleton comparison is the mate of the inverse evaluation square. -/
theorem geometricSystem_ordinaryUnitSquare (F : GeometricSystemOrdinaryData BY BX u I)
    (ordinary : ∀ n : ℕ,
      systemSingleFunctor SY TY BY n ⋙ F.functor ≅
        F.levelInverseImage n ⋙ systemSingleFunctor SX TX BX n)
    (h_multiplication :
    (∀ (n : ℕ) (P : systemLevel BY n),
    ((ordinary n).hom.app P).app n ≫
        ((systemSingleBelow SX TX BX n (Nat.le_refl n) ≪≫ TX.ordinaryUnit BX n)).hom.app
          ((F.levelInverseImage n).obj P) =
      (F.evaluation n).hom.app ((systemSingleFunctor SY TY BY n).obj P) ≫
        (F.levelInverseImage n).map
          ((systemSingleBelow SY TY BY n (Nat.le_refl n) ≪≫
            TY.ordinaryUnit BY n).hom.app P)))
    (n : ℕ) (P : systemLevel BY n) :
    (systemSingleAdjunction SX TX BX n).homEquiv _ _ ((ordinary n).symm.hom.app P) =
      (F.levelInverseImage n).map ((systemSingleAdjunction SY TY BY n).unit.app P) ≫
        (F.evaluation n).inv.app ((systemSingleFunctor SY TY BY n).obj P) := by
  have hc : ((ordinary n).hom.app P).app n ≫ ((ordinary n).inv.app P).app n = 𝟙 _ := by
    erw [← (systemEvaluation BX n).map_comp, Iso.hom_inv_id_app,
      (systemEvaluation BX n).map_id]
    rfl
  rw [Adjunction.homEquiv_unit, systemSingleAdjunction_unit_app,
    systemSingleAdjunction_unit_app,
    ← cancel_epi ((F.levelInverseImage n).map
      ((systemSingleBelow SY TY BY n (Nat.le_refl n) ≪≫ TY.ordinaryUnit BY n).hom.app P)),
    ← cancel_epi ((F.evaluation n).hom.app ((systemSingleFunctor SY TY BY n).obj P)),
    ← reassoc_of% (h_multiplication n P)]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
  exact hc

/-- The derived singleton comparison: the inverse of the derived mate of the ordinary
singleton comparison. -/
def geometricSystemDerivedComparison (F : GeometricSystemOrdinaryData BY BX u I)
    (ordinary : ∀ n : ℕ,
      systemSingleFunctor SY TY BY n ⋙ F.functor ≅
        F.levelInverseImage n ⋙ systemSingleFunctor SX TX BX n)
    (h_multiplication :
    (∀ (n : ℕ) (P : systemLevel BY n),
    ((ordinary n).hom.app P).app n ≫
        ((systemSingleBelow SX TX BX n (Nat.le_refl n) ≪≫ TX.ordinaryUnit BX n)).hom.app
          ((F.levelInverseImage n).obj P) =
      (F.evaluation n).hom.app ((systemSingleFunctor SY TY BY n).obj P) ≫
        (F.levelInverseImage n).map
          ((systemSingleBelow SY TY BY n (Nat.le_refl n) ≪≫
            TY.ordinaryUnit BY n).hom.app P)))
    (n : ℕ) :
    (systemSingleDerivedExtension BY n SY TY).derived ⋙ F.functor.mapDerivedCategory ≅
      (F.levelInverseImage n).mapDerivedCategory ⋙
        (systemSingleDerivedExtension BX n SX TX).derived :=
  derivedExtensionEvaluationIso (systemSingleDerivedExtension BY n SY TY)
    (systemSingleDerivedExtension BX n SX TX) (F.levelInverseImage n) F.functor
    (F.levelInverseImage n).mapDerivedCategory (F.levelInverseImage n).mapDerivedCategoryFactors
    (F.derivedEvaluation n).inv (F.evaluation n).inv (F.derivedEvaluation_inv_model n)
    (ordinary n).symm (geometricSystem_ordinaryUnitSquare SY TY SX TX F ordinary h_multiplication n)
    (systemLevel_kFlatResolution BY n) (fun P hP ↦ F.levelInverseImage_kFlat n P hP)

/-- The ordinary scalar comparison of a geometric system, transposed along the two
ordinary scalar adjunctions. -/
def geometricSystemScalarMate (F : GeometricSystemOrdinaryData BY BX u I)
    (tensor : ∀ {j n : ℕ} (h : j ≤ n),
      systemTensor SY BY h ⋙ F.levelInverseImage j ≅
        F.levelInverseImage n ⋙ systemTensor SX BX h)
    {n m : ℕ} (h : n ≤ m) :
    systemRestriction BY h ⋙ F.levelInverseImage m ⟶
      F.levelInverseImage n ⋙ systemRestriction BX h :=
  mateEquiv (systemTensorAdj SY BY h) (systemTensorAdj SX BX h) (tensor h).inv

/-- The derived scalar exchange induced by the ordinary scalar mate. -/
def geometricSystemDerivedScalarMate (F : GeometricSystemOrdinaryData BY BX u I)
    (tensor : ∀ {j n : ℕ} (h : j ≤ n),
      systemTensor SY BY h ⋙ F.levelInverseImage j ≅
        F.levelInverseImage n ⋙ systemTensor SX BX h)
    {n m : ℕ} (h : n ≤ m) :
    (systemRestriction BY h).mapDerivedCategory ⋙ (F.levelInverseImage m).mapDerivedCategory ⟶
      (F.levelInverseImage n).mapDerivedCategory ⋙
        (systemRestriction BX h).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).hom ≫
    Functor.mapDerivedCategoryNatTrans (geometricSystemScalarMate SY SX F tensor h) ≫
    (Functor.mapDerivedCategoryCompIso _ _).inv

/-- The derived scalar exchange is computed by the ordinary scalar mate. -/
theorem geometricSystemDerivedScalarMate_model (F : GeometricSystemOrdinaryData BY BX u I)
    (tensor : ∀ {j n : ℕ} (h : j ≤ n),
      systemTensor SY BY h ⋙ F.levelInverseImage j ≅
        F.levelInverseImage n ⋙ systemTensor SX BX h)
    {n m : ℕ} (h : n ≤ m) (K : CochainComplex (systemLevel BY n) ℤ) :
    (geometricSystemDerivedScalarMate SY SX F tensor h).app (DerivedCategory.Q.obj K) ≫
        (systemRestriction BX h).mapDerivedCategory.map
          ((F.levelInverseImage n).mapDerivedCategoryFactors.hom.app K) ≫
        (systemRestriction BX h).mapDerivedCategoryFactors.hom.app
          (((F.levelInverseImage n).mapHomologicalComplex (.up ℤ)).obj K) =
      (F.levelInverseImage m).mapDerivedCategory.map
          ((systemRestriction BY h).mapDerivedCategoryFactors.hom.app K) ≫
        (F.levelInverseImage m).mapDerivedCategoryFactors.hom.app
          (((systemRestriction BY h).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map (((geometricSystemScalarMate SY SX F tensor h).mapHomologicalComplex
          (.up ℤ)).app K) := by
  dsimp only [geometricSystemDerivedScalarMate, NatTrans.comp_app]
  rw [Category.assoc, Category.assoc, Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatTrans_fac,
    ← Functor.mapDerivedCategoryCompIso_hom_app_factors (systemRestriction BY h)
      (F.levelInverseImage m) K]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- The ordinary scalar comparison is the transpose of its scalar mate. -/
theorem geometricSystemScalarMate_unit (F : GeometricSystemOrdinaryData BY BX u I)
    (tensor : ∀ {j n : ℕ} (h : j ≤ n),
      systemTensor SY BY h ⋙ F.levelInverseImage j ≅
        F.levelInverseImage n ⋙ systemTensor SX BX h)
    {n m : ℕ} (h : n ≤ m) (P : systemLevel BY m) :
    (systemTensorAdj SX BX h).homEquiv _ _ ((tensor h).symm.hom.app P) =
      (F.levelInverseImage m).map ((systemTensorAdj SY BY h).unit.app P) ≫
        (geometricSystemScalarMate SY SX F tensor h).app ((systemTensor SY BY h).obj P) := by
  rw [Adjunction.homEquiv_unit]
  exact (unit_mateEquiv (systemTensorAdj SY BY h) (systemTensorAdj SX BX h) (tensor h).inv P).symm

/-- The derived scalar mate of a geometric system is invertible. -/
theorem geometricSystemScalar_isIso (F : GeometricSystemOrdinaryData BY BX u I)
    (tensor : ∀ {j n : ℕ} (h : j ≤ n),
      systemTensor SY BY h ⋙ F.levelInverseImage j ≅
        F.levelInverseImage n ⋙ systemTensor SX BX h)
    {n m : ℕ} (h : n ≤ m) :
    IsIso (derivedExtensionMate (systemScalarModelExtension (SY (BY.map (homOfLE h).op)))
      (systemScalarModelExtension (SX (BX.map (homOfLE h).op))) (F.levelInverseImage n)
      (F.levelInverseImage m).mapDerivedCategory
      (geometricSystemDerivedScalarMate SY SX F tensor h)) :=
  derivedExtensionMate_isIso_of_resolving _ _ (F.levelInverseImage m) (F.levelInverseImage n)
    _ (F.levelInverseImage m).mapDerivedCategoryFactors _
    (geometricSystemScalarMate SY SX F tensor h)
    (geometricSystemDerivedScalarMate_model SY SX F tensor h) (tensor h).symm
    (geometricSystemScalarMate_unit SY SX F tensor h) (systemLevelKFlat BY m)
    (systemLevel_kFlatResolution BY m) (fun _ hP ↦ hP.1)
    (fun P hP ↦ (F.levelInverseImage_kFlat m P hP).1)

/-- The derived scalar comparison of a geometric system: the inverse of the derived mate
of the ordinary scalar comparison. -/
def geometricSystemDerivedScalar (F : GeometricSystemOrdinaryData BY BX u I)
    (tensor : ∀ {j n : ℕ} (h : j ≤ n),
      systemTensor SY BY h ⋙ F.levelInverseImage j ≅
        F.levelInverseImage n ⋙ systemTensor SX BX h)
    {n m : ℕ} (h : n ≤ m) :
    systemDerivedTensor SY BY h ⋙ (F.levelInverseImage n).mapDerivedCategory ≅
      (F.levelInverseImage m).mapDerivedCategory ⋙ systemDerivedTensor SX BX h :=
  have := geometricSystemScalar_isIso SY SX F tensor h
  (asIso (derivedExtensionMate (systemScalarModelExtension (SY (BY.map (homOfLE h).op)))
      (systemScalarModelExtension (SX (BX.map (homOfLE h).op))) (F.levelInverseImage n)
      (F.levelInverseImage m).mapDerivedCategory
      (geometricSystemDerivedScalarMate SY SX F tensor h))).symm

/-- The below-level derived singleton comparison is computed by the ordinary one. -/
theorem systemSingleDerivedBelow_rep (S : SystemScalarAssignment (J := J))
    (T : SystemTensorCoherence S) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) {m n : ℕ}
    (h : m ≤ n) (L : CochainComplex (systemLevel B n) ℤ) :
    (systemSingleDerivedBelow B h S T).hom.app (DerivedCategory.Q.obj L) ≫
        (S (B.map (homOfLE h).op)).model.ε.app L =
      (derivedSystemEvaluation B m).map
          ((systemSingleDerivedExtension B n S T).comparison.app L) ≫
        (systemEvaluation B m).mapDerivedCategoryFactors.hom.app
          (((systemSingleFunctor S T B n).mapHomologicalComplex (.up ℤ)).obj L) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (systemSingleBelow S T B n h) (.up ℤ)).hom.app L) := by
  have hb := derivedExtensionMate_iso_rep (systemSingleDerivedExtension B n S T)
    (systemScalarModelExtension (S (B.map (homOfLE h).op)))
    (𝟭 (systemLevel B n)) (systemEvaluation B m) (𝟭 _) (systemSingleIdentityFactors B (n := n))
    _ (systemSingleDerivedBelow B h S T) rfl
    ((Functor.rightUnitor (systemEvaluation B n)).hom ≫ strictSystemTransition B h)
    (systemSingleDerivedSquare_rep B h)
    (Functor.leftUnitor (systemTensor S B h) ≪≫ (systemSingleBelow S T B n h).symm)
    (systemSingleOrdinaryUnitSquare S T B h) L
  have hι : (NatIso.mapHomologicalComplex (Functor.leftUnitor (systemTensor S B h) ≪≫
      (systemSingleBelow S T B n h).symm) (.up ℤ)).inv.app L =
      (NatIso.mapHomologicalComplex (systemSingleBelow S T B n h) (.up ℤ)).hom.app L := by
    ext i
    simp
  rw [hι] at hb
  refine Eq.trans ?_ hb
  dsimp only [systemSingleIdentityFactors, Iso.refl_hom, NatTrans.id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

/-- The derived multiplication at the selected level is computed by the ordinary one on
flat-term K-flat complexes. -/
theorem systemSingleDerivedMultiplication_rep (S : SystemScalarAssignment (J := J))
    (T : SystemTensorCoherence S) (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ)
    (L : CochainComplex (systemLevel B n) ℤ) (hL : systemLevelKFlat B n L) :
    (systemSingleDerivedBelow B (Nat.le_refl n) S T ≪≫ T.derivedUnit B n).hom.app
        (DerivedCategory.Q.obj L) =
      (derivedSystemEvaluation B n).map
          ((systemSingleDerivedExtension B n S T).comparison.app L) ≫
        (systemEvaluation B n).mapDerivedCategoryFactors.hom.app
          (((systemSingleFunctor S T B n).mapHomologicalComplex (.up ℤ)).obj L) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (systemSingleBelow S T B n (Nat.le_refl n) ≪≫ T.ordinaryUnit B n) (.up ℤ)).hom.app
            L) := by
  rw [Iso.trans_hom, NatTrans.comp_app, T.derivedUnit_rep B n L hL,
    reassoc_of% (systemSingleDerivedBelow_rep S T B (Nat.le_refl n) L), ← Functor.map_comp]
  congr 3

/-- The derived evaluation square of a geometric system is computed by the ordinary
evaluation square. -/
theorem GeometricSystemOrdinaryData.derivedEvaluation_hom_model
    (F : GeometricSystemOrdinaryData BY BX u I) (n : ℕ)
    (K : CochainComplex (StrictRingSystem BY) ℤ) :
    (F.derivedEvaluation n).hom.app (DerivedCategory.Q.obj K) ≫
        (F.levelInverseImage n).mapDerivedCategory.map
          ((systemEvaluation BY n).mapDerivedCategoryFactors.hom.app K) ≫
        (F.levelInverseImage n).mapDerivedCategoryFactors.hom.app
          (((systemEvaluation BY n).mapHomologicalComplex (.up ℤ)).obj K) =
      (derivedSystemEvaluation BX n).map (F.functor.mapDerivedCategoryFactors.hom.app K) ≫
        (systemEvaluation BX n).mapDerivedCategoryFactors.hom.app
          ((F.functor.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (G := systemEvaluation BY n ⋙ F.levelInverseImage n) (F.evaluation n).hom
            (.up ℤ)).app K) :=
  mapDerivedCategorySquareIso_hom_model (F₁ := F.functor) (F₂ := systemEvaluation BX n)
    (G₁ := systemEvaluation BY n) (G₂ := F.levelInverseImage n) (F.evaluation n) K

/-- The derived singleton comparison is computed by the ordinary singleton comparison. -/
theorem geometricSystemDerivedComparison_rep (F : GeometricSystemOrdinaryData BY BX u I)
    (ordinary : ∀ n : ℕ,
      systemSingleFunctor SY TY BY n ⋙ F.functor ≅
        F.levelInverseImage n ⋙ systemSingleFunctor SX TX BX n)
    (h_multiplication :
    (∀ (n : ℕ) (P : systemLevel BY n),
    ((ordinary n).hom.app P).app n ≫
        ((systemSingleBelow SX TX BX n (Nat.le_refl n) ≪≫ TX.ordinaryUnit BX n)).hom.app
          ((F.levelInverseImage n).obj P) =
      (F.evaluation n).hom.app ((systemSingleFunctor SY TY BY n).obj P) ≫
        (F.levelInverseImage n).map
          ((systemSingleBelow SY TY BY n (Nat.le_refl n) ≪≫
            TY.ordinaryUnit BY n).hom.app P)))
    (n : ℕ) (Q : CochainComplex (systemLevel BY n) ℤ) :
    (geometricSystemDerivedComparison SY TY SX TX F ordinary h_multiplication n).hom.app
        (DerivedCategory.Q.obj Q) ≫
        (systemSingleDerivedExtension BX n SX TX).derived.map
          ((F.levelInverseImage n).mapDerivedCategoryFactors.hom.app Q) ≫
        (systemSingleDerivedExtension BX n SX TX).comparison.app
          (((F.levelInverseImage n).mapHomologicalComplex (.up ℤ)).obj Q) =
      F.functor.mapDerivedCategory.map
          ((systemSingleDerivedExtension BY n SY TY).comparison.app Q) ≫
        F.functor.mapDerivedCategoryFactors.hom.app
          (((systemSingleFunctor SY TY BY n).mapHomologicalComplex (.up ℤ)).obj Q) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (ordinary n) (.up ℤ)).hom.app Q) :=
  derivedExtensionMate_iso_rep (systemSingleDerivedExtension BY n SY TY)
    (systemSingleDerivedExtension BX n SX TX) (F.levelInverseImage n) F.functor _ _ _
    (geometricSystemDerivedComparison SY TY SX TX F ordinary h_multiplication n) rfl
    (F.evaluation n).inv (F.derivedEvaluation_inv_model n) (ordinary n).symm
    (geometricSystem_ordinaryUnitSquare SY TY SX TX F ordinary h_multiplication n) Q

/-- The derived scalar comparison is computed by the ordinary scalar comparison. -/
theorem geometricSystemDerivedScalar_rep (F : GeometricSystemOrdinaryData BY BX u I)
    (tensor : ∀ {j n : ℕ} (h : j ≤ n),
      systemTensor SY BY h ⋙ F.levelInverseImage j ≅
        F.levelInverseImage n ⋙ systemTensor SX BX h)
    {n m : ℕ} (h : n ≤ m) (Q : CochainComplex (systemLevel BY m) ℤ) :
    (geometricSystemDerivedScalar SY SX F tensor h).hom.app (DerivedCategory.Q.obj Q) ≫
        (systemDerivedTensor SX BX h).map
          ((F.levelInverseImage m).mapDerivedCategoryFactors.hom.app Q) ≫
        (SX (BX.map (homOfLE h).op)).model.ε.app
          (((F.levelInverseImage m).mapHomologicalComplex (.up ℤ)).obj Q) =
      (F.levelInverseImage n).mapDerivedCategory.map
          ((SY (BY.map (homOfLE h).op)).model.ε.app Q) ≫
        (F.levelInverseImage n).mapDerivedCategoryFactors.hom.app
          (((systemTensor SY BY h).mapHomologicalComplex (.up ℤ)).obj Q) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (tensor h) (.up ℤ)).hom.app Q) :=
  derivedExtensionMate_iso_rep (systemScalarModelExtension (SY (BY.map (homOfLE h).op)))
    (systemScalarModelExtension (SX (BX.map (homOfLE h).op))) (F.levelInverseImage m)
    (F.levelInverseImage n) _ _ _ _ rfl (geometricSystemScalarMate SY SX F tensor h)
    (geometricSystemDerivedScalarMate_model SY SX F tensor h) (tensor h).symm
    (geometricSystemScalarMate_unit SY SX F tensor h) Q

/-- The derived singleton comparison is compatible with multiplication at the selected
level. -/
theorem geometricSystemDerivedComparison_multiplication
    (F : GeometricSystemOrdinaryData BY BX u I)
    (ordinary : ∀ n : ℕ,
      systemSingleFunctor SY TY BY n ⋙ F.functor ≅
        F.levelInverseImage n ⋙ systemSingleFunctor SX TX BX n)
    (h_multiplication :
    (∀ (n : ℕ) (P : systemLevel BY n),
    ((ordinary n).hom.app P).app n ≫
        ((systemSingleBelow SX TX BX n (Nat.le_refl n) ≪≫ TX.ordinaryUnit BX n)).hom.app
          ((F.levelInverseImage n).obj P) =
      (F.evaluation n).hom.app ((systemSingleFunctor SY TY BY n).obj P) ≫
        (F.levelInverseImage n).map
          ((systemSingleBelow SY TY BY n (Nat.le_refl n) ≪≫
            TY.ordinaryUnit BY n).hom.app P)))
    (n : ℕ) (P : DerivedCategory (systemLevel BY n)) :
    (derivedSystemEvaluation BX n).map
        ((geometricSystemDerivedComparison SY TY SX TX F ordinary h_multiplication n).hom.app
          P) ≫
        ((systemSingleDerivedBelow BX (Nat.le_refl n) SX TX ≪≫ TX.derivedUnit BX n)).hom.app
          ((F.levelInverseImage n).mapDerivedCategory.obj P) =
      (F.derivedEvaluation n).hom.app ((systemSingleDerivedExtension BY n SY TY).derived.obj P) ≫
        (F.levelInverseImage n).mapDerivedCategory.map
          ((systemSingleDerivedBelow BY (Nat.le_refl n) SY TY ≪≫
            TY.derivedUnit BY n).hom.app P) := by
  exact derivedEvaluation_pasting_id (L₁ := systemSingleFunctor SY TY BY n)
    (L₂ := systemSingleFunctor SX TX BX n) (G := F.levelInverseImage n) (H := F.functor)
    (R₁ := systemEvaluation BY n) (R₂ := systemEvaluation BX n)
    (systemSingleDerivedExtension BY n SY TY).derived
    (systemSingleDerivedExtension BX n SX TX).derived
    (systemSingleDerivedExtension BY n SY TY).comparison
    (systemSingleDerivedExtension BX n SX TX).comparison
    (systemSingleDerivedBelow BY (Nat.le_refl n) SY TY ≪≫ TY.derivedUnit BY n)
    (systemSingleDerivedBelow BX (Nat.le_refl n) SX TX ≪≫ TX.derivedUnit BX n)
    (systemSingleBelow SY TY BY n (Nat.le_refl n) ≪≫ TY.ordinaryUnit BY n)
    (systemSingleBelow SX TX BX n (Nat.le_refl n) ≪≫ TX.ordinaryUnit BX n)
    (geometricSystemDerivedComparison SY TY SX TX F ordinary h_multiplication n) (ordinary n)
    (F.derivedEvaluation n) (F.evaluation n) (systemLevelKFlat BY n) (systemLevelKFlat BX n)
    (systemLevel_kFlatResolution BY n) (fun K hK ↦ F.levelInverseImage_kFlat n K hK)
    (fun K _ ↦ geometricSystemDerivedComparison_rep SY TY SX TX F ordinary h_multiplication n K)
    (fun K hK ↦ systemSingleDerivedMultiplication_rep SY TY BY n K hK)
    (fun K hK ↦ systemSingleDerivedMultiplication_rep SX TX BX n K hK)
    (fun M ↦ F.derivedEvaluation_hom_model n M) (fun X ↦ (h_multiplication n X).symm) P

/-- The derived singleton comparison is compatible with the below-level identifications
and the derived scalar comparison. -/
theorem geometricSystemDerivedComparison_below (F : GeometricSystemOrdinaryData BY BX u I)
    (ordinary : ∀ n : ℕ,
      systemSingleFunctor SY TY BY n ⋙ F.functor ≅
        F.levelInverseImage n ⋙ systemSingleFunctor SX TX BX n)
    (tensor : ∀ {j n : ℕ} (h : j ≤ n),
      systemTensor SY BY h ⋙ F.levelInverseImage j ≅
        F.levelInverseImage n ⋙ systemTensor SX BX h)
    (h_tensor_evaluation :
    (∀ {j n : ℕ} (h : j ≤ n) (P : systemLevel BY n),
    (F.evaluation j).hom.app ((systemSingleFunctor SY TY BY n).obj P) ≫
        (F.levelInverseImage j).map ((systemSingleBelow SY TY BY n h).hom.app P) ≫
        (tensor h).hom.app P =
      ((ordinary n).hom.app P).app j ≫
        (systemSingleBelow SX TX BX n h).hom.app ((F.levelInverseImage n).obj P)))
    (h_multiplication :
    (∀ (n : ℕ) (P : systemLevel BY n),
    ((ordinary n).hom.app P).app n ≫
        ((systemSingleBelow SX TX BX n (Nat.le_refl n) ≪≫ TX.ordinaryUnit BX n)).hom.app
          ((F.levelInverseImage n).obj P) =
      (F.evaluation n).hom.app ((systemSingleFunctor SY TY BY n).obj P) ≫
        (F.levelInverseImage n).map
          ((systemSingleBelow SY TY BY n (Nat.le_refl n) ≪≫
            TY.ordinaryUnit BY n).hom.app P)))
    {n m : ℕ} (h : n ≤ m) (P : DerivedCategory (systemLevel BY m)) :
    (derivedSystemEvaluation BX n).map
        ((geometricSystemDerivedComparison SY TY SX TX F ordinary h_multiplication m).hom.app P) ≫
        (systemSingleDerivedBelow BX h SX TX).hom.app
          ((F.levelInverseImage m).mapDerivedCategory.obj P) =
      (F.derivedEvaluation n).hom.app ((systemSingleDerivedExtension BY m SY TY).derived.obj P) ≫
        (F.levelInverseImage n).mapDerivedCategory.map
          ((systemSingleDerivedBelow BY h SY TY).hom.app P) ≫
        (geometricSystemDerivedScalar SY SX F tensor h).hom.app P :=
  derivedEvaluation_pasting (L₁ := systemSingleFunctor SY TY BY m)
    (L₂ := systemSingleFunctor SX TX BX m) (E₁ := systemTensor SY BY h)
    (E₂ := systemTensor SX BX h) (R₁ := systemEvaluation BY n) (R₂ := systemEvaluation BX n)
    (G := F.levelInverseImage m) (G₀ := F.levelInverseImage n) (H := F.functor)
    (systemSingleDerivedExtension BY m SY TY).derived
    (systemSingleDerivedExtension BX m SX TX).derived
    (systemSingleDerivedExtension BY m SY TY).comparison
    (systemSingleDerivedExtension BX m SX TX).comparison
    (systemDerivedTensor SY BY h) (systemDerivedTensor SX BX h)
    (SY (BY.map (homOfLE h).op)).model.ε (SX (BX.map (homOfLE h).op)).model.ε
    (systemSingleDerivedBelow BY h SY TY) (systemSingleDerivedBelow BX h SX TX)
    (systemSingleBelow SY TY BY m h) (systemSingleBelow SX TX BX m h)
    (geometricSystemDerivedComparison SY TY SX TX F ordinary h_multiplication m) (ordinary m)
    (F.derivedEvaluation n) (F.evaluation n) (geometricSystemDerivedScalar SY SX F tensor h)
    (tensor h) (systemLevelKFlat BY m) (fun _ ↦ True) (systemLevel_kFlatResolution BY m)
    (fun _ _ ↦ trivial)
    (fun K hK ↦ (SX (BX.map (homOfLE h).op)).model.computes _
      (F.levelInverseImage_kFlat m K hK).1)
    (fun K _ ↦ geometricSystemDerivedComparison_rep SY TY SX TX F ordinary h_multiplication m K)
    (fun K _ ↦ systemSingleDerivedBelow_rep SY TY BY h K)
    (fun K _ ↦ systemSingleDerivedBelow_rep SX TX BX h K)
    (fun K _ ↦ geometricSystemDerivedScalar_rep SY SX F tensor h K)
    (fun M ↦ F.derivedEvaluation_hom_model n M) (fun X ↦ h_tensor_evaluation h X) P

/-- The derived singleton comparison is compatible with the lower-singleton maps. -/
theorem geometricSystemDerivedComparison_lower (F : GeometricSystemOrdinaryData BY BX u I)
    (ordinary : ∀ n : ℕ,
      systemSingleFunctor SY TY BY n ⋙ F.functor ≅
        F.levelInverseImage n ⋙ systemSingleFunctor SX TX BX n)
    (tensor : ∀ {j n : ℕ} (h : j ≤ n),
      systemTensor SY BY h ⋙ F.levelInverseImage j ≅
        F.levelInverseImage n ⋙ systemTensor SX BX h)
    (h_tensor_evaluation :
    (∀ {j n : ℕ} (h : j ≤ n) (P : systemLevel BY n),
    (F.evaluation j).hom.app ((systemSingleFunctor SY TY BY n).obj P) ≫
        (F.levelInverseImage j).map ((systemSingleBelow SY TY BY n h).hom.app P) ≫
        (tensor h).hom.app P =
      ((ordinary n).hom.app P).app j ≫
        (systemSingleBelow SX TX BX n h).hom.app ((F.levelInverseImage n).obj P)))
    (h_multiplication :
    (∀ (n : ℕ) (P : systemLevel BY n),
    ((ordinary n).hom.app P).app n ≫
        ((systemSingleBelow SX TX BX n (Nat.le_refl n) ≪≫ TX.ordinaryUnit BX n)).hom.app
          ((F.levelInverseImage n).obj P) =
      (F.evaluation n).hom.app ((systemSingleFunctor SY TY BY n).obj P) ≫
        (F.levelInverseImage n).map
          ((systemSingleBelow SY TY BY n (Nat.le_refl n) ≪≫
            TY.ordinaryUnit BY n).hom.app P)))
    {n m : ℕ} (h : n ≤ m) (P : DerivedCategory (systemLevel BY m)) :
    F.functor.mapDerivedCategory.map
        (((systemSingleDerivedExtension BY n SY TY).adjunction.homEquiv _ _).symm
          ((systemSingleDerivedBelow BY h SY TY).inv.app P)) ≫
        (geometricSystemDerivedComparison SY TY SX TX F ordinary h_multiplication m).hom.app P =
      (geometricSystemDerivedComparison SY TY SX TX F ordinary h_multiplication n).hom.app
          ((systemDerivedTensor SY BY h).obj P) ≫
        (systemSingleDerivedExtension BX n SX TX).derived.map
          ((geometricSystemDerivedScalar SY SX F tensor h).hom.app P) ≫
        (((systemSingleDerivedExtension BX n SX TX).adjunction.homEquiv _ _).symm
          ((systemSingleDerivedBelow BX h SX TX).inv.app
            ((F.levelInverseImage m).mapDerivedCategory.obj P))) :=
  derivedExtensionMate_iso_lower (systemSingleDerivedExtension BY n SY TY)
    (systemSingleDerivedExtension BX n SX TX) F.functor (F.levelInverseImage n).mapDerivedCategory
    (geometricSystemDerivedComparison SY TY SX TX F ordinary h_multiplication n)
    (F.derivedEvaluation n) rfl (systemSingleDerivedExtension BY m SY TY).derived
    (systemSingleDerivedExtension BX m SX TX).derived (F.levelInverseImage m).mapDerivedCategory
    (systemDerivedTensor SY BY h) (systemDerivedTensor SX BX h)
    (systemSingleDerivedBelow BY h SY TY) (systemSingleDerivedBelow BX h SX TX)
    (geometricSystemDerivedScalar SY SX F tensor h)
    (geometricSystemDerivedComparison SY TY SX TX F ordinary h_multiplication m)
    (geometricSystemDerivedComparison_below SY TY SX TX F ordinary tensor h_tensor_evaluation
      h_multiplication h) P

/-- Lift an already specified ordinary singleton comparison to derived categories. -/
theorem geometricSystemDerivedLift
    (F : GeometricSystemOrdinaryData BY BX u I)
    (ordinary : ∀ n : ℕ,
      systemSingleFunctor SY TY BY n ⋙ F.functor ≅
        F.levelInverseImage n ⋙ systemSingleFunctor SX TX BX n)
    (tensor : ∀ {j n : ℕ} (h : j ≤ n),
      systemTensor SY BY h ⋙ F.levelInverseImage j ≅
        F.levelInverseImage n ⋙ systemTensor SX BX h)
    (h_tensor_evaluation :
    (∀ {j n : ℕ} (h : j ≤ n) (P : systemLevel BY n),
    (F.evaluation j).hom.app ((systemSingleFunctor SY TY BY n).obj P) ≫
        (F.levelInverseImage j).map ((systemSingleBelow SY TY BY n h).hom.app P) ≫
        (tensor h).hom.app P =
      ((ordinary n).hom.app P).app j ≫
        (systemSingleBelow SX TX BX n h).hom.app ((F.levelInverseImage n).obj P)))
    (_h_tensor_generators :
    (∀ {j n : ℕ} (h : j ≤ n) (P : systemLevel BY n)
    (Z : Sheaf J (Type w))
    (b : Z ⟶ (sheafCompose J (CategoryTheory.forget CommRingCat.{w})).obj (BY.obj (op j)))
    (x : Z ⟶ (geometricSystemUnderlying BY n).obj P)
    (z : Z ⟶ (geometricSystemUnderlying BY j).obj ((systemTensor SY BY h).obj P)),
    (∀ U t, z.hom.app U t =
      systemModelTmul (SY (BY.map (homOfLE h).op)).model P U
        (b.hom.app U t) (x.hom.app U t)) →
    ∀ (W : Dᵒᵖ) (t : (u.inverse.obj Z).obj.obj W),
      ((tensor h).hom.app P).val.app W
          (((u.inverse.map z) ≫
            (I j).moduleUnderlying.inv.app ((systemTensor SY BY h).obj P)).hom.app W t) =
        systemModelTmul (SX (BX.map (homOfLE h).op)).model
          ((F.levelInverseImage n).obj P) W
          (((u.inverse.map b) ≫ (I j).ringUnderlying.hom).hom.app W t)
          (((u.inverse.map x) ≫ (I n).moduleUnderlying.inv.app P).hom.app W t)))
    (_h_above :
    (∀ (n j : ℕ) (_h : n < j) (P : systemLevel BY n),
    ((ordinary n).hom.app P).app j = 0))
    (h_multiplication :
    (∀ (n : ℕ) (P : systemLevel BY n),
    ((ordinary n).hom.app P).app n ≫
        ((systemSingleBelow SX TX BX n (Nat.le_refl n) ≪≫ TX.ordinaryUnit BX n)).hom.app
          ((F.levelInverseImage n).obj P) =
      (F.evaluation n).hom.app ((systemSingleFunctor SY TY BY n).obj P) ≫
        (F.levelInverseImage n).map
          ((systemSingleBelow SY TY BY n (Nat.le_refl n) ≪≫
            TY.ordinaryUnit BY n).hom.app P)))
    : ∃ (comparison : ∀ n : ℕ,
      (systemSingleDerivedExtension BY n SY TY).derived ⋙ F.functor.mapDerivedCategory ≅
        (F.levelInverseImage n).mapDerivedCategory ⋙
          (systemSingleDerivedExtension BX n SX TX).derived)
    (scalar : ∀ {n m : ℕ} (h : n ≤ m),
      systemDerivedTensor SY BY h ⋙ (F.levelInverseImage n).mapDerivedCategory ≅
        (F.levelInverseImage m).mapDerivedCategory ⋙ systemDerivedTensor SX BX h),
    (∀ (n : ℕ) (Q : CochainComplex (systemLevel BY n) ℤ),
    systemLevelKFlat BY n Q →
    (comparison n).hom.app (DerivedCategory.Q.obj Q) ≫
        (systemSingleDerivedExtension BX n SX TX).derived.map
          ((F.levelInverseImage n).mapDerivedCategoryFactors.hom.app Q) ≫
        (systemSingleDerivedExtension BX n SX TX).comparison.app
          (((F.levelInverseImage n).mapHomologicalComplex (.up ℤ)).obj Q) =
      F.functor.mapDerivedCategory.map
          ((systemSingleDerivedExtension BY n SY TY).comparison.app Q) ≫
        F.functor.mapDerivedCategoryFactors.hom.app
          (((systemSingleFunctor SY TY BY n).mapHomologicalComplex (.up ℤ)).obj Q) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (ordinary n) (.up ℤ)).hom.app Q)) ∧
    (∀ (n : ℕ) (P : DerivedCategory (systemLevel BY n)),
    (derivedSystemEvaluation BX n).map ((comparison n).hom.app P) ≫
        ((systemSingleDerivedBelow BX (Nat.le_refl n) SX TX ≪≫ TX.derivedUnit BX n)).hom.app
          ((F.levelInverseImage n).mapDerivedCategory.obj P) =
      (F.derivedEvaluation n).hom.app ((systemSingleDerivedExtension BY n SY TY).derived.obj P) ≫
        (F.levelInverseImage n).mapDerivedCategory.map
          ((systemSingleDerivedBelow BY (Nat.le_refl n) SY TY ≪≫
            TY.derivedUnit BY n).hom.app P)) ∧
    (∀ {n m : ℕ} (h : n ≤ m)
    (Q : CochainComplex (systemLevel BY m) ℤ), systemLevelKFlat BY m Q →
    (scalar h).hom.app (DerivedCategory.Q.obj Q) ≫
        (systemDerivedTensor SX BX h).map
          ((F.levelInverseImage m).mapDerivedCategoryFactors.hom.app Q) ≫
        (SX (BX.map (homOfLE h).op)).model.ε.app
          (((F.levelInverseImage m).mapHomologicalComplex (.up ℤ)).obj Q) =
      (F.levelInverseImage n).mapDerivedCategory.map
          ((SY (BY.map (homOfLE h).op)).model.ε.app Q) ≫
        (F.levelInverseImage n).mapDerivedCategoryFactors.hom.app
          (((systemTensor SY BY h).mapHomologicalComplex (.up ℤ)).obj Q) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (tensor h) (.up ℤ)).hom.app Q)) ∧
    (∀ {n m : ℕ} (h : n ≤ m)
    (P : DerivedCategory (systemLevel BY m)),
    F.functor.mapDerivedCategory.map
        (((systemSingleDerivedExtension BY n SY TY).adjunction.homEquiv _ _).symm
          ((systemSingleDerivedBelow BY h SY TY).inv.app P)) ≫
        (comparison m).hom.app P =
      (comparison n).hom.app ((systemDerivedTensor SY BY h).obj P) ≫
        (systemSingleDerivedExtension BX n SX TX).derived.map ((scalar h).hom.app P) ≫
        (((systemSingleDerivedExtension BX n SX TX).adjunction.homEquiv _ _).symm
          ((systemSingleDerivedBelow BX h SX TX).inv.app
            ((F.levelInverseImage m).mapDerivedCategory.obj P)))) := by
  exact ⟨geometricSystemDerivedComparison SY TY SX TX F ordinary h_multiplication,
    fun h ↦ geometricSystemDerivedScalar SY SX F tensor h,
    fun n Q _ ↦ geometricSystemDerivedComparison_rep SY TY SX TX F ordinary h_multiplication n Q,
    geometricSystemDerivedComparison_multiplication SY TY SX TX F ordinary h_multiplication,
    fun h Q _ ↦ geometricSystemDerivedScalar_rep SY SX F tensor h Q,
    geometricSystemDerivedComparison_lower SY TY SX TX F ordinary tensor h_tensor_evaluation
      h_multiplication⟩

end SheafOfModules
