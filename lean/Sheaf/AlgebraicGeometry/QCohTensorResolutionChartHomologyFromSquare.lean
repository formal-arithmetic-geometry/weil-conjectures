module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartHomologyFormula
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartHomologySquare
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartExtendedHomology
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionHomologyNaturality
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionExtendedCoordinates
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionPasteHomology

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
set_option cleanup.letToHave false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance trChartHomologySquareMonoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance trChartHomologySquareZero
    (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance trChartHomologySquareObjZero
    (X : Scheme.{u}) (L : X.Modules) :
    ((curriedTensor X.Modules).obj L).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf L

/-- Naturality of chart homology follows from the tensor-model chain square. -/
noncomputable def tensorResolutionChartHomologyIso_formula_naturality_of_square
    (Y : Scheme.{u}) (N : Y.Modules) [N.IsQuasicoherent]
    (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (MB NB : ModuleCat.{u} (Γ(Y, V.1) : Type u))
    (sA : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (sB : NB ≃ₗ[Γ(Y, V.1)] N.val.obj (op V.1))
    (PA : ProjectiveResolution MA) (PB : ProjectiveResolution MB)
    (n : ℕ) :
    let φ := Y.presheaf.map (homOfLE h).op
    let R := Scheme.Modules.restrictFunctor (Spec.map φ)
    let RC := R.mapHomologicalComplex (.up ℤ)
    let LA := ((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj PA.complex
    let LB := ((tensorRight NB).mapHomologicalComplex (.down ℕ)).obj PB.complex
    let EA := tensorResolutionChartComplex U MA PA
    let EB := tensorResolutionChartComplex V MB PB
    let N0 := (CochainComplex.singleFunctor Y.Modules 0).obj N
    let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let RV := (Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)
    ∀ (k : LA ⟶ ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex (.down ℕ)).obj LB)
      (l : RC.obj (CochainComplex.mapBifunctor EA (RU.obj N0)
        (curriedTensor (Spec Γ(Y, U.1)).Modules)) ⟶
        CochainComplex.mapBifunctor EB (RV.obj N0)
          (curriedTensor (Spec Γ(Y, V.1)).Modules)),
      (let k' := tensorResolutionSemilinearComplexMap φ (.up ℤ)
          (LA.extend ComplexShape.embeddingDownNat)
          (LB.extend ComplexShape.embeddingDownNat)
          (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat LA LB k)
       RC.map (tensorResolutionChartTensorIso N U MA NA sA PA).hom ≫ l =
         k' ≫ (tensorResolutionChartTensorIso N V MB NB sB PB).hom) →
      let t := HomologicalComplex.homologyMap k n ≫
        ((LB.sc n).mapHomologyIso (ModuleCat.restrictScalars φ.hom)).hom
      letI : (tilde.functor Γ(Y, U.1)).PreservesHomology :=
        tilde_preservesHomology (Γ(Y, U.1) : Type u)
      letI : (tilde.functor Γ(Y, V.1)).PreservesHomology :=
        tilde_preservesHomology (Γ(Y, V.1) : Type u)
      let dA := tensorResolutionExtendLeftHomologyData ComplexShape.embeddingDownNat
        LA (i := n) (i' := ComplexShape.embeddingDownNat.f n) rfl (LA.sc n).homologyData.left
      let dB := tensorResolutionExtendLeftHomologyData ComplexShape.embeddingDownNat
        LB (i := n) (i' := ComplexShape.embeddingDownNat.f n) rfl (LB.sc n).homologyData.left
      R.map (dA.map (tilde.functor Γ(Y, U.1))).homologyIso.inv ≫
        R.map (HomologicalComplex.homologyMap
          (tensorResolutionChartTensorIso N U MA NA sA PA).hom (-(n : ℤ))) ≫
          (((CochainComplex.mapBifunctor EA (RU.obj N0)
            (curriedTensor (Spec Γ(Y, U.1)).Modules)).sc (-(n : ℤ))).mapHomologyIso R).inv ≫
          HomologicalComplex.homologyMap l (-(n : ℤ)) =
        tensorResolutionSemilinearMap φ t ≫
          (dB.map (tilde.functor Γ(Y, V.1))).homologyIso.inv ≫
          HomologicalComplex.homologyMap
            (tensorResolutionChartTensorIso N V MB NB sB PB).hom (-(n : ℤ)) := by
  dsimp only
  intro k l hl
  have h₁ := tensorResolutionChartTensor_homology_square
    Y N V U h MA NA MB NB sA sB PA PB n k l hl
  have h₂ := tensorResolutionChartExtendedHomology_naturality
    Y V U h MA NA MB NB PA PB k n
  letI : (tilde.functor Γ(Y, U.1)).PreservesHomology :=
    tilde_preservesHomology (Γ(Y, U.1) : Type u)
  letI : (tilde.functor Γ(Y, V.1)).PreservesHomology :=
    tilde_preservesHomology (Γ(Y, V.1) : Type u)
  erw [h₁]
  simpa only [Category.assoc] using
    congrArg (fun a ↦ a ≫ HomologicalComplex.homologyMap
      (tensorResolutionChartTensorIso N V MB NB sB PB).hom (-(n : ℤ))) h₂

end AlgebraicGeometry
