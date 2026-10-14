/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.AffineSpectrumCanonicalStalkRingCoordinates
public import Sheaf.AlgebraicGeometry.IsoPullbackStalkCohomology
public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
@[expose] public section

/-! Existence of canonical spectrum chain coordinates -/ 
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry.SingleComplexBaseChange
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
set_option linter.unusedVariables false in
/-- Strict intermediate obligation for the affine-spectrum tensor generator argument.
Proof: construct the transported stalk chain isomorphism from the canonical affine stalk
comparison and extension/restriction along the invertible stalk map; the fixed-q version
then follows by the section-germ calculation for the tensor pullback comparisons.
Source: Stacks Project, Tags 0098, 0096, and 0DJ8.
(blueprint: lem-pc-affine-spectrum-canonical-tensor-generator-formula-q). -/
theorem exists_canonicalSpectrum_tensor_generator_formula_q
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤))
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let z := X'.isoSpec.inv z0
    let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj P
    letI := leftAlgebra f g' z
    letI := rightAlgebra f f' g g' sq z
    letI := (tensorMap f f' g g' sq z).toAlgebra
    letI := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
    letI := leftAlgebra (Spec.map f.appTop) (Spec.map g'.appTop) z0
    letI := rightAlgebra (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0
    letI := (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).toAlgebra
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} (R (Spec.map f.appTop) (Spec.map g'.appTop) z0))
    letI := HasDerivedCategory.standard (ModuleCat.{u} (B (Spec.map f'.appTop) z0))
    let R0 := R (Spec.map f.appTop) (Spec.map g'.appTop) z0
    let A0 := A (Spec.map g'.appTop) z0
    let B0 := B (Spec.map f'.appTop) z0
    let Q := stalkComplex g' z P
    let Q0 := stalkComplex (Spec.map g'.appTop) z0 P0
    let H :=
      let z := X'.isoSpec.inv z0
      let P0 := ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
        (.up ℤ)).obj P
      let Pg := ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P
      let j := X'.isoSpec.inv
      let S0 := RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0
      let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
      let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
        AddCommGrpCat.{u}
      let alpha := (NatIso.mapHomologicalComplex
        ((Scheme.Modules.tensorPullbackCompositionIso (Spec.map g'.appTop) X.isoSpec.inv
          ((Spec.map g'.appTop) ≫ X.isoSpec.inv) rfl).symm ≪≫
        Scheme.Modules.tensorPullbackCompositionIso j g'
          ((Spec.map g'.appTop) ≫ X.isoSpec.inv) (Scheme.isoSpec_inv_naturality g').symm)
        (.up ℤ)).app P
      let U :=
        letI : (Scheme.Modules.tensorPullback j).Additive := tensorPullbackAdditive j
        letI : (RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0).Additive :=
          comparisonStalkAdditive (Spec Γ(X', ⊤)) z0
        let E := Scheme.Modules.tensorPullback j
        let S := RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0 ⋙
          forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0)) AddCommGrpCat.{u}
        let SZ := RingedSpace.moduleStalkFunctor X'.toRingedSpace (j z0)
        let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk (j z0))) AddCommGrpCat.{u}
        let F0 := forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0)) AddCommGrpCat.{u}
        (Functor.mapHomologicalComplexCompIso (Iso.refl (SZ ⋙ F)) (.up ℤ)).app Pg ≪≫
          (NatIso.mapHomologicalComplex (isoPullbackAdditiveStalkIso j z0) (.up ℤ)).app Pg ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ S)) (.up ℤ)).symm.app Pg ≪≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (RingedSpace.moduleStalkFunctor (Spec Γ(X', ⊤)).toRingedSpace z0 ⋙ F0))
            (.up ℤ)).symm.app ((E.mapHomologicalComplex (.up ℤ)).obj Pg)
      let H := (F.mapHomologicalComplex (.up ℤ)).mapIso
          (tensorStalkIso f f' g g' sq z P) ≪≫ U ≪≫
        (F0.mapHomologicalComplex (.up ℤ)).mapIso
          ((S0.mapHomologicalComplex (.up ℤ)).mapIso alpha.symm) ≪≫
        (F0.mapHomologicalComplex (.up ℤ)).mapIso
          (tensorStalkIso (Spec.map f.appTop) (Spec.map f'.appTop)
            (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0).symm
      H
    let hA : g' z = X.isoSpec.inv ((Spec.map g'.appTop) z0) :=
      (congrArg (fun k : Spec Γ(X', ⊤) ⟶ X ↦ k z0)
        (Scheme.isoSpec_inv_naturality g')).symm
    let eA := canonicalSpectrumStalkEquiv X (g' z) ((Spec.map g'.appTop) z0) hA
    let eD := canonicalSpectrumStalkEquiv X' z z0 rfl
    ∃ q : Q ≅ ((ModuleCat.restrictScalars.{u} eA.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj Q0, True := by
  dsimp only
  have transport
      {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j] (y : Y)
      (P : CochainComplex Z.Modules ℤ) :
      Nonempty
        ((((RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y)).mapHomologicalComplex
          (.up ℤ)).obj P) ≅
        ((ModuleCat.restrictScalars (j.stalkMap y).hom).mapHomologicalComplex (.up ℤ)).obj
          (((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).mapHomologicalComplex
            (.up ℤ)).obj
            (((Scheme.Modules.tensorPullback j).mapHomologicalComplex (.up ℤ)).obj P))) := by
    let ρ := (j.stalkMap y).hom
    let eρ := RingEquiv.ofBijective ρ
      (ConcreteCategory.bijective_of_isIso (j.stalkMap y))
    have : (ModuleCat.restrictScalars.{u} ρ).IsEquivalence :=
      ModuleCat.restrictScalars_isEquivalence_of_ringEquiv eρ
    let E := ModuleCat.extendScalars.{u} ρ
    let U := ModuleCat.restrictScalars.{u} ρ
    let S := RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y)
    let T := Scheme.Modules.tensorPullback j ⋙ RingedSpace.moduleStalkFunctor Y.toRingedSpace y
    have : E.IsEquivalence :=
      (ModuleCat.extendRestrictScalarsAdj ρ).isEquivalence_left_of_isEquivalence_right
    let e := Classical.choose (Scheme.Modules.exists_tensorPullback_stalk_iso j y)
    let b : S ≅ T ⋙ U :=
      (Functor.rightUnitor S).symm ≪≫
        Functor.isoWhiskerLeft S (asIso (ModuleCat.extendRestrictScalarsAdj ρ).unit) ≪≫
        (Functor.associator S E U).symm ≪≫ Functor.isoWhiskerRight e.symm U
    have : (Scheme.Modules.tensorPullback j).Additive := tensorPullbackAdditive.{u, w} j
    have : (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).Additive :=
      comparisonStalkAdditive Y y
    have : T.Additive := by dsimp [T]; infer_instance
    have hT : T.PreservesZeroMorphisms := by
      dsimp [T]
      have hp : (Scheme.Modules.tensorPullback j).PreservesZeroMorphisms := inferInstance
      have hs : (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).PreservesZeroMorphisms :=
        inferInstance
      infer_instance
    have hU : U.PreservesZeroMorphisms := by dsimp [U]; infer_instance
    have hTU : (T ⋙ U).PreservesZeroMorphisms := inferInstance
    let q := (NatIso.mapHomologicalComplex b (.up ℤ)).app P
    exact ⟨q ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ U)) (.up ℤ)).app P ≪≫
      ((U.mapHomologicalComplex (.up ℤ)).mapIso
        ((Functor.mapHomologicalComplexCompIso (Iso.refl T) (.up ℤ)).app P))⟩
  let z := X'.isoSpec.inv z0
  let y := (Spec.map g'.appTop) z0
  have hA : g' z = X.isoSpec.inv y :=
    (congrArg (fun k : Spec Γ(X', ⊤) ⟶ X ↦ k z0)
      (Scheme.isoSpec_inv_naturality g')).symm
  have canonical (x : X) (h : x = X.isoSpec.inv y) :
      Nonempty
        ((((RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
          (.up ℤ)).obj P) ≅
        ((ModuleCat.restrictScalars
          (canonicalSpectrumStalkEquiv X x y h).toRingHom).mapHomologicalComplex
          (.up ℤ)).obj
          (((RingedSpace.moduleStalkFunctor
            (Spec Γ(X, ⊤)).toRingedSpace y).mapHomologicalComplex (.up ℤ)).obj
            (((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
              (.up ℤ)).obj P))) := by
    subst x
    simpa only [canonicalSpectrumStalkEquiv, eqToIso_refl, Iso.refl_trans,
      RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom, asIso_hom] using
      transport X.isoSpec.inv y P
  obtain ⟨q⟩ := canonical (g' z) hA
  exact ⟨q, trivial⟩
end AlgebraicGeometry.SingleComplexBaseChange
