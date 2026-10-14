/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.AffineSpectrumCanonicalStalkRingCoordinates
public import Sheaf.AlgebraicGeometry.IsoPullbackStalkCohomology
public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso
public import Sheaf.AlgebraicGeometry.AffineSpectrumCanonicalStalkComplexIso
/-! # The canonical affine-spectrum comparison on coefficient-one tensors -/

@[expose] public section

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

/-- The coefficient-one comparison for the canonical input chain coordinates.
Proof: represent x by the germ of a section s of P.X k. The original tensor-stalk
comparison takes 1 tensor x to the germ of the pullback adjunction unit on s.
The additive comparison along j takes this to the germ of its pullback along j:
this follows from restriction-stalk compatibility and adjunction uniqueness.
The inverse of alpha is the mate of the pushforward composition isomorphism.
The composite-adjunction unit identity therefore identifies this successive
pullback-unit germ with the germ obtained by pulling s first along X.isoSpec.inv
and then along Spec.map g'.appTop. By definition, the extension/restriction unit
sends x to 1 tensor x; applying the inverse pullback-stalk comparison yields
canonicalSpectrumStalkComplexIso.hom(x). The spectrum tensor-stalk comparison
sends 1 tensor this element to precisely the preceding germ. Cancel that last
comparison to obtain the asserted coefficient-one equation. Stalk elements all
have section-germ representatives, so this establishes the equation for all x.
The mapHomologicalComplex composition isomorphisms have identity components and
do not alter this calculation. Zero modules and empty spectra cause no exception.
Source: Stacks Project, Tags 0098, 0096, and 0DJ8.
(blueprint: lem-pc-affine-spectrum-canonical-tensor-comparison-one). -/
theorem canonicalSpectrum_tensor_comparison_one
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
    let q : Q ≅ ((ModuleCat.restrictScalars.{u} eA.toRingHom).mapHomologicalComplex
      (.up ℤ)).obj Q0 :=
      canonicalSpectrumStalkComplexIso X (g' z) ((Spec.map g'.appTop) z0) hA P
    (∀ (k : ℤ) (x : Q.X k),
        H.hom.f k ((1 : C z) ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
          (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] x) =
        (1 : C z0) ⊗ₜ[A0, (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
          (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).comp
          (algebraMap A0 (A0 ⊗[R0] B0))] (show Q0.X k from q.hom.f k x)) := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
