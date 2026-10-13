/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.IsoPullbackStalkCohomology
public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso
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

/-- The canonical additive pullback-stalk comparison on ordinary complexes.
Source: Stacks Project, Tag 0098, stalk pullback formula.
(blueprint: lem-pc-affine-spectrum-tensor-coherent-coordinate-data). -/
def ordinaryIsoPullbackStalkComplexIso {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j]
    (y : Y)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ) :=
  letI : (Scheme.Modules.tensorPullback j).Additive := tensorPullbackAdditive j
  letI : (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).Additive :=
    comparisonStalkAdditive Y y
  let E := Scheme.Modules.tensorPullback j
  let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace y ⋙
    forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
  let SZ := RingedSpace.moduleStalkFunctor Z.toRingedSpace (j y)
  let F := forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u}
  let F0 := forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
  (Functor.mapHomologicalComplexCompIso (Iso.refl (SZ ⋙ F)) (.up ℤ)).app P ≪≫
    (NatIso.mapHomologicalComplex (isoPullbackAdditiveStalkIso j y) (.up ℤ)).app P ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ S)) (.up ℤ)).symm.app P ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (RingedSpace.moduleStalkFunctor Y.toRingedSpace y ⋙ F0))
      (.up ℤ)).symm.app ((E.mapHomologicalComplex (.up ℤ)).obj P)

/-- Canonical affine coordinates with chain-level pullback-stalk coherence.
Source: Stacks Project, Tag 0098 (stalk pullback formula), Tag 0096 (adjunction),
and Tag 0DJ8 (affine reduction).
(blueprint: lem-pc-affine-spectrum-tensor-coherent-coordinate-data).
Proof: take the stalk ring isomorphisms induced by the four isoSpec maps; naturality
of isoSpec and functoriality of stalk maps give the three ring equations. Take q
from the pullback-stalk comparison along X.isoSpec.inv, including the point equality
from isoSpec naturality. Define t termwise by d tensor x mapping to eD(d) tensor q(x).
The ring equations make this balanced and eD-linear; the inverse uses the inverse
ring and stalk isomorphisms. Naturality of the stalk comparison in the differential
makes t a chain isomorphism. To prove the chain coherence, use tensor induction in
each degree. On d tensor x both composites are the germ d times the pullback germ
of x. The adjunction mate defining the pullback composition isomorphism identifies
these germs. The restriction-stalk comparison identifies their additive images.
Thus they agree in each degree, and chain-map extensionality proves the equation.
This construction applies to zero complexes and all stalk rings, without flatness. -/
theorem exists_affineSpectrum_tensor_coherent_coordinate_data
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (z0 : Spec Γ(X', ⊤)) (i : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
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
    let D0 := C z0
    let Q := stalkComplex g' z P
    let Q0 := stalkComplex (Spec.map g'.appTop) z0 P0
    let V0 := tensorComplex (Spec.map f.appTop) (Spec.map f'.appTop)
      (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0
    ∃ (eR : R f g' z ≃+* R0) (eA : A g' z ≃+* A0)
      (eB : B f' z ≃+* B0) (eD : C z ≃+* D0)
      (q : Q ≅ ((ModuleCat.restrictScalars.{u} eA.toRingHom).mapHomologicalComplex
        (.up ℤ)).obj Q0)
      (t : tensorComplex f f' g g' sq z P ≅
        ((ModuleCat.restrictScalars.{u} eD.toRingHom).mapHomologicalComplex
          (.up ℤ)).obj V0),
      (∀ r : R f g' z,
        eA (algebraMap (R f g' z) (A g' z) r) = algebraMap R0 A0 (eR r)) ∧
      (∀ r : R f g' z,
        eB (algebraMap (R f g' z) (B f' z) r) = algebraMap R0 B0 (eR r)) ∧
      (∀ (a : A g' z) (b : B f' z),
        eD (algebraMap (A g' z ⊗[R f g' z] B f' z) (C z) (a ⊗ₜ[R f g' z] b)) =
          algebraMap (A0 ⊗[R0] B0) D0 (eA a ⊗ₜ[R0] eB b)) ∧
      (∀ (k : ℤ) (d : C z) (x : Q.X k),
        t.hom.f k (d ⊗ₜ[A g' z, (tensorMap f f' g g' sq z).comp
          (algebraMap (A g' z) (A g' z ⊗[R f g' z] B f' z))] x) =
        eD d ⊗ₜ[A0, (tensorMap (Spec.map f.appTop) (Spec.map f'.appTop)
          (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0).comp
          (algebraMap A0 (A0 ⊗[R0] B0))] (show Q0.X k from q.hom.f k x)) ∧
      (F.mapHomologicalComplex (.up ℤ)).map t.hom ≫
          (Functor.mapHomologicalComplexCompIso
            (Iso.refl (ModuleCat.restrictScalars.{u} eD.toRingHom ⋙ F)) (.up ℤ)).hom.app V0 ≫
          (F0.mapHomologicalComplex (.up ℤ)).map
            (tensorStalkIso (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0).hom =
        (F.mapHomologicalComplex (.up ℤ)).map
            (tensorStalkIso f f' g g' sq z P).hom ≫
          (ordinaryIsoPullbackStalkComplexIso j z0 Pg).hom ≫
          (F0.mapHomologicalComplex (.up ℤ)).map
            ((S0.mapHomologicalComplex (.up ℤ)).map alpha.inv) := by sorry


end AlgebraicGeometry.SingleComplexBaseChange
