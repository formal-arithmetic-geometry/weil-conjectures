/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.IsoPullbackStalkCohomology
public import Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso

/-! # Affine coordinate transport of the localized tensor comparison

Source: Stacks Project, Tag 0DJ8, equation-bc and affine reduction; Tag 0098.
(blueprint: lem-pc-affine-spectrum-tensor-coordinate-transport).
-/

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

/-- Ordinary pullback transports additive stalk homology along an isomorphism.
This is constructed from the restriction-stalk isomorphism on complexes and exact
stalk homology factors; it uses no derived pullback or derived pullback counit.
Source: Stacks Project, Tag 0098, lemma-stalk-pullback-modules.
(blueprint: lem-pc-affine-spectrum-tensor-coordinate-transport). -/
def ordinaryIsoPullbackStalkHomologyIso {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsIso j]
    (y : Y) (i : ℤ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) ℤ) :=
  letI : (Scheme.Modules.tensorPullback j).Additive := tensorPullbackAdditive j
  letI : (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).Additive :=
    comparisonStalkAdditive Y y
  let E := Scheme.Modules.tensorPullback j
  let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace y ⋙
    forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℤ) i
  let F := forget₂ (ModuleCat.{u} (Z.presheaf.stalk (j y))) AddCommGrpCat.{u}
  let F0 := forget₂ (ModuleCat.{u} (Y.presheaf.stalk y)) AddCommGrpCat.{u}
  F.mapIso (comparisonStalkHomologyIso Z (j y) P i).symm ≪≫
    (additiveStalkCohomologyFactors Z (j y) i).app P ≪≫
    H.mapIso ((NatIso.mapHomologicalComplex (isoPullbackAdditiveStalkIso j y)
      (.up ℤ)).app P) ≪≫
    H.mapIso ((Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ S))
      (.up ℤ)).symm.app P) ≪≫
    (additiveStalkCohomologyFactors Y y i).symm.app
      ((E.mapHomologicalComplex (.up ℤ)).obj P) ≪≫
    F0.mapIso (comparisonStalkHomologyIso Y y
      ((E.mapHomologicalComplex (.up ℤ)).obj P) i)

/-- Affine spectrum coordinates identify the input stalk complex and the ordinary
localized tensor complex, compatibly with the ordinary pullback stalk map.
This statement is purely about rings and ordinary complexes, not derived tensor
cohomology or its comparison counit.

Proof: apply isoSpec naturality at each vertex. The stalk maps of the four
isomorphisms, with stalkCongr for the equal points, give eR, eA, eB and eD.
Their inverses are the stalk maps of the inverse scheme isomorphisms, so these
are ring equivalences. stalkMap_comp and stalkMap_congr_hom give hA and hB.
The two restrictions of tensorMap then give hD on pure tensors. The pullback-stalk
germ isomorphism of Tag 0098 for the isomorphism X.isoSpec.inv gives q; it is
linear after restriction along eA and commutes with differentials by naturality.
Define t degreewise on pure tensors by d tensor x mapping to eD(d) tensor q(x).
The structural-map equations make this balanced and semilinear, hence linear
into restriction along eD. The inverse uses the inverse ring equivalences and
q.inv; their composites are identity by tensor induction. Naturality of q for
differentials makes t a chain isomorphism. The germ formula for tensorStalkIso
and the adjunction-mate formula for alpha identify the induced additive stalk
chain map with isoPullbackAdditiveStalkIso followed by the stalk of alpha.inv.
Apply homology and the exact restriction mapHomologyIso, using the exact
stalk factors in ordinaryIsoPullbackStalkHomologyIso, to obtain the final equation.
No derived tensor model is used. Zero complexes satisfy the same tensor formulas;
on an empty spectrum the point hypothesis has no instances.
Source: Stacks Project, Tag 0098, lemma-stalk-pullback-modules; Tag 0096,
pullback adjunction; Tag 0DJ8, affine reduction of equation-bc.
(blueprint: lem-pc-affine-spectrum-tensor-coordinate-transport). -/
theorem exists_affineSpectrum_tensor_coordinates
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
      F.map (HomologicalComplex.homologyMap t.hom i) ≫
          F.map ((V0.sc i).mapHomologyIso (ModuleCat.restrictScalars.{u} eD.toRingHom)).hom ≫
          F0.map (HomologicalComplex.homologyMap
            (tensorStalkIso (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) sq0 z0 P0).hom i) =
        F.map (HomologicalComplex.homologyMap (tensorStalkIso f f' g g' sq z P).hom i) ≫
          (ordinaryIsoPullbackStalkHomologyIso j z0 i Pg).hom ≫
          F0.map (HomologicalComplex.homologyMap
            ((S0.mapHomologicalComplex (.up ℤ)).map alpha.inv) i) := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
