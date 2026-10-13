/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-! # AffineBaseChangeTildeMateFactorization

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-base-change-tilde-mate-factorization). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The actual tilde representative of affine derived pullback.
Source: Stacks Project, Tags 01I9 and 08DW.
(blueprint: lem-pc-affine-base-change-tilde-mate-factorization).
The tensor-pullback comparison is unit-normalized. The other two factors are
respectively the inverse of the supplied derived counit and the image of e. -/
def affineBaseChangeTildeRepresentativeIso
    (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A')
    (K : schemeDerivedCategory (Spec (.of A)))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (e : DerivedCategory.Q.obj
      (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φ))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((affineTildeFunctor A).mapHomologicalComplex (.up ℤ)).obj M)))) :
    DerivedCategory.Q.obj (((affineTildeFunctor A').mapHomologicalComplex (.up ℤ)).obj
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M)) ≅
      (derivedPullback (Spec.map (CommRingCat.ofHom φ))).obj K := by
  let TA := affineTildeFunctor A
  let TB := affineTildeFunctor A'
  let : TA.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : TB.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let f := Spec.map (CommRingCat.ofHom φ)
  let P := (TA.mapHomologicalComplex (.up ℤ)).obj M
  let C := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
  let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace) :=
    Scheme.Modules.tensorPullback f
  let : E.Additive := SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f
  let : IsIso ((SingleComplexBaseChange.counit f).app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := hc
  let θ := Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso
    (CommRingCat.ofHom φ))
  let θ' : TA ⋙ E ≅ ModuleCat.extendScalars φ ⋙ TB := θ
  let δ : (E.mapHomologicalComplex (.up ℤ)).obj P ≅
      (TB.mapHomologicalComplex (.up ℤ)).obj C :=
    (Functor.mapHomologicalComplexCompIso θ' (.up ℤ)).app M
  exact (DerivedCategory.Q.mapIso δ).symm ≪≫
    (asIso ((SingleComplexBaseChange.counit f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))).symm ≪≫
    (derivedPullback f).mapIso e

/-- The source tensor model transports the affine derived mate to the ordinary
coefficient map followed by the actual right-derived pushforward unit. This
contains no natural presentation of target cohomology and no global sections.
Source: Stacks Project, perfect.tex, Tag 0DJ8, affine proof and equation-bc;
more-algebra.tex, Tag 06Y6; cohomology.tex, Tag 08HY, derived mate construction.
(blueprint: lem-pc-affine-base-change-tilde-mate-factorization).

Proof: Resolve the restriction of M to R by a flat K-flat complex P. The universal
left-derived scalar extension and the counit in m identify its value with scalar
extension of P to R'. Exact tilde and the affine pullback tensor formula identify
this derived object with Lg* of the affine pushforward of Q(tilde M). The affine
acyclic pushforward calculation identifies the latter with Rf*K, using e. Take
cohomology and compose with m.cohomologyIso to obtain eC. Apply the pinned derived
base-change unit compatibility on the common K-flat span. The unit-normalized
tensor-pullback comparison identifies its ordinary exchange with the augmentation
followed termwise by the coefficient map from A tensor R' to A'. Apply homology:
m.comparison_eq supplies the augmentation factor, and exact restriction of scalars
supplies the mapHomologyIso factor in cE. The natural comparison for consecutive
restriction of scalars is rho; it is identity on carriers, so transporting through
hphi_f introduces exactly rho.inv. Transport the extended complex through hphi_g.
The remaining arrow is the termwise tilde/pushforward comparison followed by the
right-derived unit, which is the explicitly constructed cohomology map. Finally,
the inverse pullback counit and e identify its target with Lg'*K. Naturality and
cancellation of this counit yield the displayed factorization. The coefficient
map need not be invertible, and the square need only commute. P may be unbounded;
zero rings and zero complexes are included. -/
theorem exists_affineBaseChangeTildeMateFactorization
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra (A ⊗[R] R') A']
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R')]
    (φg' : A →+* A') (φf' : R' →+* A')
    (hφg' : (algebraMap (A ⊗[R] R') A').comp
      (algebraMap A (A ⊗[R] R')) = φg')
    (hφf' : (algebraMap (A ⊗[R] R') A').comp
      Algebra.TensorProduct.includeRight.toRingHom = φf')
    (hw : Spec.map (CommRingCat.ofHom φg') ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom φf') ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (K : schemeDerivedCategory (Spec (.of A)))
    (hK : schemeDerivedQCohProperty (Spec (.of A)) K)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat M)
    (e : DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)))) (i : ℤ)
 :
    let m := ModuleCat.baseDerivedTensorCohomologyModel R A R' M A'
    let α := algebraMap (A ⊗[R] R') A'
    let j : R' →+* A ⊗[R] R' := Algebra.TensorProduct.includeRight.toRingHom
    let T := tilde.functor (.of R')
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i
    let C := (((ModuleCat.extendScalars (α.comp
      (algebraMap A (A ⊗[R] R')))).mapHomologicalComplex (.up ℤ)).obj M)
    let Cg := ((ModuleCat.extendScalars φg').mapHomologicalComplex (.up ℤ)).obj M
    let cE := m.comparison i ≫ HomologicalComplex.homologyMap m.ordinaryToLocalized i ≫
      ((C.sc i).mapHomologyIso (ModuleCat.restrictScalars α)).hom
    let ρ := ModuleCat.restrictScalarsComp' j α φf' hφf'.symm
    let s := (ModuleCat.restrictScalars j).map cE ≫ ρ.inv.app (C.homology i)
    let z₀ := (HomologicalComplex.homologyFunctor (ModuleCat.{u} A') (.up ℤ) i).map
      (eqToHom (by dsimp only [C, α]; rw [hφg'] : C = Cg))
    let t := affineBaseChangeTildeRepresentativeIso A A' φg' K M e hc
    ∃ eC : T.obj ((ModuleCat.restrictScalars j).obj (m.cohomology i)) ≅
        H.obj ((derivedPullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).obj
          ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj K)),
      eC.hom ≫ H.map (schemeDerivedBaseChangeMap
        (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom φf'))
        (Spec.map (CommRingCat.ofHom (algebraMap R R')))
        (Spec.map (CommRingCat.ofHom φg')) hw K) =
      T.map s ≫ T.map ((ModuleCat.restrictScalars φf').map z₀) ≫
        affineTildePushforwardCohomologyMap A' R' φf' Cg i ≫
        H.map ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf'))).map t.hom)
    := by sorry

end AlgebraicGeometry
