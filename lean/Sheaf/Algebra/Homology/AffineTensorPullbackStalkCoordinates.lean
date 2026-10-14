/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.Algebra.Homology.AffineBaseChangeTildeCoordinates

/-! # AffineTensorPullbackStalkCoordinates

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-tensor-pullback-stalk-coordinates). -/

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

def affineTensorPullbackHomologyStalkIso
    (A A' : Type u) [CommRing A] [CommRing A'] (φ : A →+* A')
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (p : PrimeSpectrum A') (i : ℤ) :
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
    let T := ((Scheme.Modules.tensorPullback
      (Spec.map (CommRingCat.ofHom φ))).mapHomologicalComplex (.up ℤ)).obj P
    LocalizedModule p.asIdeal.primeCompl
      ((((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M).homology i) ≃+
        (RingedSpace.moduleStalkFunctor (Spec (.of A')).toRingedSpace p).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i).obj
              (DerivedCategory.Q.obj T)) := by
  let TA : ModuleCat.{u} A ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) := tilde.functor (.of A)
  let TB : ModuleCat.{u} A' ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace) := tilde.functor (.of A')
  let : TA.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : TB.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : TA.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let : TB.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let : TB.PreservesHomology := tilde_preservesHomology A'
  let f := Spec.map (CommRingCat.ofHom φ)
  let E : SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace) :=
    Scheme.Modules.tensorPullback f
  let : E.Additive := SingleComplexBaseChange.tensorPullbackAdditive.{u, w} f
  let θ : TA ⋙ E ≅ ModuleCat.extendScalars φ ⋙ TB :=
    Classical.choose (Scheme.Modules.exists_tensorPullback_tilde_iso (CommRingCat.ofHom φ))
  let P : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ :=
    (TA.mapHomologicalComplex (.up ℤ)).obj M
  let C : CochainComplex (ModuleCat.{u} A') ℤ :=
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M
  let T : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) ℤ :=
    (E.mapHomologicalComplex (.up ℤ)).obj P
  let δ : T ≅ (TB.mapHomologicalComplex (.up ℤ)).obj C :=
    (Functor.mapHomologicalComplexCompIso θ (.up ℤ)).app M
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i
  let s := RingedSpace.moduleStalkFunctor (Spec (.of A')).toRingedSpace p
  let Rs := ModuleCat.restrictScalars (StructureSheaf.toStalk A' p).hom
  let t : C.homology i →ₗ[A'] (Rs.obj (s.obj (TB.obj (C.homology i)))) :=
    StructureSheaf.toStalkₗ A' (C.homology i) p
  have : IsLocalizedModule p.asIdeal.primeCompl t :=
    inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl
      (StructureSheaf.toStalkₗ A' (C.homology i) p))
  let l : LocalizedModule p.asIdeal.primeCompl (C.homology i) ≃ₗ[A']
      (Rs.obj (s.obj (TB.obj (C.homology i)))) :=
    IsLocalizedModule.iso p.asIdeal.primeCompl t
  let d : TB.obj (C.homology i) ≅ H.obj (DerivedCategory.Q.obj T) :=
    ((C.sc i).mapHomologyIso TB).symm ≪≫
      ((DerivedCategory.homologyFunctorFactors _ i).app
        ((TB.mapHomologicalComplex (.up ℤ)).obj C)).symm ≪≫
      H.mapIso (DerivedCategory.Q.mapIso δ).symm
  exact l.toAddEquiv.trans (s.mapIso d).toLinearEquiv.toAddEquiv


/-- Affine localization identifies the base-change coordinate with the stalk map
of the inverse ordinary pullback counit.  This is the geometric localization
identity from Stacks Tag 0DJ8; the remaining supplied representative isomorphism
is handled by functoriality in the main theorem.
(blueprint: new-lem-pc-affine-tensor-pullback-stalk-coordinates-at).
Proof: expand affine localization and stalk coordinates; the adjunction triangle and
naturality of the localization germ map identify the inverse counit component. Apply
the supplied representative isomorphism by functoriality. This works for arbitrary
complexes and degrees, including zero objects. -/
theorem affineTensorPullbackHomologyStalkIso_counit_coordinate
    (A A' : Type u) [CommRing A] [CommRing A'] (φg' : A →+* A')
    (K : schemeDerivedCategory (Spec (.of A)))
    (hL : schemeDerivedQCohProperty (Spec (.of A'))
      ((derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
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
    (p : PrimeSpectrum A') :
    let L : schemeDerivedQCohCategory (Spec (.of A')) := ⟨_, hL⟩
    let b := affineBaseChangeTildeCohomologyIso A A' φg' K M e hc i
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i
    let s := RingedSpace.moduleStalkFunctor (Spec (.of A')).toRingedSpace p
    let z := fun y => s.map (H.map (inv ((SingleComplexBaseChange.counit
      (Spec.map (CommRingCat.ofHom φg'))).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P))))
      (affineTensorPullbackHomologyStalkIso A A' φg' M p i y)
    ∀ y, affineDerivedCohomologyStalkIso A' i p L
        (LocalizedModule.map p.asIdeal.primeCompl b.hom.hom y) =
      s.map (H.map ((derivedPullback (Spec.map (CommRingCat.ofHom φg'))).map e.hom))
        (z y) := by
  sorry


/-- The canonical target coordinate commutes with stalk localization.
Source: Stacks Project, Tags 01I9, 01HV and 0DJ8.
(blueprint: lem-pc-affine-tensor-pullback-stalk-coordinates).
Proof: expand the target coordinate into exact tilde homology, the termwise
pullback comparison, the inverse derived counit and e. For the sheaf isomorphism
d so obtained, the tilde/global-sections unit followed by the tilde/Gamma counit
is the identity by the adjunction triangle. Naturality of the localization germ
map identifies the localization of Gamma(d) with the stalk of tilde(Gamma(d)).
Composing with the stalk counit therefore gives the stalk of d. The first factors
of d are exactly the isomorphisms defining affineTensorPullbackHomologyStalkIso;
its final factor is the inverse derived counit followed by derived pullback of e.
Functoriality of homology and stalks gives the displayed equation. The argument
works in every degree for arbitrary complexes; zero complexes and identity maps
cause no exceptions, and zero rings have no primes. -/
theorem affineTensorPullbackHomologyStalkIso_coordinates
    (A A' : Type u) [CommRing A] [CommRing A'] (φg' : A →+* A')
    (K : schemeDerivedCategory (Spec (.of A)))
    (hL : schemeDerivedQCohProperty (Spec (.of A'))
      ((derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
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
    (p : PrimeSpectrum A') :
    let L : schemeDerivedQCohCategory (Spec (.of A')) := ⟨_, hL⟩
    let b := affineBaseChangeTildeCohomologyIso A A' φg' K M e hc i
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace)) i
    let s := RingedSpace.moduleStalkFunctor (Spec (.of A')).toRingedSpace p
    ∀ y, affineDerivedCohomologyStalkIso A' i p L
        (LocalizedModule.map p.asIdeal.primeCompl b.hom.hom y) =
      s.map (H.map (inv ((SingleComplexBaseChange.counit
        (Spec.map (CommRingCat.ofHom φg'))).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
            (derivedPullback (Spec.map (CommRingCat.ofHom φg'))).map e.hom))
        (affineTensorPullbackHomologyStalkIso A A' φg' M p i y) := by
  dsimp only
  intro y
  rw [affineTensorPullbackHomologyStalkIso_counit_coordinate A A' φg' K hL M e hc i p y]
  simp only [Functor.map_comp]
  rfl

end AlgebraicGeometry
