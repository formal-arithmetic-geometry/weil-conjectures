/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.Algebra.Homology.AffineTensorPullbackStalkCoordinates

/-! # AffineOrdinaryTensorStalkCoordinates

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-ordinary-tensor-stalk-coordinates). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Localization of ordinary cohomology into the stalk complex of its tilde.
Source: Stacks Project, Tags 01I9 and 01AG.
(blueprint: lem-pc-affine-ordinary-tensor-stalk-coordinates).
Constructed from the tilde stalk localization, exact tilde homology and exact stalks. -/
def affineTildeHomologyLocalization
    (D : Type u) [CommRing D] (C : CochainComplex (ModuleCat.{u} D) ℤ)
    (p : PrimeSpectrum D) (i : ℤ) :
    let TB : ModuleCat.{u} D ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) :=
      tilde.functor (.of D)
    letI : TB.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
    let N := (TB.mapHomologicalComplex (.up ℤ)).obj C
    let s := RingedSpace.moduleStalkFunctor (Spec (.of D)).toRingedSpace p
    LocalizedModule p.asIdeal.primeCompl (C.homology i) ≃+
      ((s.mapHomologicalComplex (.up ℤ)).obj N).homology i := by
  let TB : ModuleCat.{u} D ⥤
      SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace) := tilde.functor (.of D)
  let : TB.Additive := instAdditiveModuleCatCarrierModulesSpecOfFunctor
  let : TB.PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let : TB.PreservesHomology := tilde_preservesHomology D
  let N := (TB.mapHomologicalComplex (.up ℤ)).obj C
  let s := RingedSpace.moduleStalkFunctor (Spec (.of D)).toRingedSpace p
  let Rs := ModuleCat.restrictScalars (StructureSheaf.toStalk D p).hom
  let t : C.homology i →ₗ[D] (Rs.obj (s.obj (TB.obj (C.homology i)))) :=
    StructureSheaf.toStalkₗ D (C.homology i) p
  have : IsLocalizedModule p.asIdeal.primeCompl t :=
    inferInstanceAs (IsLocalizedModule p.asIdeal.primeCompl
      (StructureSheaf.toStalkₗ D (C.homology i) p))
  let l := IsLocalizedModule.iso p.asIdeal.primeCompl t
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of D)).toRingedSpace)) i
  let d : TB.obj (C.homology i) ≅ H.obj (DerivedCategory.Q.obj N) :=
    ((C.sc i).mapHomologyIso TB).symm ≪≫
      ((DerivedCategory.homologyFunctorFactors _ i).app N).symm
  exact l.toAddEquiv.trans ((s.mapIso d).toLinearEquiv.toAddEquiv.trans
    (affineRepresentativeStalkIso (Spec (.of D)) p N i).toLinearEquiv.toAddEquiv)

/-- The ordinary tensor target has canonical stalk-complex coordinates.
Source: Stacks Project, Tags 01I9, 01HV, 01AG and 0DJ8.
(blueprint: lem-pc-affine-ordinary-tensor-stalk-coordinates).

Proof: exact tilde homology and exact stalks give affineTildeHomologyLocalization.
The tensor-pullback/tilde natural isomorphism identifies T with tilde C. Take its
inverse on stalk complexes and compose with the inverse tensorStalkIso to obtain
τ. The unit equation of the tilde comparison and the pure-tensor equation of the
pullback-stalk comparison show its displayed action on germs. Germs of pure tensors
generate the localized modules, so these equations determine τ in each degree.
Naturality of exact stalk homology, followed by the homologyFunctorFactors equation,
identifies the resulting cohomology composite with the three factors in the
constructed affineTensorPullbackHomologyStalkIso. This gives the second equation.
The construction uses no derived source comparison or K-flatness and works for
zero complexes and identity maps; zero rings have no primes. -/
theorem exists_affineOrdinaryTensorStalkCoordinates
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra (A ⊗[R] R') A']
    (φg' : A →+* A') (φf' : R' →+* A')
    (hφg' : (algebraMap (A ⊗[R] R') A').comp
      (algebraMap A (A ⊗[R] R')) = φg')
    (hφf' : (algebraMap (A ⊗[R] R') A').comp
      Algebra.TensorProduct.includeRight.toRingHom = φf')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ) :
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
    let T := ((Scheme.Modules.tensorPullback
      (Spec.map (CommRingCat.ofHom φg'))).mapHomologicalComplex (.up ℤ)).obj P
    let C := ((ModuleCat.extendScalars φg').mapHomologicalComplex (.up ℤ)).obj M
    (p : PrimeSpectrum A') →
      let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
      let f' := Spec.map (CommRingCat.ofHom φf')
      let g := Spec.map (CommRingCat.ofHom (algebraMap R R'))
      let g' := Spec.map (CommRingCat.ofHom φg')
      letI := SingleComplexBaseChange.leftAlgebra f g' p
      letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
      letI := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
      let N := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A' ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A')).toRingedSpace))
            (tilde.functor (.of A'))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj C)
      let s := RingedSpace.moduleStalkFunctor (Spec (.of A')).toRingedSpace p
      let ρ := (SingleComplexBaseChange.tensorMap f f' g g' sq p).comp
        (algebraMap (SingleComplexBaseChange.A g' p)
          (SingleComplexBaseChange.A g' p ⊗[SingleComplexBaseChange.R f g' p]
            SingleComplexBaseChange.B f' p))
      ∃ τ : (s.mapHomologicalComplex (.up ℤ)).obj N ≅
          SingleComplexBaseChange.tensorComplex f f' g g' sq p P,
        (∀ (j : ℤ) (x : M.X j),
          τ.hom.f j (TopCat.Presheaf.germ (N.X j).val.presheaf ⊤ p trivial
            (tilde.toOpen (R := .of A') (C.X j) ⊤ ((1 : A') ⊗ₜ[A, φg'] x))) =
            (1 : (Spec (.of A')).presheaf.stalk p) ⊗ₜ[SingleComplexBaseChange.A g' p, ρ]
              (TopCat.Presheaf.germ (P.X j).val.presheaf ⊤ (g' p) trivial
                (tilde.toOpen (R := .of A) (M.X j) ⊤ x))) ∧
        ∀ y, affineTensorPullbackHomologyStalkIso A A' φg' M p i y =
          (affineRepresentativeStalkIso (Spec (.of A')) p T i).inv
            (HomologicalComplex.homologyMap
              (SingleComplexBaseChange.tensorStalkIso f f' g g' sq p P).hom i
                (HomologicalComplex.homologyMap τ.hom i
                  (affineTildeHomologyLocalization A' C p i y))) := by sorry

end AlgebraicGeometry
