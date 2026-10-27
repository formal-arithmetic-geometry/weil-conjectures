/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E4
-/
module

public import Sheaf.Paper.ProEtaleTensorPullbackModels
public import Mathlib.CategoryTheory.Whiskering
import all Sheaf.Paper.ProEtaleTensorPullbackModels
import all Sheaf.Paper.RingedTopoiCanonicalTensorPullback
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.ResolvingRepresentativeWhiskering
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # The complex-level setup for canonical tensor pullback

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0G7E;
Categories, Tag 04VK (blueprint: lem-weil-pbc-proetale-tensor-descent-data).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.presheafToSheaf
  CategoryTheory.tensorPullbackTotal CategoryTheory.tensorPullbackTotalComponent
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotal
  AlgebraicGeometry.Scheme.proEtaleTensorPullbackTotalIso

universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

attribute [local irreducible] SheafOfModules.monoidalCategory

private theorem pullback_flatRepresentatives
    (P : CochainComplex (proEtaleRingModules Y R) ℤ)
    (hp : proEtaleFlatRepresentatives Y R P) :
    proEtaleFlatRepresentatives X S
      (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P) := by
  let A := proEtaleRingModules Y R
  let L := proEtaleRingModulePullback f R S c
  let I := modelNormalizedAlgebraicLift f R
  have : PreservesFiniteLimits (proEtaleSheafInverseImage f (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1
  have hobj (M : A) : L.obj M = SheafOfModules.changeOfRings c.hom (I.modules.obj M) :=
    rfl
  have hmap : ∀ {M N : A} (v : M ⟶ N), L.map v = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom c.hom (I.modules.obj M) (I.modules.map v) ≫
        eqToHom (hobj N).symm := by
    intros
    rfl
  exact SheafOfModules.isKFlat_ringedToposPullback
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1))) I c.hom L hobj hmap P hp.1 hp.2


private theorem tensorRepresentatives_fullyFaithful :
    Nonempty (((whiskeringLeft
      ((proEtaleFlatRepresentatives Y R).FullSubcategory ×
        (proEtaleFlatRepresentatives Y R).FullSubcategory)
      (DerivedCategory (proEtaleRingModules Y R) ×
        DerivedCategory (proEtaleRingModules Y R))
      (DerivedCategory (proEtaleRingModules X S))).obj
      (((proEtaleFlatRepresentatives Y R).ι ⋙ DerivedCategory.Q).prod
        ((proEtaleFlatRepresentatives Y R).ι ⋙ DerivedCategory.Q))).FullyFaithful) := by
  let A := proEtaleRingModules Y R
  let B := proEtaleRingModules X S
  let PR := proEtaleFlatRepresentatives Y R
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun Z ↦ PR Z.as
  have hres : ∀ Z : HomotopyCategory A (.up ℤ),
      ∃ (W : H.FullSubcategory) (v : W.obj ⟶ Z), HomotopyCategory.quasiIso A (.up ℤ) v := by
    intro Z
    obtain ⟨P, v, hp, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) Z.as
    have hflat : ∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology Y) (R := R)
        (P.X n) := fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R (P.X n)).symm (hf n)
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, hp, hflat⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map v, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff v).2 hq
  obtain ⟨ff⟩ := CategoryTheory.resolvingRepresentativesFullyFaithfulWhiskering
    (K := CochainComplex A ℤ) (H := HomotopyCategory A (.up ℤ))
    (D := DerivedCategory A) (DerivedCategory B)
    (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh PR H (fun _ ↦ Iff.rfl) hres
  let ff' := ff.ofIso ((Functor.whiskeringLeft _ _ (DerivedCategory B)).mapIso
    (NatIso.prod (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))
      (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))))
  exact ⟨ff'⟩


private theorem totalTensorPullbackIso_exists :
    ∃ e :
    ((((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).prod
      ((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ))) ⋙
      Functor.uncurry.obj ((proEtaleOrdinaryTensor X S).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ))) ≅
    (Functor.uncurry.obj ((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))) ⋙
      (proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ),
    ∀ P Q : CochainComplex (proEtaleRingModules Y R) ℤ,
      e.inv.app (P, Q) = (proEtaleTensorPullbackTotalIso f R S c P Q).inv := by
  let L := proEtaleRingModulePullback f R S c
  let F := L.mapHomologicalComplex (.up ℤ)
  let tR := Functor.uncurry.obj ((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  let tS := Functor.uncurry.obj ((proEtaleOrdinaryTensor X S).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  let b0 : (F.prod F) ⋙ tS ≅ tR ⋙ F := NatIso.ofComponents
    (fun Z ↦ proEtaleTensorPullbackTotalIso f R S c Z.1 Z.2)
    (by
      intro Z W v
      let := SheafOfModules.monoidalCategory R
      let := SheafOfModules.monoidalCategory S
      simp only [proEtaleTensorPullbackTotalIso, asIso_hom, proEtaleTensorPullbackTotal]
      dsimp only [F, tR, tS, Functor.comp_map, Functor.prod_map]
      simp only [Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
        SheafOfModules.CanonicalTensorPullbackProof.tensorMap_factor]
      exact SheafOfModules.CanonicalTensorPullbackProof.tensorPullbackTotal_naturality
        L (proEtaleOrdinaryTensorPullback f R S c)
        (fun {_ _ _ _} v z ↦ by
          simpa only [proEtaleOrdinaryTensor, curriedTensor, tensorHom_def, Category.assoc]
            using proEtaleOrdinaryTensorPullback_naturality f R S c _ _ _ _ v z) v.1 v.2)
  exact ⟨b0, fun _ _ ↦ rfl⟩

/-- The complex-level inputs for tensor-comparison descent, with every component fixed.
Source: Stacks 07A4, 0G7E and Categories 04VK
(blueprint: lem-weil-pbc-proetale-tensor-descent-data).
Proof: apply ringed-topos K-flat pullback to the normalized algebraic inverse image.
Resolve each homotopy object by a flat-term K-flat complex, identify the two tensor
flatness predicates, and apply the resolving-representative restriction theorem.
The quotient comparison transfers full faithfulness to the specified localization.
Finally, the signed-total comparisons form a natural isomorphism: naturality holds
on every homogeneous tensor summand by ordinary tensor naturality. Its inverse
component is the stipulated inverse total comparison by construction. -/
theorem proEtaleTensorPullbackDescentData :
    (∀ (P : CochainComplex (proEtaleRingModules Y R) ℤ),
      proEtaleFlatRepresentatives Y R P →
        proEtaleFlatRepresentatives X S
          (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P)) ∧
    Nonempty (((whiskeringLeft
      ((proEtaleFlatRepresentatives Y R).FullSubcategory ×
        (proEtaleFlatRepresentatives Y R).FullSubcategory)
      (DerivedCategory (proEtaleRingModules Y R) ×
        DerivedCategory (proEtaleRingModules Y R))
      (DerivedCategory (proEtaleRingModules X S))).obj
      (((proEtaleFlatRepresentatives Y R).ι ⋙ DerivedCategory.Q).prod
        ((proEtaleFlatRepresentatives Y R).ι ⋙ DerivedCategory.Q))).FullyFaithful) ∧
    ∃ e :
    ((((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).prod
      ((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ))) ⋙
      Functor.uncurry.obj ((proEtaleOrdinaryTensor X S).map₂HomologicalComplex
        (.up ℤ) (.up ℤ) (.up ℤ))) ≅
    (Functor.uncurry.obj ((proEtaleOrdinaryTensor Y R).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))) ⋙
      (proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ),
    ∀ P Q : CochainComplex (proEtaleRingModules Y R) ℤ,
      e.inv.app (P, Q) = (proEtaleTensorPullbackTotalIso f R S c P Q).inv := by
  exact ⟨pullback_flatRepresentatives f R S c,
    tensorRepresentatives_fullyFaithful R S, totalTensorPullbackIso_exists f R S c⟩

end AlgebraicGeometry.Scheme
