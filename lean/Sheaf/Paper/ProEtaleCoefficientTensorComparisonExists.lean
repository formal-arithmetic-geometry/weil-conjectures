/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module
public import Sheaf.Paper.BoundedConstructibleTower
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import Sheaf.Algebra.Homology.RingIsomorphismTensorTransport
import all Sheaf.Paper.RingedTopoiCanonicalTensorPullback
import Sheaf.Paper.ResolvingRepresentativeWhiskering
import Sheaf.Paper.TensorPullbackRepresentativeDescent
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! # Existence of the coefficient restriction tensor comparison

(blueprint: lem-pbc-coefficient-restriction-tensor-comparison-existence)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] SheafOfModules.monoidalCategory
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CoefficientTensorTransport

private theorem representatives_fullyFaithful (X : Scheme.{u})
    (R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    Nonempty (((whiskeringLeft
      ((proEtaleFlatRepresentatives X S).FullSubcategory ×
        (proEtaleFlatRepresentatives X S).FullSubcategory)
      (DerivedCategory (proEtaleRingModules X S) ×
        DerivedCategory (proEtaleRingModules X S))
      (DerivedCategory (proEtaleRingModules X R))).obj
      (((proEtaleFlatRepresentatives X S).ι ⋙ DerivedCategory.Q).prod
        ((proEtaleFlatRepresentatives X S).ι ⋙ DerivedCategory.Q))).FullyFaithful) := by
  let A := proEtaleRingModules X S
  let B := proEtaleRingModules X R
  let PR := proEtaleFlatRepresentatives X S
  let H : ObjectProperty (HomotopyCategory A (.up ℤ)) := fun Z ↦ PR Z.as
  have hres : ∀ Z : HomotopyCategory A (.up ℤ),
      ∃ (W : H.FullSubcategory) (v : W.obj ⟶ Z), HomotopyCategory.quasiIso A (.up ℤ) v := by
    intro Z
    obtain ⟨P, v, hp, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := S) Z.as
    have hflat : ∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology X) (R := S)
        (P.X n) := fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso S (P.X n)).symm (hf n)
    refine ⟨⟨(HomotopyCategory.quotient A (.up ℤ)).obj P, hp, hflat⟩,
      (HomotopyCategory.quotient A (.up ℤ)).map v, ?_⟩
    exact (HomotopyCategory.quotient_map_mem_quasiIso_iff v).2 hq
  obtain ⟨ff⟩ := CategoryTheory.resolvingRepresentativesFullyFaithfulWhiskering
    (K := CochainComplex A ℤ) (H := HomotopyCategory A (.up ℤ))
    (D := DerivedCategory A) (DerivedCategory B)
    (HomotopyCategory.quotient A (.up ℤ)) HomotopyCategory.quotient_obj_surjective
    (HomotopyCategory.quasiIso A (.up ℤ)) DerivedCategory.Qh PR H (fun _ ↦ Iff.rfl) hres
  exact ⟨ff.ofIso ((Functor.whiskeringLeft _ _ (DerivedCategory B)).mapIso
    (NatIso.prod (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))
      (isoWhiskerLeft PR.ι (DerivedCategory.quotientCompQhIso A))))⟩

/-- Restriction along a coefficient isomorphism has a normalized derived tensor
comparison between any two supplied tensor models. The proof transports flat
K-flat representatives through the exact monoidal equivalence and descends the
signed total comparison by full faithfulness of the resolving subcategory.
(blueprint: lem-pbc-coefficient-restriction-tensor-comparison-existence)
-/
theorem tensorComparison_exists {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (aY : ProEtaleTensorModel Y R)
    (z : ProEtaleTensorModel X
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
    (aX : ProEtaleTensorModel X S) :
    Nonempty (((pbcDerivedRestrict c.hom).prod (pbcDerivedRestrict c.hom)) ⋙ z.tensor ≅
      aX.tensor ⋙ pbcDerivedRestrict c.hom) := by
  let _ := aY
  obtain ⟨o⟩ := SheafOfModules.ringIso_tensor_transport c
  let L := pbcRestrict c.hom
  let F := L.mapHomologicalComplex (.up ℤ)
  let LF := pbcDerivedRestrict c.hom
  let PR := proEtaleFlatRepresentatives X S
  let PS := proEtaleFlatRepresentatives X
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
  let tR := Functor.uncurry.obj ((proEtaleOrdinaryTensor X S).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))
  let tS := Functor.uncurry.obj ((proEtaleOrdinaryTensor X
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)).map₂HomologicalComplex
      (.up ℤ) (.up ℤ) (.up ℤ))
  have hF (P : CochainComplex (proEtaleRingModules X S) ℤ) (hp : PR P) :
      PS (F.obj P) :=
    ⟨(o.kflat_iff P).2 hp.1, fun n ↦ (o.flat_iff (P.X n)).2 (hp.2 n)⟩
  let b : tR ⋙ F ≅ (F.prod F) ⋙ tS := NatIso.ofComponents
    (fun Z ↦ o.totalIso Z.1 Z.2)
    (by
      intro Z W v
      dsimp only [tR, tS, Functor.comp_map, Functor.prod_map]
      simp only [Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
        SheafOfModules.CanonicalTensorPullbackProof.tensorMap_factor]
      exact o.total_naturality v.1 v.2)
  obtain ⟨ff⟩ := representatives_fullyFaithful X _ S
  obtain ⟨alpha, _, _⟩ := CategoryTheory.tensorComparisonDescent
    DerivedCategory.Q DerivedCategory.Q F LF L.mapDerivedCategoryFactors.hom
    PR PS hF ff tR tS aX.tensor z.tensor aX.representative z.representative b
    (fun _ _ ↦ inferInstance) (fun _ _ _ _ ↦ inferInstance)
  exact ⟨alpha.symm⟩

end AlgebraicGeometry.Scheme.CoefficientTensorTransport
