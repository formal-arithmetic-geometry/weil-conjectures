/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Tensoring a K-flat quasi-isomorphism with an arbitrary complex

The ring is regarded as a constant sheaf on the one-point site with the bottom topology.
K-flatness is the existing `CochainComplex.IsKFlatTensor` for sheaves of modules on this site.

## References

* Stacks Project, Lemma 15.60.12, Tag 064L (see also Tags 0FNI, 06Y0, 06Y4)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- The commutative ring `R` regarded as a
sheaf on the one-point site.
The bottom topology imposes no additional sheaf condition; the constant presheaf
has value `R` at the unique object. -/
def onePointRingSheaf (R : Type u) [CommRing R] :
    Sheaf (⊥ : GrothendieckTopology (Discrete PUnit.{u+1})) CommRingCat.{u} :=
  ⟨(Functor.const _).obj (CommRingCat.of R), Presheaf.isSheaf_bot _⟩

private theorem quasiIso_of_commuting_square
    {A B C D : CochainComplex (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj (onePointRingSheaf R))) ℤ}
    (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (k : C ⟶ D)
    (hf : QuasiIso f) (hg : QuasiIso g) (hh : QuasiIso h)
    (comm : f ≫ h = g ≫ k) : QuasiIso k := by
  have := hf
  have := hg
  have := hh
  have hcomp : QuasiIso (g ≫ k) := by
    rw [← comm]
    infer_instance
  have := hcomp
  exact quasiIso_of_comp_left g k

private theorem kFlat_tensor_right_of_quasiIso
    {E E' K : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj (onePointRingSheaf R))) ℤ}
    (α : E ⟶ E') (hα : QuasiIso α) (hK : K.IsKFlatTensor) :
    (letI := SheafOfModules.monoidalCategory (onePointRingSheaf R)
     QuasiIso (HomologicalComplex.mapBifunctorMap α (𝟙 K) (curriedTensor _) (.up ℤ))) := by
  let := SheafOfModules.monoidalCategory (onePointRingSheaf R)
  let := (SheafOfModules.tensorClosed (onePointRingSheaf R)).1.some
  have hc := (mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (mappingCone α) hc
  apply (mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht i).of_iso (mapBifunctorMappingCone₁Iso α K (curriedTensor _))

private theorem kFlat_tensor_left_of_quasiIso
    {K L L' : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj (onePointRingSheaf R))) ℤ}
    (α : L ⟶ L') (hα : QuasiIso α) (hK : K.IsKFlatTensor) :
    (letI := SheafOfModules.monoidalCategory (onePointRingSheaf R)
     QuasiIso (HomologicalComplex.mapBifunctorMap (𝟙 K) α (curriedTensor _) (.up ℤ))) := by
  let := SheafOfModules.monoidalCategory (onePointRingSheaf R)
  let := SheafOfModules.symmetricCategory (onePointRingSheaf R)
  let := (SheafOfModules.tensorClosed (onePointRingSheaf R)).1.some
  have hc := (mappingCone.quasiIso_iff_acyclic α).1 hα
  have ht := hK (mappingCone α) hc
  let F := curriedTensor (SheafOfModules.{u}
    ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj (onePointRingSheaf R)))
  let e : (((F.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (mappingCone α)).obj K) ≅
      (((F.flip.mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj
      (mappingCone α)).obj K) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents
        (fun q ↦ β_ ((mappingCone α).X p) (K.X q)) (by
          intro q q' hqq'
          exact (BraidedCategory.braiding_naturality_right
            ((mappingCone α).X p) (K.d q q')).symm)) (by
        intro p p' hpp'
        ext q : 1
        exact (BraidedCategory.braiding_naturality_left
          ((mappingCone α).d p p') (K.X q)).symm)
  have ht' : (mapBifunctor K (mappingCone α) F).Acyclic := by
    intro i
    exact (ht i).of_iso (HomologicalComplex₂.total.mapIso e (.up ℤ) ≪≫
      HomologicalComplex.mapBifunctorFlipIso K (mappingCone α) F (.up ℤ))
  apply (mappingCone.quasiIso_iff_acyclic _).2
  intro i
  exact (ht' i).of_iso (mapBifunctorMappingCone₂Iso K α F)

/-- If `α` is a quasi-isomorphism between K-flat complexes of `R`-modules, then `Tot(α ⊗ 1_N)`
is a quasi-isomorphism for every complex `N`. Here `R` is a sheaf on the one-point site. -/
theorem kFlat_tensor_quasiIso
    {E E' N : CochainComplex
      (SheafOfModules.{u}
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj (onePointRingSheaf R))) ℤ}
    (α : E ⟶ E')
    (hα : QuasiIso α)
    (hE : E.IsKFlatTensor)
    (hE' : E'.IsKFlatTensor) :
    (letI := SheafOfModules.monoidalCategory (onePointRingSheaf R)
     QuasiIso (HomologicalComplex.mapBifunctorMap α (𝟙 N) (curriedTensor _) (.up ℤ))) := by
  let := SheafOfModules.monoidalCategory (onePointRingSheaf R)
  obtain ⟨K, s, hK, _, hs, _⟩ := exists_isKFlatResolution N
  let f := HomologicalComplex.mapBifunctorMap α (𝟙 K) (curriedTensor _) (.up ℤ)
  let g := HomologicalComplex.mapBifunctorMap (𝟙 E) s (curriedTensor _) (.up ℤ)
  let h := HomologicalComplex.mapBifunctorMap (𝟙 E') s (curriedTensor _) (.up ℤ)
  let k := HomologicalComplex.mapBifunctorMap α (𝟙 N) (curriedTensor _) (.up ℤ)
  apply quasiIso_of_commuting_square f g h k
  · exact kFlat_tensor_right_of_quasiIso α hα hK
  · exact kFlat_tensor_left_of_quasiIso s hs hE
  · exact kFlat_tensor_left_of_quasiIso s hs hE'
  · change ((curriedTensor _).map₂CochainComplex.map α).app K ≫
        ((curriedTensor _).map₂CochainComplex.obj E').map s =
      ((curriedTensor _).map₂CochainComplex.obj E).map s ≫
        ((curriedTensor _).map₂CochainComplex.map α).app N
    exact (((curriedTensor _).map₂CochainComplex.map α).naturality s).symm

end CochainComplex
