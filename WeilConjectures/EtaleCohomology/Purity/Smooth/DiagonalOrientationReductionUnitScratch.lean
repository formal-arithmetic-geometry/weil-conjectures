module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitChange

universe u

open CategoryTheory Limits MonoidalCategory

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.Etale

open Scheme Functor.OplaxMonoidal Functor.LaxMonoidal

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (X : Scheme.{u})

set_option profiler true in
lemma cc :
    (Adjunction.mapHomologicalComplex (.up ℤ)
        (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ)).unit.app
        (𝟙_ (CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ)) ≫
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomologicalComplex (.up ℤ)).map
        (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomologicalComplex (.up ℤ))) =
    (HomologicalComplex.single _ (.up ℤ) 0).map (extendScalarsUnitMap ρ X) ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (Sheaf.restrictScalars X.smallEtaleTopology ρ) (.up ℤ) 0).inv.app (𝟙_ _) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [HomologicalComplex.comp_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapCochainComplex_η,
    Functor.mapCochainComplexεIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self, extendScalarsUnitMap,
    Adjunction.homEquiv_unit, Functor.Monoidal.εIso_inv, Functor.map_comp, Category.assoc, Iso.app_hom, Iso.inv_hom_id_assoc, Iso.map_inv_hom_id_assoc]
  have hn := (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).unit.naturality
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))).hom
  exact (Category.assoc _ _ _).symm.trans (hn =≫ _).symm

set_option profiler true in
lemma hu' :
    ((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).mapHomotopyCategory
        (.up ℤ)).unit.app (𝟙_ _) =
      (HomotopyCategory.quotient _ (.up ℤ)).map ((Adjunction.mapHomologicalComplex (.up ℤ)
        (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ)).unit.app
        (𝟙_ (CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ))) :=
  Adjunction.mapHomotopyCategory_unit_app_quotient _ _ _

set_option profiler true in
lemma hη :
    ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).map
        (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ))) =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        (((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomologicalComplex (.up ℤ)).map
          (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomologicalComplex (.up ℤ)))) :=
  rfl

set_option profiler true in
lemma hdef :
    extendScalarsHomotopyUnitMap ρ X =
      ((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).mapHomotopyCategory
        (.up ℤ)).unit.app (𝟙_ _) ≫
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).map
        (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ))) :=
  Adjunction.homEquiv_unit _ _ _ _

set_option profiler true in
lemma c2 :
    extendScalarsHomotopyUnitMap ρ X =
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.single _ (.up ℤ) 0).map (extendScalarsUnitMap ρ X) ≫
          (HomologicalComplex.singleMapHomologicalComplex
            (Sheaf.restrictScalars X.smallEtaleTopology ρ) (.up ℤ) 0).inv.app (𝟙_ _)) := by
  rw [hdef, hu', hη, ← Functor.map_comp, cc]

end AlgebraicGeometry.Etale
