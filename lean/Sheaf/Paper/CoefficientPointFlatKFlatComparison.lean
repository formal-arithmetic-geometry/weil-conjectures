/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V5
-/
module

public import Sheaf.Paper.ExternalRHomConePairing
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import all Sheaf.Algebra.Homology.NilpotentDerivedUpperBound
import Sheaf.Algebra.Homology.RingIsomorphismTensorTransport
import all Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import Sheaf.CategoryTheory.ConstantModuleKFlat
import Sheaf.CategoryTheory.ConstantModuleFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat

/-! # Flatness and K-flatness in the coefficient point realization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale.ExternalRHom
variable (A : Type (u + 1)) [CommRing A]

private abbrev J := (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2}))

private def pointRingComparison :
    CochainComplex.onePointRingSheaf A ≅ realizationRing (J.{u}) A := by
  let F := (Functor.const (Discrete PUnit.{u + 2})ᵒᵖ).obj (CommRingCat.of A)
  let := isIso_toSheafify (J.{u}) (Presheaf.isSheaf_bot F)
  exact ObjectProperty.isoMk _ (asIso (toSheafify (J.{u}) F))

private def pointSeed (M : ModuleCat.{u + 1} A) :
    (DerivedCategory.pointConstant A).obj M ⟶
      (SheafOfModules.scalarRestriction.{u + 1, u + 1, u + 1}
        (pointRingComparison A).hom).obj
        ((pointRealization A).obj M) := by
  let P := (siteConstantModulePresheafGeneral
    (C := Discrete PUnit.{u + 2}) A).obj M
  let := (realizationRingUnit_locallyBijective J.{u} A).1
  let := (realizationRingUnit_locallyBijective J.{u} A).2
  exact ⟨PresheafOfModules.toSheafify (realizationRingUnit J.{u} A)
    (M₀ := P) (A := (presheafToSheaf J.{u} AddCommGrpCat.{u + 1}).obj P.presheaf)
    (toSheafify J.{u} P.presheaf)⟩

private instance pointSeed_isIso (M : ModuleCat.{u + 1} A) : IsIso (pointSeed A M) := by
  have : IsIso (((SheafOfModules.toSheaf _) ⋙
      sheafToPresheaf J.{u} AddCommGrpCat.{u + 1}).map (pointSeed A M)) := by
    change IsIso (toSheafify J.{u}
      ((Functor.const (Discrete PUnit.{u + 2})ᵒᵖ).obj
        ((forget₂ (ModuleCat A) AddCommGrpCat).obj M)))
    exact isIso_toSheafify J.{u} (Presheaf.isSheaf_bot _)
  exact isIso_of_reflects_iso _
    ((SheafOfModules.toSheaf _) ⋙ sheafToPresheaf J.{u} AddCommGrpCat.{u + 1})

private instance pointConstant_additive : (DerivedCategory.pointConstant A).Additive where
  map_add := by intros; rfl

private def pointRealizationComparison :
    DerivedCategory.pointConstant A ≅ pointRealization A ⋙
      SheafOfModules.scalarRestriction.{u + 1, u + 1, u + 1}
        (pointRingComparison A).hom :=
  NatIso.ofComponents (fun M ↦ asIso (pointSeed A M)) (by
    intro M N f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    ext x
    exact congrArg (fun z ↦ z.app W x)
      (toSheafify_naturality (J.{u})
        ((Functor.const (Discrete PUnit.{u + 2})ᵒᵖ).map
          ((forget₂ (ModuleCat A) AddCommGrpCat).map f))))

/-- Flatness and K-flatness can be read back from the coefficient point realization.
Source: Stacks Project, Tags 03CY, 06YS and 06YN
(blueprint: lem-pur-coefficient-point-flat-kflat-comparison).
Proof: the bottom-topology constant-ring sheafification unit is an isomorphism.
Transport scalars through it. The module sheafification unit identifies the resulting
complex with the literal constant module complex. Evaluation on the unique point is
an exact tensor equivalence, so it takes flat terms to flat modules and takes the
acyclic-tensor test to the ordinary test. The latter is the categorical K-flat
predicate, by the acyclic-cone criterion. No boundedness assumption is involved. -/
theorem native_flat_kFlat_of_point (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients ((pointComplex A).obj P))
    (hf : ∀ n, SheafOfModules.IsFlatOnSite
      (J := (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})))
      (R := realizationRing (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) A)
        ((pointRealization A).obj (P.X n))) :
    (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)).kFlat P ∧
      ∀ n, ObjectProperty.flat (P.X n) := by
  let R := CochainComplex.onePointRingSheaf A
  let S := realizationRing (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) A
  let := HasDerivedCategory.standard
    (SheafOfModules.scalarModules (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) R)
  let := HasDerivedCategory.standard
    (SheafOfModules.scalarModules (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})) S)
  obtain ⟨T⟩ := SheafOfModules.ringIso_tensor_transport (pointRingComparison A)
  let e := (Functor.mapHomologicalComplexCompIso
    (pointRealizationComparison A).symm (.up ℤ)).app P
  have hraw := (T.kflat_iff ((pointComplex A).obj P)).2 hP
  have hconst := SheafOfModules.kFlat_iso_independent R e hraw
  constructor
  · apply (HomotopyCategory.kFlat_quotient_obj_iff P).1
    apply RingedDerivedNative.kFlat_of_acyclic
    intro Z hZ
    exact DerivedCategory.pointEval_kFlat _ hconst Z hZ
  · intro n
    have hc := SheafOfModules.flatOnSite_of_iso R
      (HomologicalComplex.eval _ (.up ℤ) n |>.mapIso e)
      ((T.flat_iff _).2 (hf n))
    have hc' : SheafOfModules.IsFlat
        (R := CochainComplex.onePointRingSheaf A)
        ((DerivedCategory.pointConstant A).obj (P.X n)) := by
      exact (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso R _ ) hc
    exact (ModuleCat.flat_iff_flat _).2 (DerivedCategory.pointEval_flat _ hc')


/-- The coefficient realization preserves flat-term K-flat module complexes.
Source: Stacks Project, Tags 06YS and 0G7E
(blueprint: lem-sfb-constant-module-kflat).
Proof: constant realization preserves flatness by the local relation criterion.
It is additive, preserves integer-indexed colimits and flat objects, hence preserves
flat-term K-flat complexes. This works for unbounded complexes and the zero ring. -/
private theorem pointComplex_flat_kFlat (P : CochainComplex (ModuleCat.{u + 1} A) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)).kFlat P)
    (hf : ∀ n, ObjectProperty.flat (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients ((pointComplex A).obj P) ∧
      ∀ n, SheafOfModules.IsFlatOnSite
      (J := (⊥ : GrothendieckTopology (Discrete PUnit.{u + 2})))
        (R := realizationRing ((⊥ : GrothendieckTopology (Discrete PUnit.{u + 2}))) A)
        ((pointRealization A).obj (P.X n)) := by
  exact ⟨isKFlat_constantModule ((⊥ : GrothendieckTopology (Discrete PUnit.{u + 2}))) A P hP
    (fun n ↦ (ModuleCat.flat_iff_flat _).1 (hf n)),
    fun n ↦ isFlatOnSite_constantModule ((⊥ : GrothendieckTopology (Discrete PUnit.{u + 2}))) A _
      ((ModuleCat.flat_iff_flat _).1 (hf n))⟩

end AlgebraicGeometry.Etale.ExternalRHom
