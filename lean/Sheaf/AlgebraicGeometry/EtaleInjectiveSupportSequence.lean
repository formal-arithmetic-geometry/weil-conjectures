/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
public import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.ExactSequence
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.SixFunctors.OpenClosed.SupportedSections
import WeilConjectures.SixFunctors.OpenClosed.Derived
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# The ordinary etale injective support sequence

Source: Stacks Project, Tags 093X, 09XQ, 0A45, 08FI, 070I, 070K, 08BJ and 0152
(blueprint: lem-pur-etale-injective-support-sequence).

The functor `closedUpperShriek (ModuleCat A) i j` is the existing construction
`i^* ker(id → j_*j^*)`. The sequence uses its actual adjunction counit and the actual
open adjunction unit. The derived comparisons below are fixed by the derived-functor
unit and uniqueness of right adjoints, including counit normalization.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Functor

/- Compatibility of derived adjunction maps with their fixed complex comparisons. -/
section
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]

private theorem quotient_hom (E : Type*) [Category E] [Abelian E]
    [HasDerivedCategory E] (I : CochainComplex E ℤ) :
    (DerivedCategory.quotientCompQhIso E).hom.app I = 𝟙 (DerivedCategory.Q.obj I) := rfl

private theorem quotient_inv (E : Type*) [Category E] [Abelian E]
    [HasDerivedCategory E] (I : CochainComplex E ℤ) :
    (DerivedCategory.quotientCompQhIso E).inv.app I = 𝟙 (DerivedCategory.Q.obj I) := rfl

private theorem homotopy_inv (I : CochainComplex C ℤ) :
    (L.mapHomotopyCategoryFactors (.up ℤ)).inv.app I =
      𝟙 ((HomotopyCategory.quotient _ _).obj
        ((L.mapHomologicalComplex (.up ℤ)).obj I)) := rfl

variable [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions D]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)

private theorem derivedUnit_Q (I : CochainComplex C ℤ)
    [CochainComplex.IsKInjective ((L.mapHomologicalComplex (.up ℤ)).obj I)] :
    DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app I) ≫
      (R.rightDerivedFunctorObjQIso ((L.mapHomologicalComplex (.up ℤ)).obj I)).inv =
    adj.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj I) ≫
      R.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.hom.app I) := by
  have h := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ _).obj I)
  rw [L.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient (c := .up ℤ) adj I] at h
  simp only [quotient_hom, quotient_inv, homotopy_inv, CategoryTheory.Functor.map_id] at h
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_inv, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv,
    Functor.mapIso_symm, Functor.mapIso_hom, asIso_hom, quotient_hom, quotient_inv,
    Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Category.comp_id] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact h.symm

private theorem derivedUnit_Q_normalized (I : CochainComplex C ℤ)
    [CochainComplex.IsKInjective ((L.mapHomologicalComplex (.up ℤ)).obj I)] :
    DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app I) ≫
        (R.rightDerivedFunctorObjQIso ((L.mapHomologicalComplex (.up ℤ)).obj I)).inv ≫
        R.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.inv.app I) =
      adj.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Q.obj I) := by
  rw [← Category.assoc, derivedUnit_Q adj I, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem derivedCounit_Q (I : CochainComplex D ℤ) [I.IsKInjective] :
    L.mapDerivedCategory.map (R.rightDerivedFunctorObjQIso I).inv ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Q.obj I) =
    L.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj I) ≫
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  have h := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso D (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.quotient _ _).obj I)
  erw [L.mapDerivedCategoryFactorsh_hom_app ((R.mapHomologicalComplex (.up ℤ)).obj I),
    Adjunction.mapHomotopyCategory_counit_app_quotient (c := .up ℤ) adj I] at h
  simp only [quotient_hom, quotient_inv, homotopy_inv, CategoryTheory.Functor.map_id] at h
  simp only [Functor.rightDerivedFunctorObjQIso, Iso.trans_inv, Iso.symm_inv,
    Iso.app_hom, Iso.app_inv,
    Functor.mapIso_symm, Functor.mapIso_hom, asIso_hom, quotient_hom, quotient_inv,
    Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Category.comp_id] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact h
private theorem derivedCounit_Q_normalized [Abelian.HasKInjectiveResolutions C]
    {T : DerivedCategory D ⥤ DerivedCategory C} (other : L.rightDerivedFunctor ⊣ T)
    (I : CochainComplex D ℤ) [I.IsKInjective] :
    L.mapDerivedCategoryFactors.inv.app ((R.mapHomologicalComplex (.up ℤ)).obj I) ≫
        L.rightDerivedFunctorIsoMapDerivedCategory.inv.app
          (DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj I)) ≫
        L.rightDerivedFunctor.map ((R.rightDerivedFunctorObjQIso I).inv ≫
          (((adj.mapDerivedCategoryRightDerivedAdjunction).ofNatIsoLeft
              L.rightDerivedFunctorIsoMapDerivedCategory.symm).rightAdjointUniq other).hom.app
            (DerivedCategory.Q.obj I)) ≫
        other.counit.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [Adjunction.rightAdjointUniq_hom_app_counit]
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Iso.symm_inv]
  rw [← L.rightDerivedFunctorIsoMapDerivedCategory.inv.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [derivedCounit_Q adj I]
  simp only [Iso.inv_hom_id_app_assoc]

end

-- Keep chosen derived adjoints abstract when checking the comparison morphisms.
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Adjunction.mapHomologicalComplex
  _root_.DerivedCategory.Q _root_.DerivedCategory.Qh
  CategoryTheory.Functor.rightAdjoint CategoryTheory.Adjunction.ofIsLeftAdjoint
  CategoryTheory.Functor.rightDerivedFunctorObjQIso
  CategoryTheory.Functor.rightDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors

namespace AlgebraicGeometry.Etale

attribute [local irreducible] upperStar lowerStar closedUpperShriek
  lowerStarClosedUpperShriekAdjunction upperStarLowerStarAdjunction
  derivedLowerStarClosedUpperShriekAdjunction mapDerivedUpperStarLowerStarAdjunction

variable (A : Type (u + 1)) [CommRing A]
  {Z P U : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i]
  (j : U ⟶ P) [IsOpenImmersion j]
  (hij : Set.range i.base = (Set.range j.base)ᶜ)

/-- The termwise support inclusion, as a natural transformation with its explicit
source and target functors. It is the existing closed adjunction counit on complexes.
Source: Stacks Project, Tags 09XQ and 0A45
(blueprint: lem-pur-etale-injective-support-sequence). -/
noncomputable def etaleSupportInclusion :
    (closedUpperShriek (ModuleCat.{u + 1} A) i j).mapHomologicalComplex (.up ℤ) ⋙
      (lowerStar (ModuleCat.{u + 1} A) i).mapHomologicalComplex (.up ℤ) ⟶ 𝟭 _ :=
  ((lowerStarClosedUpperShriekAdjunction (ModuleCat.{u + 1} A) i j hij).mapHomologicalComplex
    (.up ℤ)).counit

/-- The termwise open restriction map, as a natural transformation with its explicit
source and target functors. It is the existing open adjunction unit on complexes.
Source: Stacks Project, Tags 093X and 0A45
(blueprint: lem-pur-etale-injective-support-sequence). -/
noncomputable def etaleSupportRestriction :
    𝟭 (CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) ⟶
      (upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ) ⋙
        (lowerStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ) :=
  ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).mapHomologicalComplex
    (.up ℤ)).unit

/-- The closed support counit followed by the open unit is zero, termwise.
Source: Stacks Project, Tag 09XQ, the support adjunction
(blueprint: lem-pur-etale-injective-support-sequence).

Proof: the supported kernel restricts to zero on U. Every map out of a closed
pushforward is consequently killed by the open unit, by adjunction and disjointness
(lem-pur-etale-supported-kernel-adjunction). Apply this to the support counit in
each degree; equality of maps of complexes is degreewise equality. -/
theorem etaleSupportSequence_zero
    (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (etaleSupportInclusion A i j hij).app I ≫
      (etaleSupportRestriction A j).app I = 0 := by
  apply HomologicalComplex.hom_ext
  intro r
  simp only [HomologicalComplex.comp_f, HomologicalComplex.zero_f,
    etaleSupportInclusion, etaleSupportRestriction,
    Adjunction.mapHomologicalComplex_counit_app_f, Adjunction.mapHomologicalComplex_unit_app_f]
  change (lowerStarClosedUpperShriekAdjunction (ModuleCat.{u + 1} A) i j hij).counit.app
      (I.X r) ≫ (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app (I.X r) = 0
  exact lowerStar_map_comp_unit_app_eq_zero (ModuleCat.{u + 1} A) i j hij _

/-- The canonical sequence `i_*H_A(I) → I → j_*j^*I`, with H_A the existing
closed supported inverse image, and maps the termwise counit and unit.
Source: Stacks Project, Tag 0A45, proof
(blueprint: lem-pur-etale-injective-support-sequence). -/
noncomputable def etaleSupportSequence
    (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ShortComplex (CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :=
  ShortComplex.mk
    ((etaleSupportInclusion A i j hij).app I)
    ((etaleSupportRestriction A j).app I)
    (etaleSupportSequence_zero A i j hij I)

/-- The sequence is functorial on all chain maps, with the prescribed three components.
Source: Stacks Project, Tag 0A45, proof, and Tag 0152, naturality
(blueprint: lem-pur-etale-injective-support-sequence). -/
noncomputable def etaleSupportSequenceMap
    {I J : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ}
    (f : I ⟶ J) : etaleSupportSequence A i j hij I ⟶ etaleSupportSequence A i j hij J :=
  ShortComplex.homMk
    (S₁ := etaleSupportSequence A i j hij I)
    (S₂ := etaleSupportSequence A i j hij J)
    (((closedUpperShriek (ModuleCat.{u + 1} A) i j).mapHomologicalComplex (.up ℤ) ⋙
      (lowerStar (ModuleCat.{u + 1} A) i).mapHomologicalComplex (.up ℤ)).map f)
    f
    (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ) ⋙
      (lowerStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).map f)
    ((etaleSupportInclusion A i j hij).naturality f)
    ((etaleSupportRestriction A j).naturality f)

private theorem supportSequence_shortExact
    (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [∀ r : ℤ, Injective (I.X r)] :
    (etaleSupportSequence A i j hij I).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro r
  let S := (etaleSupportSequence A i j hij I).map
    (HomologicalComplex.eval _ (.up ℤ) r)
  have hmono : Mono S.f := by
    change Mono (((lowerStarClosedUpperShriekAdjunction
      (ModuleCat.{u + 1} A) i j hij).mapHomologicalComplex (.up ℤ)).counit.app I |>.f r)
    rw [Adjunction.mapHomologicalComplex_counit_app_f]
    infer_instance
  have hepi : Epi S.g := by
    change Epi (((upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).unit.app I |>.f r)
    rw [Adjunction.mapHomologicalComplex_unit_app_f]
    have := isSplitEpi_upperStarLowerStarAdjunction_unit_app_of_injective
      (ModuleCat.{u + 1} A) j i hij (I.X r)
    infer_instance
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_of_f_is_kernel S ?_) hmono hepi
  have hf : S.f = (lowerStarClosedUpperShriekAdjunction
      (ModuleCat.{u + 1} A) i j hij).counit.app (I.X r) :=
    Adjunction.mapHomologicalComplex_counit_app_f _ _ _ _
  have hg : S.g = (upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) j).unit.app (I.X r) :=
    Adjunction.mapHomologicalComplex_unit_app_f _ _ _ _
  exact IsKernel.ofIso _ (kernelIsKernel
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app (I.X r)))
    (KernelFork.ofι S.f S.zero) (Iso.refl _) (Iso.refl _)
    ((closedUpperShriekCompLowerStarIso (ModuleCat.{u + 1} A) i j hij).app (I.X r)).symm
    (by simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id] using hg)
    (by
      change ((closedUpperShriekCompLowerStarIso
        (ModuleCat.{u + 1} A) i j hij).app (I.X r)).inv ≫ S.f =
        kernel.ι ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app (I.X r)) ≫ 𝟙 _
      rw [hf, lowerStarClosedUpperShriekAdjunction_counit_app]
      simp only [Iso.app_inv, Iso.inv_hom_id_app_assoc, Category.comp_id]
      rfl)

private theorem supportRestriction_isKInjective
    (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj I) := by
  have : (upperStar (ModuleCat.{u + 1} A) j).PreservesKInjectiveComplexes :=
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
      |>.preservesKInjectiveComplexes
  exact Functor.PreservesKInjectiveComplexes.isKInjective_map I

/-- The computation of `Ri_A^!` on a K-injective complex, using the derived unit and
then the unique counit-compatible comparison to the recorded ordinary right adjoint.
Source: Stacks Project, Tags 070K, 08BJ and 09XQ; det-sp-unique-right-adjoint
(blueprint: lem-pur-etale-injective-support-sequence). -/
noncomputable def etaleSupportShriekComparison [Finite A]
    (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [I.IsKInjective] :
    _root_.DerivedCategory.Q.obj
        (((closedUpperShriek (ModuleCat.{u + 1} A) i j).mapHomologicalComplex (.up ℤ)).obj I) ≅
      (R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj
        (_root_.DerivedCategory.Q.obj I) :=
  ((closedUpperShriek (ModuleCat.{u + 1} A) i j).rightDerivedFunctorObjQIso I).symm ≪≫
    ((derivedLowerStarClosedUpperShriekAdjunction (R := A) i j hij).rightAdjointUniq
      (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i)))).app
        (_root_.DerivedCategory.Q.obj I)

/-- The first-term comparison, using exact termwise closed direct image and the
preceding counit-compatible computation of `Ri_A^!`.
Source: Stacks Project, Tags 04CA, 09XQ and 0A45
(blueprint: lem-pur-etale-injective-support-sequence). -/
noncomputable def etaleSupportFirstComparison [Finite A]
    (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [I.IsKInjective] :
    _root_.DerivedCategory.Q.obj (etaleSupportSequence A i j hij I).X₁ ≅
      (R(lowerStar (ModuleCat.{u + 1} A) i)).obj
        ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.obj
          (_root_.DerivedCategory.Q.obj I)) :=
  ((lowerStar (ModuleCat.{u + 1} A) i).mapDerivedCategoryFactors.app
    (((closedUpperShriek (ModuleCat.{u + 1} A) i j).mapHomologicalComplex (.up ℤ)).obj I)).symm ≪≫
    ((lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctorIsoMapDerivedCategory.app
      (_root_.DerivedCategory.Q.obj
        (((closedUpperShriek (ModuleCat.{u + 1} A) i j).mapHomologicalComplex
          (.up ℤ)).obj I))).symm ≪≫
    (R(lowerStar (ModuleCat.{u + 1} A) i)).mapIso
      (etaleSupportShriekComparison A i j hij I)

/-- The third-term comparison is normalized by the right-derived unit and the
exact restriction comparison. The proof argument records K-injectivity on U,
without imposing it as an extra hypothesis of the main statement.
Source: Stacks Project, Tags 08FI, 070K and 0A45
(blueprint: lem-pur-etale-injective-support-sequence). -/
noncomputable def etaleSupportThirdComparison
    (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hJ : CochainComplex.IsKInjective
      (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj I)) :
    _root_.DerivedCategory.Q.obj
        (((lowerStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj
          (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj I)) ≅
      (R(lowerStar (ModuleCat.{u + 1} A) j)).obj
        ((D(upperStar (ModuleCat.{u + 1} A) j)).obj (_root_.DerivedCategory.Q.obj I)) :=
  letI := hJ
  ((lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorObjQIso
    (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj I)).symm ≪≫
    (R(lowerStar (ModuleCat.{u + 1} A) j)).mapIso
      ((upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryFactors.app I).symm

private theorem supportFirst_counit [Finite A]
    (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [I.IsKInjective] :
    (etaleSupportFirstComparison A i j hij I).hom ≫
        (Adjunction.ofIsLeftAdjoint
          (R(lowerStar (ModuleCat.{u + 1} A) i))).counit.app
            (_root_.DerivedCategory.Q.obj I) =
      _root_.DerivedCategory.Q.map ((etaleSupportInclusion A i j hij).app I) := by
  dsimp only [etaleSupportFirstComparison, etaleSupportShriekComparison,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom]
  simp only [Category.assoc]
  unfold derivedLowerStarClosedUpperShriekAdjunction
  exact derivedCounit_Q_normalized
    (lowerStarClosedUpperShriekAdjunction (ModuleCat.{u + 1} A) i j hij)
    (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat.{u + 1} A) i))) I

private theorem supportThird_unit
    (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (hJ : CochainComplex.IsKInjective
      (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj I)) :
    _root_.DerivedCategory.Q.map ((etaleSupportRestriction A j).app I) ≫
        (etaleSupportThirdComparison A j I hJ).hom =
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app
        (_root_.DerivedCategory.Q.obj I) := by
  let := hJ
  dsimp only [etaleSupportThirdComparison, etaleSupportRestriction, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv]
  unfold mapDerivedUpperStarLowerStarAdjunction
  exact derivedUnit_Q_normalized
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j) I

/-- A degreewise-injective K-injective model gives the short exact support sequence,
and its canonical SES triangle realizes the actual derived counit/unit triangle,
with fixed endpoint comparisons and the representing isomorphism in the middle.
The boundary is one natural transformation on the ordinary unbounded derived category.
Source: Stacks Project, Tags 093X, 09XQ, 0A45, 08FI, 070I, 070K, 08BJ and 0152
(blueprint: lem-pur-etale-injective-support-sequence).

Proof:
1. Form G(M)=ker(eta_j(M)). The closed unit q:G(M)→i_*i^*G(M) is invertible by
   lem-pur-etale-supported-kernel-adjunction and is module-linear. Exact closed
   direct image and full faithfulness identify maps i_*N→M with maps N→i^*G(M);
   the counit is q inverse followed by the kernel inclusion (lem-kun-04ca).
2. Evaluate the open unit on an etale V over P. It is restriction along the
   monomorphism V×_P U→V (lem-weil-pbc-etale-inverse-image-restriction). By
   lem-pur-ringed-site-injective-mono-restriction it is surjective for each
   injective module I^r. Substitute the supported-kernel identification to get
   degreewise short exactness; lem-weil-pbc-cochain-complexes-degreewise-exact
   gives short exactness of complexes. Naturality of unit and counit gives its maps.
3. Module sheaves are Grothendieck abelian (lem-weil-pbc-ring-sheaves-grothendieck),
   hence have degreewise-injective K-injective replacements
   (lem-pur-kinjective-degreewise-existence). The termwise additive H_A acts on
   homotopies, shifts and cones. lem-weil-pbc-kinjective-total-derived computes RH_A
   on I. No bounded-below replacement is made.
4. Since i_* is exact, H_A preserves K-injectives
   (lem-weil-pbc-right-adjoint-preserves-kinjective). The Hom bijections of
   lem-weil-pbc-kinjective-hom-derived and lem-weil-pbc-termwise-adjunction-homotopy
   identify RH_A as the right adjoint of Ri_*=i_*. det-sp-unique-right-adjoint
   identifies it with the ordinary right adjoint, compatibly with the counit.
5. Identify open restriction with slice restriction by
   lem-weil-pbc-etale-site-localization-open and
   lem-weil-pbc-etale-inverse-image-restriction. Then
   lem-pur-kinjective-restrict-localized makes j^*I K-injective. Total derivation
   computes Rj_*j^*QI on j_*j^*I, and the termwise adjunction identifies its map
   from QI with the actual derived open unit.
6. Apply lem-weil-pbc-complex-ses-triangle. Its cone-to-quotient construction fixes
   the boundary, including its sign. Steps 4 and 5 identify the endpoints and the
   first two arrows with the ordinary closed counit and open unit. The natural
   boundary of lem-exc-closed-support-triangle is the transported SES boundary.
7. Derived maps between K-injectives are unique homotopy classes of chain maps
   (lem-weil-pbc-kinjective-hom-derived); quasi-isomorphisms are homotopy equivalences.
   Termwise functors preserve these homotopies. SES boundary naturality therefore
   descends to derived naturality and comparison of representatives. No injectivity
   after scalar restriction or forgetting modules is used. -/
theorem etale_injective_support_sequence [Finite A] :
    ∃ δ : D(upperStar (ModuleCat.{u + 1} A) j) ⋙
        R(lowerStar (ModuleCat.{u + 1} A) j) ⟶
        ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint ⋙
          R(lowerStar (ModuleCat.{u + 1} A) i)) ⋙
          shiftFunctor (_root_.DerivedCategory
            (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A))) (1 : ℤ),
      (∀ L : _root_.DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)),
        Triangle.mk
          ((Adjunction.ofIsLeftAdjoint
            (R(lowerStar (ModuleCat.{u + 1} A) i))).counit.app L)
          ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app L)
          (δ.app L) ∈ distTriang _) ∧
      ∀ (I : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        [I.IsKInjective] [∀ r : ℤ, Injective (I.X r)]
        (L : _root_.DerivedCategory (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)))
        (e : _root_.DerivedCategory.Q.obj I ≅ L),
        ∃ (hS : (etaleSupportSequence A i j hij I).ShortExact)
          (hJ : CochainComplex.IsKInjective
            (((upperStar (ModuleCat.{u + 1} A) j).mapHomologicalComplex (.up ℤ)).obj I))
          (t : _root_.DerivedCategory.triangleOfSES hS ≅
            Triangle.mk
              ((Adjunction.ofIsLeftAdjoint
                (R(lowerStar (ModuleCat.{u + 1} A) i))).counit.app L)
              ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app L)
              (δ.app L)),
          t.hom.hom₁ = (etaleSupportFirstComparison A i j hij I).hom ≫
            (R(lowerStar (ModuleCat.{u + 1} A) i)).map
              ((R(lowerStar (ModuleCat.{u + 1} A) i)).rightAdjoint.map e.hom) ∧
          t.hom.hom₂ = e.hom ∧
          t.hom.hom₃ = (etaleSupportThirdComparison A j I hJ).hom ≫
            (R(lowerStar (ModuleCat.{u + 1} A) j)).map
              ((D(upperStar (ModuleCat.{u + 1} A) j)).map e.hom) := by
  classical
  obtain ⟨δ, hδ⟩ := exists_etale_closedSupportTriangle A i j hij
  refine ⟨δ, hδ, ?_⟩
  intro I _ _ L e
  let hS := supportSequence_shortExact A i j hij I
  let hJ := supportRestriction_isKInjective A j I
  let F := R(lowerStar (ModuleCat.{u + 1} A) i)
  let G := R(lowerStar (ModuleCat.{u + 1} A) j)
  let J := D(upperStar (ModuleCat.{u + 1} A) j)
  let e₁ := etaleSupportFirstComparison A i j hij I ≪≫ F.mapIso (F.rightAdjoint.mapIso e)
  let e₃ := etaleSupportThirdComparison A j I hJ ≪≫ G.mapIso (J.mapIso e)
  have h₁ : e₁.hom ≫ (Adjunction.ofIsLeftAdjoint F).counit.app L =
      _root_.DerivedCategory.Q.map ((etaleSupportSequence A i j hij I).f) ≫ e.hom := by
    dsimp only [e₁, Iso.trans_hom, Functor.mapIso_hom]
    rw [Category.assoc]
    erw [(Adjunction.ofIsLeftAdjoint F).counit_naturality]
    rw [← Category.assoc, supportFirst_counit]
    rfl
  have h₃ : _root_.DerivedCategory.Q.map ((etaleSupportSequence A i j hij I).g) ≫ e₃.hom =
      e.hom ≫ (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app L := by
    change _root_.DerivedCategory.Q.map ((etaleSupportRestriction A j).app I) ≫
      e₃.hom = _
    dsimp only [e₃, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, supportThird_unit]
    exact ((mapDerivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) j).unit.naturality e.hom).symm
  obtain ⟨t, ht₁, ht₂⟩ := exists_iso_of_arrow_iso _ _
    (_root_.DerivedCategory.triangleOfSES_distinguished hS) (hδ L)
    (Arrow.isoMk e₁ e h₁)
  have horth : Subsingleton
      ((F.obj (F.rightAdjoint.obj L))⟦(1 : ℤ)⟧ ⟶ G.obj (J.obj L)) := by
    have hz : IsZero (J.obj ((F.obj (F.rightAdjoint.obj L))⟦(1 : ℤ)⟧)) :=
      ((shiftFunctor _ (1 : ℤ)).map_isZero
        (isZero_mapDerivedCategoryUpperStar_obj_rightDerivedLowerStar_of_disjoint_range
          (ModuleCat.{u + 1} A) j i (by rw [hij]; exact disjoint_compl_right) _)).of_iso
        ((J.commShiftIso (1 : ℤ)).app _)
    have : Subsingleton (J.obj ((F.obj (F.rightAdjoint.obj L))⟦(1 : ℤ)⟧) ⟶ J.obj L) :=
      ⟨fun _ _ ↦ hz.eq_of_src _ _⟩
    exact ((mapDerivedUpperStarLowerStarAdjunction
      (ModuleCat.{u + 1} A) j).homEquiv _ _).symm.subsingleton
  have : Subsingleton
      ((_root_.DerivedCategory.triangleOfSES hS).obj₁⟦(1 : ℤ)⟧ ⟶ G.obj (J.obj L)) :=
    (((shiftFunctor _ (1 : ℤ)).mapIso e₁).homCongr (Iso.refl _)).subsingleton
  refine ⟨hS, hJ, t, ht₁, ht₂, ?_⟩
  apply Triangle.cancel_mor₂_of_subsingleton (Y := G.obj (J.obj L))
    (_root_.DerivedCategory.triangleOfSES_distinguished hS)
  rw [t.hom.comm₂, ht₂]
  exact h₃.symm


/-- Naturality of the entire support SES triangle, including its canonical boundary,
for chain maps between degreewise-injective K-injective models.
Source: Stacks Project, Tag 0152, naturality of the canonical delta functor
(blueprint: lem-pur-etale-injective-support-sequence).

Proof: etaleSupportSequenceMap is the termwise diagram induced by the chain map,
using naturality of the closed counit and open unit. Apply
lem-weil-pbc-complex-ses-triangle, specifically triangleOfSESδ_naturality, to this
morphism of short exact sequences. Its third square is exactly the displayed equality.
The other two squares are the two fields of the sequence morphism. -/
theorem etaleSupportSequence_boundary_naturality [Finite A]
    {I J : CochainComplex (Sheaf P.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ}
    [I.IsKInjective] [J.IsKInjective]
    [∀ r : ℤ, Injective (I.X r)] [∀ r : ℤ, Injective (J.X r)]
    (hI : (etaleSupportSequence A i j hij I).ShortExact)
    (hJ : (etaleSupportSequence A i j hij J).ShortExact) (f : I ⟶ J) :
    _root_.DerivedCategory.triangleOfSESδ hI ≫
        (_root_.DerivedCategory.Q.map (etaleSupportSequenceMap A i j hij f).τ₁)⟦1⟧' =
      _root_.DerivedCategory.Q.map (etaleSupportSequenceMap A i j hij f).τ₃ ≫
        _root_.DerivedCategory.triangleOfSESδ hJ := by
  exact _root_.DerivedCategory.triangleOfSESδ_naturality hI hJ
    (etaleSupportSequenceMap A i j hij f)

end AlgebraicGeometry.Etale
