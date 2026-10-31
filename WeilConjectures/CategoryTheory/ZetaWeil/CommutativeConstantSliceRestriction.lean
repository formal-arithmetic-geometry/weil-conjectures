/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-! # Restriction of constant modules with commutative coefficients

Source: Stacks Project, Modules on Sites, Sections 03CY and 03DH.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max u v)) [CommRing R] (U : C)

/-- Actual slice restriction followed by the canonical constant-ring identification.
Source: Stacks 03CY and 03DH
(blueprint: lem-zl-commutative-constant-slice-restriction). -/
def commutativeConstantSliceRestriction :
    realizationModules J R ⥤ realizationModules (J.over U) R :=
  SheafOfModules.overFunctor.{max u v}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (realizationRing J R)) U ⋙
    SheafOfModules.restrictScalars.{max u v}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).map
        (constantSheafOverIso J CommRingCat U (CommRingCat.of R)).hom)

instance commutativeConstantSliceRestriction_additive :
    (commutativeConstantSliceRestriction J R U).Additive := by
  let := (ringedOverFunctor_exactGeneral.{u, v, max u v, max u v}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (realizationRing J R)) U).1
  unfold commutativeConstantSliceRestriction
  infer_instance

instance commutativeConstantSliceRestriction_limits :
    PreservesFiniteLimits (commutativeConstantSliceRestriction J R U) := by
  let := (ringedOverFunctor_exactGeneral.{u, v, max u v, max u v}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (realizationRing J R)) U).2.1
  let f := (constantSheafOverIso J CommRingCat U (CommRingCat.of R)).hom
  obtain ⟨hl, _, _⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction f
  let := hl
  unfold commutativeConstantSliceRestriction
  infer_instance

instance commutativeConstantSliceRestriction_colimits :
    PreservesFiniteColimits (commutativeConstantSliceRestriction J R U) := by
  let := (ringedOverFunctor_exactGeneral.{u, v, max u v, max u v}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj (realizationRing J R)) U).2.2
  let f := (constantSheafOverIso J CommRingCat U (CommRingCat.of R)).hom
  obtain ⟨_, hc, _⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction f
  let := hc
  unfold commutativeConstantSliceRestriction
  infer_instance

open Opposite

private theorem sliceScalar_unit (V : (Over U)ᵒᵖ) (r : R) :
    ((constantSheafOverIso J CommRingCat U (CommRingCat.of R)).hom.hom.app V)
      ((realizationRingUnit (J.over U) R).app V r) =
        (realizationRingUnit J R).app ((Over.forget U).op.obj V) r := by
  exact ConcreteCategory.congr_hom
    (congr_app (toSheafify_constantSheafOverHom_hom J CommRingCat U (CommRingCat.of R)) V) r

private def sliceConstantSeed (M : ModuleCat.{max u v} R) :
    (siteConstantModulePresheafGeneral (C := Over U) R).obj M ⟶
      (PresheafOfModules.restrictScalars (realizationRingUnit (J.over U) R)).obj
        ((commutativeConstantSliceRestriction J R U).obj
          ((commutativeSiteConstantModuleFunctor J R).obj M)).val := by
  let := (realizationRingUnit_locallyBijective J R).1
  let := (realizationRingUnit_locallyBijective J R).2
  let P := (siteConstantModulePresheafGeneral (C := C) R).obj M
  let t := PresheafOfModules.toSheafify (realizationRingUnit J R)
    (toSheafify J P.presheaf)
  refine PresheafOfModules.homMk
    (Functor.whiskerLeft (Over.forget U).op (toSheafify J P.presheaf)) ?_
  intro V r x
  refine ((t.app ((Over.forget U).op.obj V)).hom.map_smul r x).trans ?_
  change (realizationRingUnit J R).app ((Over.forget U).op.obj V) r •
      (show ((commutativeSiteConstantModuleFunctor J R).obj M).val.obj
        ((Over.forget U).op.obj V) from t.app ((Over.forget U).op.obj V) x) =
    ((constantSheafOverIso J CommRingCat U (CommRingCat.of R)).hom.hom.app V)
      ((realizationRingUnit (J.over U) R).app V r) •
      (show ((commutativeSiteConstantModuleFunctor J R).obj M).val.obj
        ((Over.forget U).op.obj V) from t.app ((Over.forget U).op.obj V) x)
  rw [sliceScalar_unit]

private def sliceConstantComparison (M : ModuleCat.{max u v} R) :
    (commutativeSiteConstantModuleFunctor (J.over U) R).obj M ⟶
      (commutativeConstantSliceRestriction J R U).obj
        ((commutativeSiteConstantModuleFunctor J R).obj M) :=
  let := (realizationRingUnit_locallyBijective (J.over U) R).1
  let := (realizationRingUnit_locallyBijective (J.over U) R).2
  (PresheafOfModules.sheafificationHomEquiv (realizationRingUnit (J.over U) R)).symm
    (sliceConstantSeed J R U M)

private theorem sliceConstantComparison_fac (M : ModuleCat.{max u v} R) :
    toSheafify (J.over U)
        ((siteConstantModulePresheafGeneral (C := Over U) R).obj M).presheaf ≫
      ((SheafOfModules.toSheaf _).map (sliceConstantComparison J R U M)).hom =
    Functor.whiskerLeft (Over.forget U).op
      (toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj M).presheaf) := by
  let := (realizationRingUnit_locallyBijective (J.over U) R).1
  let := (realizationRingUnit_locallyBijective (J.over U) R).2
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (realizationRingUnit (J.over U) R) (sliceConstantComparison J R U M)
  dsimp only [sliceConstantComparison] at h
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

private theorem sliceConstantComparison_isIso (M : ModuleCat.{max u v} R) :
    IsIso (sliceConstantComparison J R U M) := by
  let P := ((siteConstantModulePresheafGeneral (C := Over U) R).obj M).presheaf
  let t := toSheafify J ((siteConstantModulePresheafGeneral (C := C) R).obj M).presheaf
  let tU := Functor.whiskerLeft (Over.forget U).op t
  let g := (SheafOfModules.toSheaf _).map (sliceConstantComparison J R U M)
  have : Presheaf.IsLocallyInjective (J.over U) tU :=
    Presheaf.isLocallyInjective_whisker (J.over U) J (Over.forget U) t
  have : Presheaf.IsLocallySurjective (J.over U) tU :=
    Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U) t
  have hi : Presheaf.IsLocallyInjective (J.over U) (toSheafify (J.over U) P ≫ g.hom) := by
    rw [sliceConstantComparison_fac]
    infer_instance
  have hs : Presheaf.IsLocallySurjective (J.over U) (toSheafify (J.over U) P ≫ g.hom) := by
    rw [sliceConstantComparison_fac]
    infer_instance
  have : IsIso g := (Sheaf.isLocallyBijective_iff_isIso g).mp
    ⟨(Presheaf.comp_isLocallyInjective_iff (J.over U) (toSheafify (J.over U) P) g.hom).mp hi,
      (Presheaf.comp_isLocallySurjective_iff (J.over U) (toSheafify (J.over U) P) g.hom).mp hs⟩
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)

/-- Constants commute with slice restriction, including their coefficient action.
Source: Stacks Project, Modules on Sites, Sections 03CY and 03DH; HRS (3.1).
(blueprint: lem-zl-commutative-constant-slice-restriction).

Proof: a covering sieve in the slice is a covering sieve on its underlying object.
Consequently restriction commutes with sheafification: the locally bijective unit
of a constant module presheaf remains locally bijective after restriction.
The constant-ring comparison carries each constant scalar r to the same section r.
Thus the identity on constant module presheaves is linear after the indicated
coefficient transport. The module sheafification universal property extends it
uniquely in both directions. Their composites are identities because they are
identities on constant presheaf sections. The same uniqueness proves naturality
in the ordinary R-module. If the empty sieve covers an object, both sheaves have
zero sections there; this argument therefore needs no nonemptiness assumption. -/
theorem commutative_constant_slice_restriction :
    Nonempty (commutativeSiteConstantModuleFunctor J R ⋙
      commutativeConstantSliceRestriction J R U ≅
        commutativeSiteConstantModuleFunctor (J.over U) R) := by
  have (M : ModuleCat.{max u v} R) : IsIso (sliceConstantComparison J R U M) :=
    sliceConstantComparison_isIso J R U M
  refine ⟨(NatIso.ofComponents (fun M ↦ asIso (sliceConstantComparison J R U M)) ?_).symm⟩
  intro M N f
  let := (realizationRingUnit_locallyBijective (J.over U) R).1
  let := (realizationRingUnit_locallyBijective (J.over U) R).2
  apply (PresheafOfModules.sheafificationHomEquiv
    (realizationRingUnit (J.over U) R)).injective
  apply (PresheafOfModules.toPresheaf _).map_injective
  simp only [PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def]
  change toSheafify (J.over U)
      ((siteConstantModulePresheafGeneral (C := Over U) R).obj M).presheaf ≫
      (((SheafOfModules.toSheaf _).map
        ((commutativeSiteConstantModuleFunctor (J.over U) R).map f)).hom ≫
        ((SheafOfModules.toSheaf _).map (sliceConstantComparison J R U N)).hom) =
    toSheafify (J.over U)
      ((siteConstantModulePresheafGeneral (C := Over U) R).obj M).presheaf ≫
      (((SheafOfModules.toSheaf _).map (sliceConstantComparison J R U M)).hom ≫
        ((SheafOfModules.toSheaf _).map
          ((commutativeConstantSliceRestriction J R U).map
            ((commutativeSiteConstantModuleFunctor J R).map f))).hom)
  simp only [← Category.assoc]
  rw [sliceConstantComparison_fac]
  have hn := toSheafify_naturality (J.over U)
    ((PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := Over U) R).map f))
  change _ = toSheafify (J.over U)
      ((siteConstantModulePresheafGeneral (C := Over U) R).obj M).presheaf ≫
      ((SheafOfModules.toSheaf _).map
        ((commutativeSiteConstantModuleFunctor (J.over U) R).map f)).hom at hn
  rw [← hn, Category.assoc]
  change (PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := Over U) R).map f) ≫
      (toSheafify (J.over U)
        ((siteConstantModulePresheafGeneral (C := Over U) R).obj N).presheaf ≫
        ((SheafOfModules.toSheaf _).map (sliceConstantComparison J R U N)).hom) = _
  rw [sliceConstantComparison_fac]
  ext V x
  exact ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality J
      ((PresheafOfModules.toPresheaf _).map
        ((siteConstantModulePresheafGeneral (C := C) R).map f)))
      ((Over.forget U).op.obj V)) x

end CategoryTheory
