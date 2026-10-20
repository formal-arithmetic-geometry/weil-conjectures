/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Sheaf.Algebra.Homology.TermwiseTorAcyclicDerivedTensor
import WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
import all WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivRawTransportIso
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-! # Termwise Tor acyclicity for the universal base-tensor comparison

Source: Stacks Project, Tag 08IB, local affine comparison, and Tag 06Y6.
(blueprint: lem-pc-termwise-tor-acyclic-base-comparison).
-/

@[expose] public section

set_option autoImplicit false

universe uR uA uB uD v w

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MonoidalCategory CategoryTheory.Functor

namespace ModuleCat.BaseDerivedTensorCohomologyModel

private theorem counit_isIso_of_tor_acyclic
    {S T : Type v} [CommRing S] [CommRing T] [Algebra S T]
    [HasDerivedCategory.{w} (ModuleCat.{v} S)]
    [HasDerivedCategory.{w} (ModuleCat.{v} T)]
    (K : CochainComplex (ModuleCat.{v} S) ℤ)
    (hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n))
    (ht : ∀ (n : ℤ) (i : ℕ), 0 < i →
      IsZero (((Tor' (ModuleCat.{v} S) i).obj (K.X n)).obj (of S T)))
    (L : DerivedCategory (ModuleCat.{v} S) ⥤ DerivedCategory (ModuleCat.{v} T))
    (ε : DerivedCategory.Qh ⋙ L ⟶
      (extendScalars (algebraMap S T)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hL : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso _ (.up ℤ))) :
    IsIso (ε.app ((HomotopyCategory.quotient _ _).obj K)) := by
  classical
  have (N : ModuleCat.{v} S) : PreservesColimitsOfShape ℤ
      ((curriedTensor (ModuleCat.{v} S)).flip.obj N) :=
    inferInstanceAs (PreservesColimitsOfShape ℤ (tensorRight N))
  have : HasExactColimitsOfShape ℤ (ModuleCat.{v} S) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{v} S)
      (AsSmall.equiv (C := ℤ)).symm
  let Λ := (Classical.choice (inferInstance :
    Abelian.HasFunctorialFlatResolution (ModuleCat.{v} S))).reduced
  let P := Λ.resolutionFunctor.obj K
  let s : P ⟶ K := Λ.resolutionNatTrans.app K
  have hs : QuasiIso s := inferInstance
  have hP := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le K
  have hp := scalarExtensionCounit_isIso_of_kFlat (algebraMap S T) P
    (by
      intro N hN
      have h := (HomotopyCategory.kFlat_iff_preserves_acyclic _).1
        ((HomotopyCategory.kFlat_quotient_obj_iff P).2 hP)
        ((HomotopyCategory.quotient _ _).obj N)
        ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic N).2 hN)
      exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1 h.2)
    L ε hL
  have hright := (CochainComplex.quasiIso_tensor_of_termwise_tor_acyclic K hb ht
    ⟨P, hP⟩ s hs).1
  let b : (restrictScalars (algebraMap S T)).obj (of T T) ≅ of S T :=
    (show (restrictScalars (algebraMap S T)).obj (of T T) ≃ₗ[S] of S T from
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r x ↦ (@Algebra.smul_def S T _ _ _ r x).symm }).toModuleIso
  let c₀ : extendScalars (algebraMap S T) ⋙ restrictScalars (algebraMap S T) ≅
      tensorLeft (of S T) :=
    (curriedTensor (ModuleCat.{v} S)).mapIso b
  let c₁ : tensorLeft (of S T) ≅ (tensoringRight (ModuleCat.{v} S)).obj (of S T) :=
    BraidedCategory.tensorLeftIsoTensorRight _
  let c := Functor.mapHomologicalComplexCompIso (c₀ ≪≫ c₁) (.up ℤ)
  have hext : QuasiIso
      (((extendScalars (algebraMap S T)).mapHomologicalComplex (.up ℤ)).map s) := by
    apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
      (restrictScalars (algebraMap S T))).1
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk (c.app P) (c.app K) (by exact (c.hom.naturality s).symm))).2 hright
  have : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 hs
  have : IsIso (DerivedCategory.Q.map
      (((extendScalars (algebraMap S T)).mapHomologicalComplex (.up ℤ)).map s)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hext
  have : IsIso ((DerivedCategory.Qh ⋙ L).map
      ((HomotopyCategory.quotient _ _).map s)) := by
    change IsIso (L.map (DerivedCategory.Q.map s))
    infer_instance
  have : IsIso (((extendScalars (algebraMap S T)).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).map ((HomotopyCategory.quotient _ _).map s)) := by
    change IsIso (DerivedCategory.Q.map
      (((extendScalars (algebraMap S T)).mapHomologicalComplex (.up ℤ)).map s))
    infer_instance
  rw [← isIso_comp_left_iff ((DerivedCategory.Qh ⋙ L).map
    ((HomotopyCategory.quotient _ _).map s)),
    ε.naturality ((HomotopyCategory.quotient _ _).map s)]
  infer_instance

private noncomputable def ulift_scalar_iso
    {S : Type uR} {T : Type uB} [CommRing S] [CommRing T] (φ : S →+* T) :
    restrictScalars.{max uR uB v}
        (ULift.ringEquiv.symm : S ≃+* ULift.{max uR uB v} S).toRingHom ⋙
      (extendScalars.{uR, uB, max uR uB v} φ ⋙ restrictScalars
        (ULift.ringEquiv : ULift.{max uR uB v} T ≃+* T).toRingHom) ≅
          extendScalars (RingHom.ulift.{max uR uB v, max uR uB v} φ) := by
  let eS : ULift.{max uR uB v} S ≃+* S := ULift.ringEquiv
  let eT : ULift.{max uR uB v} T ≃+* T := ULift.ringEquiv
  let adj := (restrictScalarsEquivalenceOfRingEquiv.{_, _, max uR uB v} eS.symm).toAdjunction.comp
    ((extendRestrictScalarsAdj.{max uR uB v, _, _} φ).comp
      (restrictScalarsEquivalenceOfRingEquiv.{_, _, max uR uB v} eT).toAdjunction)
  let r : restrictScalars.{max uR uB v} (RingHom.ulift.{max uR uB v, max uR uB v} φ) ≅
      (restrictScalars eT.symm.toRingHom ⋙ restrictScalars φ) ⋙
        restrictScalars eS.toRingHom :=
    restrictScalarsComp eS.toRingHom (eT.symm.toRingHom.comp φ) ≪≫
      isoWhiskerRight (restrictScalarsComp φ eT.symm.toRingHom) _
  exact (adj.ofNatIsoRight r.symm).leftAdjointUniq
    (extendRestrictScalarsAdj.{max uR uB v, _, _}
      (RingHom.ulift.{max uR uB v, max uR uB v} φ))

attribute [local instance] ULift.algebra'

variable {R : Type uR} {A : Type uA} {B : Type uB} {D : Type uD}
  [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uA uB uD v} R)]
  [HasDerivedCategory.{w} (ModuleCat.{max uR uA uB uD v} B)]
  {Q : CochainComplex (ModuleCat.{max uR uA uB uD v} A) ℤ}

/-- Source: Stacks Project, Tag 08IB, affine Tor-independent comparison;
Tag 06Y6, computation of a derived functor on K-flat resolutions.
(blueprint: lem-pc-termwise-tor-acyclic-base-comparison).

Proof: Lift R, B and each term to the common carrier universe. The equivalences
along the ring isomorphisms ULift R ≃ R and ULift B ≃ B preserve homology and
intertwine scalar extension with tensoring by ULift B (tensor symmetry accounts
for its placement on the right). Apply the termwise Tor-acyclic comparison to a
K-flat resolution of the restricted bounded complex. Its tensor augmentation is
a quasi-isomorphism. The left-derived counit computed on this resolution is
therefore an isomorphism; uniqueness of the universal derived pair transports
this to M.counit. More explicitly, in the naturality square for the resolution
augmentation, its image under the localized derived functor is invertible,
the counit at the K-flat source is invertible by
scalarExtensionCounit_isIso_of_kFlat after the same universe transport, and the
ordinary-tensor image of
the augmentation is invertible by termwise Tor acyclicity. Thus the fourth side,
the counit at Q, is invertible. The argument also applies to the zero complex,
zero rings and arbitrary bounds, including m > n. No localization or finite
projectivity is required. -/
theorem counit_isIso_of_termwise_tor_acyclic
    (M : BaseDerivedTensorCohomologyModel R A B Q D)
    (hbounded : ∃ m n : ℤ, ∀ i : ℤ, i < m ∨ n < i → IsZero (Q.X i))
    (hTor : ∀ (n : ℤ) (i : ℕ), 0 < i →
      IsZero (((CategoryTheory.Tor'
        (ModuleCat.{max uR uA uB uD v} (ULift.{max uR uA uB uD v} R)) i).obj
        (@ModuleCat.of (ULift.{max uR uA uB uD v} R) _
          (ULift.{max uR uA uB uD v} (Q.X n)) inferInstance
          (Module.compHom _ (algebraMap (ULift.{max uR uA uB uD v} R)
            (ULift.{max uR uA uB uD v} A))))).obj
        (ModuleCat.of (ULift.{max uR uA uB uD v} R)
          (ULift.{max uR uA uB uD v} B)))) :
    IsIso (M.counit.app ((HomotopyCategory.quotient _ _).obj
      (((restrictScalars.{max uR uA uB uD v} (algebraMap R A)).mapHomologicalComplex
        (.up ℤ)).obj Q))) := by
  classical
  let eR : ULift.{max uR uA uB uD v} R ≃+* R := ULift.ringEquiv
  let eB : ULift.{max uR uA uB uD v} B ≃+* B := ULift.ringEquiv
  let SR := restrictScalars.{max uR uA uB uD v} eR.symm.toRingHom
  let TR := restrictScalars.{max uR uA uB uD v} eR.toRingHom
  let TB := restrictScalars.{max uR uA uB uD v} eB.toRingHom
  let := HasDerivedCategory.standard
    (ModuleCat.{max uR uA uB uD v} (ULift.{max uR uA uB uD v} R))
  let := HasDerivedCategory.standard
    (ModuleCat.{max uR uA uB uD v} (ULift.{max uR uA uB uD v} B))
  let SD := SR.mapDerivedCategory
  let TD := TB.mapDerivedCategory
  have : SD.IsEquivalence :=
    ModuleCat.derived_equivalence (restrictScalarsEquivalenceOfRingEquiv eR.symm)
  have : TD.IsEquivalence :=
    ModuleCat.derived_equivalence (restrictScalarsEquivalenceOfRingEquiv eB)
  let F := extendScalars.{uR, uB, max uR uA uB uD v} (algebraMap R B)
  let Fup := extendScalars.{max uR uA uB uD v, max uR uA uB uD v,
    max uR uA uB uD v} (RingHom.ulift.{max uR uA uB uD v, max uR uA uB uD v} (algebraMap R B))
  let Sh := SR.mapHomotopyCategory (.up ℤ)
  have : Sh.IsEquivalence := by
    let e := restrictScalarsEquivalenceOfRingEquiv eR.symm
    let Th := TR.mapHomotopyCategory (.up ℤ)
    let iu : Sh ⋙ Th ≅ 𝟭 _ :=
      Functor.mapHomotopyCategoryCompIso e.unitIso.symm (.up ℤ) ≪≫
        Functor.mapHomotopyCategoryIdIso _ _
    let ic : Th ⋙ Sh ≅ 𝟭 _ :=
      Functor.mapHomotopyCategoryCompIso e.counitIso (.up ℤ) ≪≫
        Functor.mapHomotopyCategoryIdIso _ _
    exact (CategoryTheory.Equivalence.mk Sh Th iu.symm ic).isEquivalence_functor
  let L := M.derived
  let ε := M.counit
  let η := (Functor.associator Sh DerivedCategory.Qh L).hom ≫ whiskerLeft Sh ε
  have hKan : L.IsRightKanExtension ε :=
    let := M.universal
    Functor.IsLeftDerivedFunctor.isRightKanExtension L ε
      (HomotopyCategory.quasiIso (ModuleCat.{max uR uA uB uD v} R) (.up ℤ))
  let _ := hKan
  have hη := (Functor.isRightKanExtension_iff_precomp L Sh ε).1 hKan
  let κ := (Functor.associator DerivedCategory.Qh SD L).inv ≫
    whiskerRight SR.mapDerivedCategoryFactorsh.hom L ≫ η
  have hκ := (Functor.isRightKanExtension_iff_postcomp₁ SD
    SR.mapDerivedCategoryFactorsh η).1 hη
  let _ := hκ
  let χ : ((Sh ⋙ (F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)) ⋙ TD) ≅
      Fup.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft Sh (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ TB.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight
      ((Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (SR ⋙ F)) (.up ℤ)) _ ≪≫
        Functor.mapHomotopyCategoryCompIso
          (Functor.associator SR F TB ≪≫ ulift_scalar_iso.{uR, uB, max uA uD v} (algebraMap R B))
          (.up ℤ)) _
  let ζ := (Functor.associator DerivedCategory.Qh (SD ⋙ L) TD).inv ≫ whiskerRight κ TD
  let εup := ζ ≫ χ.hom
  have hζ := ModuleCat.kan_postcomp_equivalence DerivedCategory.Qh _ (SD ⋙ L) TD κ
  have hu : ((SD ⋙ L) ⋙ TD).IsLeftDerivedFunctor εup
      (HomotopyCategory.quasiIso
        (ModuleCat.{max uR uA uB uD v} (ULift.{max uR uA uB uD v} R)) (.up ℤ)) := by
    constructor
    exact (Functor.isRightKanExtension_iff_of_iso₂ ζ εup χ (Iso.refl _) (by
      simp [εup])).1 hζ
  let X := ((restrictScalars.{max uR uA uB uD v} (algebraMap R A)).mapHomologicalComplex
    (.up ℤ)).obj Q
  let Kup := (TR.mapHomologicalComplex (.up ℤ)).obj X
  have hb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (Kup.X n) := by
    obtain ⟨a, b, hab⟩ := hbounded
    refine ⟨a, b, fun n hn ↦ ?_⟩
    exact TR.map_isZero
      ((restrictScalars (algebraMap R A)).map_isZero (hab n hn))
  have ht : ∀ (n : ℤ) (i : ℕ), 0 < i →
      IsZero (((Tor'
        (ModuleCat.{max uR uA uB uD v} (ULift.{max uR uA uB uD v} R)) i).obj
        (Kup.X n)).obj (of (ULift.{max uR uA uB uD v} R)
          (ULift.{max uR uA uB uD v} B))) := by
    intro n i hi
    let e : Kup.X n ≅
        (@ModuleCat.of (ULift.{max uR uA uB uD v} R) _
          (ULift.{max uR uA uB uD v} (Q.X n)) inferInstance
          (Module.compHom _ (algebraMap (ULift.{max uR uA uB uD v} R)
            (ULift.{max uR uA uB uD v} A)))) :=
      (show Kup.X n ≃ₗ[ULift.{max uR uA uB uD v} R] _ from
        { toFun := ULift.up
          invFun := ULift.down
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }).toModuleIso
    exact (hTor n i hi).of_iso
      (Functor.mapIso
        (((tensoringRight _).obj (of (ULift.{max uR uA uB uD v} R)
          (ULift.{max uR uA uB uD v} B))).leftDerived i) e)
  have hc := counit_isIso_of_tor_acyclic Kup hb ht ((SD ⋙ L) ⋙ TD) εup hu
  have hcomp : IsIso (TD.map (ε.app (Sh.obj ((HomotopyCategory.quotient _ _).obj Kup)))) := by
    simpa only [εup, ζ, κ, η, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      Functor.map_comp, isIso_comp_left_iff, isIso_comp_right_iff] using hc
  have he : IsIso (ε.app (Sh.obj ((HomotopyCategory.quotient _ _).obj Kup))) := by
    let _ := hcomp
    exact isIso_of_reflects_iso _ TD
  let iC := ((restrictScalarsEquivalenceOfRingEquiv eR.symm).mapHomologicalComplex
    (.up ℤ)).counitIso.app X
  let iH := (SR.mapHomotopyCategoryFactors (.up ℤ)).app Kup ≪≫
    (HomotopyCategory.quotient _ _).mapIso iC
  exact (NatTrans.isIso_app_iff_of_iso ε iH).1 he

end ModuleCat.BaseDerivedTensorCohomologyModel
