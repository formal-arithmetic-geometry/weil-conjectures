/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSumFlatKFlat
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Algebra.Homology.Single

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison

import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Sites.FlatLocalRelations
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
import Sheaf.Paper.IntrinsicRealizationFlat
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-!
# Flat constant coefficients with closed support

Source: blueprint `lem-pur-kunneth-supported`, support-quotient argument, and its
stage-1 refinement (blueprint: lem-pur-support-quotient-flat).

The two quotients are actual cokernels of the extension-by-zero counits. Restriction
of the constant sheaf to the open complement is canonically the same constant sheaf.
Thus these counits are precisely the arrows induced by the inclusion of the open
object into the final object. The canonical coefficient realizations express ordinary
module-valued sheaves as modules over the constant commutative ring sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency true in
private theorem single_kflat_of_flat
    {D : Type*} [Category* D] [EssentiallySmall.{u + 1} D]
    {J : GrothendieckTopology D} (R : Sheaf J CommRingCat.{u + 1})
    (M : SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))
    (hM : SheafOfModules.IsFlatOnSite (J := J) (R := R) M) :
    CochainComplex.IsKFlatIndependentCoefficients
      ((HomologicalComplex.single _ (.up ℤ) 0).obj M) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  apply SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite R _ 0
  intro i
  by_cases hi : i = 0
  · subst i
    simpa only [HomologicalComplex.single_obj_X_self] using hM
  · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi
    have hf := CategoryTheory.ObjectProperty.flat_of_isZero hz
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm hf.2

variable (A : Type u) [CommRing A] [Finite A]
  {C T : Scheme.{u}} (a : C ⟶ T) [IsClosedImmersion a]

/-- The defining etale arrow, the extension-by-zero counit on the constant ring module.
It sends the generator indexed by a factorization through the open complement to one.
Source: blueprint support quotient (blueprint: lem-pur-support-quotient-flat). -/
def etaleSupportQuotientArrow :=
  (Etale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) a.openComplement.ι).counit.app
      ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))

/-- The defining pro-etale arrow, the same extension-by-zero counit.
Source: blueprint support quotient (blueprint: lem-pur-support-quotient-flat). -/
def proEtaleSupportQuotientArrow :=
  (ProEtale.openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) a.openComplement.ι).counit.app
      ((constantSheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
        (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))

/-- The etale support quotient is the actual cokernel, not a chosen supported object.
Source: blueprint support quotient (blueprint: lem-pur-support-quotient-flat). -/
def etaleSupportQuotient := cokernel (etaleSupportQuotientArrow A a)

/-- The pro-etale support quotient is the actual cokernel of its defining arrow.
Source: blueprint support quotient (blueprint: lem-pur-support-quotient-flat). -/
def proEtaleSupportQuotient := cokernel (proEtaleSupportQuotientArrow A a)

/-- The etale quotient map.
Source: blueprint support quotient (blueprint: lem-pur-support-quotient-flat). -/
def etaleSupportQuotientMap := cokernel.π (etaleSupportQuotientArrow A a)

/-- The pro-etale quotient map.
Source: blueprint support quotient (blueprint: lem-pur-support-quotient-flat). -/
def proEtaleSupportQuotientMap := cokernel.π (proEtaleSupportQuotientArrow A a)

/-- The canonical comparison on the constant ring module. Its adjunct extends the
constant scalar sections, so it sends the pulled-back constant one to constant one.
Source: blueprint comparison normalization (blueprint: lem-pur-support-quotient-flat). -/
def supportQuotientConstantComparison :=
  ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).homEquiv
    ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
      (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))
    ((constantSheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
      (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))).symm
    (((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (Etale.isTerminalMkId T)).homEquiv _ _).symm
        ((toSheafify (ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))).app
              (op (ProEt.mk (𝟙 T)))))

omit [Finite A] in
set_option backward.isDefEq.respectTransparency true in
private theorem support_stalk_quotientMap_isIso
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (ht : t (IsLocalRing.closedPoint Ω) ∈ Set.range a) :
    IsIso ((pointSmallEtale t).sheafFiber.map (etaleSupportQuotientMap A a)) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let F := (constantSheaf T.smallEtaleTopology B).obj
    (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))
  have ht' : t (IsLocalRing.closedPoint Ω) ∉ Set.range a.openComplement.ι := by
    rw [a.range_eq_compl_range_openComplement_ι] at ht
    exact ht
  have hz := Etale.isZero_uliftSheafFiber_openImmersionLowerShriek_obj B
    a.openComplement.ι t ht' ((Etale.openImmersionRestriction B a.openComplement.ι).obj F)
  have hz' := hz.of_iso
    (((pointSmallEtale t).uliftSheafFiberIso.{u + 1} B).app
      ((Etale.openImmersionLowerShriek B a.openComplement.ι).obj
        ((Etale.openImmersionRestriction B a.openComplement.ι).obj F))).symm
  let Φ := (pointSmallEtale t).sheafFiber (A := B)
  change IsIso (Φ.map (cokernel.π (etaleSupportQuotientArrow A a)))
  have hzero : Φ.map (etaleSupportQuotientArrow A a) = 0 := hz'.eq_of_src _ _
  exact CokernelCofork.IsColimit.isIso_π _
    (isColimitOfHasCokernelOfPreservesColimit Φ _) hzero

omit [Finite A] in
set_option backward.isDefEq.respectTransparency true in
private theorem support_stalk_quotient_isZero
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (ht : t (IsLocalRing.closedPoint Ω) ∉ Set.range a) :
    IsZero ((pointSmallEtale t).sheafFiber.obj (etaleSupportQuotient A a)) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  have ht' : Set.range t ⊆ Set.range a.openComplement.ι := by
    rintro _ ⟨x, rfl⟩
    rw [a.range_eq_compl_range_openComplement_ι, Set.notMem_compl_iff] at ht
    simpa only [Subsingleton.elim x (IsLocalRing.closedPoint Ω)] using ht
  let s := IsOpenImmersion.lift a.openComplement.ι t ht'
  have hs : s ≫ a.openComplement.ι = t := IsOpenImmersion.lift_fac _ _ _
  have hiso : IsIso ((Etale.upperStar B a.openComplement.ι).map
      (etaleSupportQuotientArrow A a)) := by
    have hi : IsIso ((Etale.openImmersionRestriction B a.openComplement.ι).map
        (etaleSupportQuotientArrow A a)) := by
      dsimp only [etaleSupportQuotientArrow]
      infer_instance
    exact (NatIso.isIso_map_iff (Etale.upperStarIsoOpenImmersionRestriction B
      a.openComplement.ι) _).mpr hi
  have hmap : IsIso ((pointSmallEtale t).sheafFiber.map
      (etaleSupportQuotientArrow A a)) := by
    rw [← hs]
    let e := Etale.upperStarCompSheafFiberIso B a.openComplement.ι s
    have hi : IsIso (((Etale.upperStar B a.openComplement.ι) ⋙
        (pointSmallEtale s).sheafFiber).map (etaleSupportQuotientArrow A a)) := by
      change IsIso ((pointSmallEtale s).sheafFiber.map
        ((Etale.upperStar B a.openComplement.ι).map (etaleSupportQuotientArrow A a)))
      have := hiso
      let e' := (pointSmallEtale s).sheafFiber.mapIso (asIso
        ((Etale.upperStar B a.openComplement.ι).map (etaleSupportQuotientArrow A a)))
      exact e'.isIso_hom
    exact NatIso.isIso_map_iff e _ |>.mp hi
  exact (isZero_cokernel_of_epi _).of_iso
    (PreservesCokernel.iso (pointSmallEtale t).sheafFiber (etaleSupportQuotientArrow A a))

omit [Finite A] in
private theorem supportQuotient_stalk_clauses
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T) :
    (t (IsLocalRing.closedPoint Ω) ∈ Set.range a →
      ∃ e : (pointSmallEtale t).sheafFiber.obj (etaleSupportQuotient A a) ≅
        ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A),
        (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))).app
            (op (Etale.mk (𝟙 T))) ≫
          (pointSmallEtale t).toPresheafFiber (Etale.mk (𝟙 T))
            (Over.homMk t (Category.comp_id t))
            ((constantSheaf T.smallEtaleTopology
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
                (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))).obj ≫
          (pointSmallEtale t).sheafFiber.map (etaleSupportQuotientMap A a) ≫ e.hom =
            𝟙 _) ∧
    (t (IsLocalRing.closedPoint Ω) ∉ Set.range a →
      IsZero ((pointSmallEtale t).sheafFiber.obj (etaleSupportQuotient A a))) := by
  constructor
  · intro ht
    let B := ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)
    let Φ := pointSmallEtale t
    let c := (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj B)).app
      (op (Etale.mk (𝟙 T))) ≫
      Φ.toPresheafFiber (Etale.mk (𝟙 T)) (Over.homMk t (Category.comp_id t))
        ((constantSheaf T.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj B).obj
    have hc : IsIso c := by
      let U : T.Etale := Etale.mk (𝟙 T)
      let x : Φ.fiber.obj U := Over.homMk t (Category.comp_id t)
      have h₁ : (Φ.presheafFiberConstIso B).inv = Φ.toPresheafFiber U x
          ((Functor.const T.Etaleᵒᵖ).obj B) := by
        have h := Φ.toPresheafFiber_presheafFiberConstIso_hom B U x
        calc
          (Φ.presheafFiberConstIso B).inv = 𝟙 _ ≫ (Φ.presheafFiberConstIso B).inv :=
            (Category.id_comp _).symm
          _ = _ := by rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
      have hcomp : (Φ.presheafFiberConstIso B).inv ≫
          Φ.presheafFiber.map (toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj B)) = c := by
        rw [h₁, Φ.toPresheafFiber_naturality]
        rfl
      rw [← hcomp]
      infer_instance
    have hq : IsIso (Φ.sheafFiber.map (etaleSupportQuotientMap A a)) :=
      support_stalk_quotientMap_isIso A a t ht
    let e : Φ.sheafFiber.obj (etaleSupportQuotient A a) ≅ B :=
      (asIso (c ≫ Φ.sheafFiber.map (etaleSupportQuotientMap A a))).symm
    refine ⟨e, ?_⟩
    change c ≫ Φ.sheafFiber.map (etaleSupportQuotientMap A a) ≫
      inv (c ≫ Φ.sheafFiber.map (etaleSupportQuotientMap A a)) = 𝟙 _
    rw [← Category.assoc, IsIso.hom_inv_id]
  · exact support_stalk_quotient_isZero A a t

omit [Finite A] in
set_option backward.isDefEq.respectTransparency false in
private theorem etale_realization_scalar
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (U : T.Etaleᵒᵖ) (c : ULift.{u + 1, u} A) (x : F.obj.obj U) :
    ((toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app U) c •
        (show ((etaleSumFlatModuleRealization T (ULift.{u + 1, u} A)).obj F).val.obj U
          from x) = c • x := by
  let α := toSheafify T.smallEtaleTopology
    ((Functor.const T.Etaleᵒᵖ).obj (RingCat.of (ULift.{u + 1, u} A)))
  let e := constantModuleHomRingIso T.smallEtaleTopology (ULift.{u + 1, u} A)
  let : T.smallEtaleTopology.PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
    GrothendieckTopology.instPreservesSheafification T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
      (FD := fun B D : CommRingCat.{u + 1} ↦ B →+* D)
      (CD := fun B : CommRingCat.{u + 1} ↦ B)
      (FE := fun B D : RingCat.{u + 1} ↦ B →+* D)
      (CE := fun B : RingCat.{u + 1} ↦ B)
  have h : α.app U c = e.inv.hom.app U
      (((toSheafify T.smallEtaleTopology
        ((Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app U) c) := by
    have hf := sheafComposeIso_inv_fac T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
      ((Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app hf U) c).symm
  change (e.inv.hom.app U _) •
    (show ((etaleConstantModuleFunctor T (ULift.{u + 1, u} A)).obj F).val.obj U
      from x) = c • x
  rw [← h]
  let f := (PresheafOfModules.toSheafify α
    (M₀ := etaleConstantModulePresheaf T (ULift.{u + 1, u} A) F)
    (A := (sheafCompose T.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) AddCommGrpCat.{u + 1})).obj F)
    (𝟙 _)).app U
  exact (f.hom.map_smul c x).symm

omit [Finite A] in
set_option backward.isDefEq.respectTransparency true in
private theorem etale_scalar_lift
    (U : T.Etale) (n : ℕ)
    (a : Fin n → ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1, u} A))).obj.obj (op U)) :
    ∃ S : Sieve U, S ∈ T.smallEtaleTopology U ∧
      ∀ (V : T.Etale) (f : V ⟶ U), S f →
        ∀ i, ∃ c : ULift.{u + 1, u} A,
          ((toSheafify T.smallEtaleTopology
            ((Functor.const T.Etaleᵒᵖ).obj
              (CommRingCat.of (ULift.{u + 1, u} A)))).app (op V)) c =
            (((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
              (CommRingCat.of (ULift.{u + 1, u} A))).obj.map f.op) (a i) := by
  induction n with
  | zero => exact ⟨⊤, T.smallEtaleTopology.top_mem U, fun _ _ _ i ↦ Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨S, hS, hs⟩ := ih (fun i ↦ a i.succ)
    let α := toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))
    let Z := Presheaf.imageSieve α (a 0)
    refine ⟨Z ⊓ S, T.smallEtaleTopology.intersection_covering
      (Presheaf.imageSieve_mem _ _ _) hS, ?_⟩
    intro V f hf
    refine Fin.cases ?_ (fun i ↦ hs V f hf.2 i)
    exact hf.1

private def etale_relationSieve
    (N : SheafOfModules.{u + 1} ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1, u} A)))))
    {U : T.Etale} {n : ℕ}
    (a : Fin n → ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1, u} A))).obj.obj (op U))
    (s : Fin n → N.val.obj (op U)) : Sieve U where
  arrows V f := ∃ (l : ℕ)
    (b : Fin n → Fin l → ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1, u} A))).obj.obj (op V))
    (t : Fin l → N.val.obj (op V)),
    (∀ i, N.val.map f.op (s i) = ∑ j, b i j • t j) ∧
    (∀ j, ∑ i, (((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1, u} A))).obj.map f.op) (a i) * b i j = 0)
  downward_closed := by
    rintro V W f ⟨l, b, t, hs, ha⟩ g
    refine ⟨l, (fun i j ↦ (((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1, u} A))).obj.map g.op) (b i j)),
      (fun j ↦ N.val.map g.op (t j)), ?_, ?_⟩
    · intro i
      simp only [op_comp, N.val.map_comp_apply, hs, map_sum, N.val.map_smul]
      rfl
    · intro j
      simp only [op_comp, Functor.map_comp_apply, ← map_mul, ← map_sum, ha, map_zero]

set_option backward.isDefEq.respectTransparency false in
private theorem etale_realization_flat
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (hF : ObjectProperty.flat F) :
    SheafOfModules.IsFlatOnSite (J := T.smallEtaleTopology) (R :=
      (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} A)))
      ((etaleSumFlatModuleRealization T (ULift.{u + 1, u} A)).obj F) := by
  classical
  let R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
    (CommRingCat.of (ULift.{u + 1, u} A))
  let N := (etaleSumFlatModuleRealization T (ULift.{u + 1, u} A)).obj F
  have hrel := Sheaf.hasLocallyTrivialRelations_of_flat hF
  apply (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, u + 1} R N).mpr
  intro U n a s hs
  let Z := etale_relationSieve A N a s
  refine ⟨Z, ?_, fun V f hf ↦ hf⟩
  obtain ⟨S, hS, hfac⟩ := etale_scalar_lift A U n a
  apply T.smallEtaleTopology.transitive hS
  intro V f hf
  choose c hc using hfac V f hf
  let d : Matrix (Fin 1) (Fin n) (ULift.{u + 1, u} A) := fun _ i ↦ c i
  let y : Fin n → F.obj.obj (op V) := fun i ↦ N.val.map f.op (s i)
  have he : ∀ k, ∑ i, d k i • y i = 0 := by
    intro k
    have h := congrArg (N.val.map f.op) hs
    simp only [map_sum, map_zero, N.val.map_smul] at h
    change ∑ i, c i • y i = 0
    calc
      ∑ i, c i • y i = ∑ i, R.obj.map f.op (a i) •
          (show N.val.obj (op V) from y i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← hc i]
        exact (etale_realization_scalar A F (op V) (c i) (y i)).symm
      _ = 0 := h
  obtain ⟨S', hS', hfac'⟩ := hrel y d he
  apply T.smallEtaleTopology.superset_covering _ hS'
  intro W g hg
  obtain ⟨l, b, t, hb, ht⟩ := hfac' g hg
  let β (W : T.Etaleᵒᵖ) : ULift.{u + 1, u} A →+* R.obj.obj W :=
    ((toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app W).hom
  let t' : Fin l → N.val.obj (op W) := t
  refine ⟨l, (fun i j ↦ β (op W) (b i j)), t', ?_, ?_⟩
  · intro i
    change N.val.map (g ≫ f).op (s i) = ∑ j, β (op W) (b i j) • t' j
    have hi : (show N.val.obj (op W) from F.obj.map g.op (y i)) =
        ∑ j, β (op W) (b i j) • t' j := by
      calc
        (show N.val.obj (op W) from F.obj.map g.op (y i)) =
            (show N.val.obj (op W) from ∑ j, b i j • t j) := ht i
        _ = _ := by
          apply Finset.sum_congr rfl
          intro j _
          exact (etale_realization_scalar A F (op W) (b i j) (t j)).symm
    rw [op_comp, N.val.map_comp_apply]
    exact hi
  · intro j
    have hb' := congrFun (congrFun hb 0) j
    have hz := congrArg (β (op W)) hb'
    simp only [Matrix.mul_apply, Matrix.zero_apply, map_sum, map_mul, map_zero] at hz
    change ∑ i, R.obj.map (g ≫ f).op (a i) * β (op W) (b i j) = 0
    convert hz using 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    change R.obj.map (g ≫ f).op (a i) = β (op W) (c i)
    rw [op_comp, Functor.map_comp_apply, ← hc i]
    exact (NatTrans.naturality_apply (toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))) g.op
      (c i)).symm

omit [Finite A] in
set_option backward.isDefEq.respectTransparency true in
private theorem supportQuotient_fixed_flat :
    ObjectProperty.flat (etaleSupportQuotient A a) := by
  classical
  apply (Etale.flat_iff_forall_flat_sheafFiber_obj _).mpr
  intro Ω _ _ t
  let e := ((pointSmallEtale t).uliftSheafFiberIso.{u + 1}
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).app (etaleSupportQuotient A a)
  by_cases ht : t (IsLocalRing.closedPoint Ω) ∈ Set.range a
  · obtain ⟨q, -⟩ := (supportQuotient_stalk_clauses A a t).1 ht
    exact ObjectProperty.prop_of_iso ObjectProperty.flat (e ≪≫ q).symm
      (ObjectProperty.prop_unit ObjectProperty.flat)
  · exact ObjectProperty.flat_of_isZero
      ((support_stalk_quotient_isZero A a t ht).of_iso e)

omit [Finite A] in
private theorem support_constant_comparison_isIso :
    IsIso (supportQuotientConstantComparison A (T := T)) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let M := ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)
  let adj := ProEtale.comparisonAdjunction B T
  let adjEt := constantSheafAdj T.smallEtaleTopology B (Etale.isTerminalMkId T)
  let adjPro := constantSheafAdj (ProEt.topology T) B
    ((Etale.isTerminalMkId T).isTerminalObj (toProEt T))
  let e := (adjEt.comp adj).leftAdjointUniq adjPro
  have he : e.hom.app M = supportQuotientConstantComparison A (T := T) := by
    apply (adj.homEquiv _ _).injective
    dsimp only [supportQuotientConstantComparison]
    rw [Equiv.apply_symm_apply]
    apply (adjEt.homEquiv _ _).injective
    change (adjEt.comp adj).homEquiv _ _ (e.hom.app M) = _
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app, Equiv.apply_symm_apply]
    rfl
  rw [← he]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem support_comparison_square
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
    let j := a.openComplement.ι
    let D := ProEtale.comparisonUpperStar B T
    let d := ProEtale.openImmersionLowerShriek B j
    let r := Etale.openImmersionRestriction B j
    let c := ProEtale.openImmersionLowerShriekComparisonUpperStarIso B j
    let b := ProEtale.openComparisonRestrictionIso (ULift.{u + 1, u} A) j
    D.map ((Etale.openImmersionLowerShriekAdjunction B j).counit.app F) =
      c.hom.app (r.obj F) ≫ d.map (b.hom.app F) ≫
        (ProEtale.openImmersionLowerShriekAdjunction B j).counit.app (D.obj F) := by
  dsimp only
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let j := a.openComplement.ι
  let D := ProEtale.comparisonUpperStar B T
  let C := ProEtale.comparisonUpperStar B a.openComplement
  let e := Etale.openImmersionLowerShriek B j
  let d := ProEtale.openImmersionLowerShriek B j
  let r := Etale.openImmersionRestriction B j
  let s := ProEtale.openImmersionRestriction B j
  let c := ProEtale.openImmersionLowerShriekComparisonUpperStarIso B j
  let b := ProEtale.openComparisonRestrictionIso (ULift.{u + 1, u} A) j
  let ae := Etale.openImmersionLowerShriekAdjunction B j
  let ad := ProEtale.openImmersionLowerShriekAdjunction B j
  have hu := (ProEtale.openComparison_unit_normalization
    (ULift.{u + 1, u} A) j).2 (r.obj F)
  have h : c.inv.app (r.obj F) ≫ D.map (ae.counit.app F) =
      (ad.homEquiv _ _).symm (b.hom.app F) := by
    apply (ad.homEquiv _ _).injective
    change ad.homEquiv (C.obj (r.obj F)) (D.obj F)
      (c.inv.app (r.obj F) ≫ D.map (ae.counit.app F)) =
      ad.homEquiv (C.obj (r.obj F)) (D.obj F)
        ((ad.homEquiv (C.obj (r.obj F)) (D.obj F)).symm (b.hom.app F))
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    rw [← hu]
    simp only [Functor.map_comp, Category.assoc]
    change C.map (ae.unit.app (r.obj F)) ≫ b.hom.app (e.obj (r.obj F)) ≫
      s.map (c.hom.app (r.obj F)) ≫ s.map (c.inv.app (r.obj F)) ≫
      s.map (D.map (ae.counit.app F)) = b.hom.app F
    rw [← s.map_comp_assoc, Iso.hom_inv_id_app]
    erw [s.map_id, Category.id_comp]
    have hn : C.map (r.map (ae.counit.app F)) ≫ b.hom.app F =
        b.hom.app (e.obj (r.obj F)) ≫ s.map (D.map (ae.counit.app F)) :=
      b.hom.naturality (ae.counit.app F)
    calc
      _ = C.map (ae.unit.app (r.obj F)) ≫
          (C.map (r.map (ae.counit.app F)) ≫ b.hom.app F) :=
        congrArg (fun k ↦ C.map (ae.unit.app (r.obj F)) ≫ k) hn.symm
      _ = _ := by
        rw [← C.map_comp_assoc, ae.right_triangle_components]
        erw [C.map_id, Category.id_comp]
  change D.map (ae.counit.app F) = _
  calc
    _ = c.hom.app (r.obj F) ≫ (c.inv.app (r.obj F) ≫ D.map (ae.counit.app F)) := by
      rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
    _ = c.hom.app (r.obj F) ≫ (ad.homEquiv _ _).symm (b.hom.app F) := by rw [h]; rfl
    _ = _ := by rw [Adjunction.homEquiv_counit]

private theorem supportQuotient_comparison :
    ∃ e : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).obj
          (etaleSupportQuotient A a) ≅ proEtaleSupportQuotient A a,
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).map
          (etaleSupportQuotientMap A a) ≫ e.hom =
        supportQuotientConstantComparison A (T := T) ≫ proEtaleSupportQuotientMap A a := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let j := a.openComplement.ι
  let F := (constantSheaf T.smallEtaleTopology B).obj
    (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))
  let D := ProEtale.comparisonUpperStar B T
  let d := ProEtale.openImmersionLowerShriek B j
  let r := Etale.openImmersionRestriction B j
  let s := ProEtale.openImmersionRestriction B j
  let c := ProEtale.openImmersionLowerShriekComparisonUpperStarIso B j
  let b := ProEtale.openComparisonRestrictionIso (ULift.{u + 1, u} A) j
  let := support_constant_comparison_isIso A (T := T)
  let q := asIso (supportQuotientConstantComparison A (T := T))
  let p := c.app (r.obj F) ≪≫ d.mapIso (b.app F ≪≫ s.mapIso q)
  have h : D.map (etaleSupportQuotientArrow A a) ≫ q.hom =
      p.hom ≫ proEtaleSupportQuotientArrow A a := by
    have h₁ := support_comparison_square A a F
    change D.map (etaleSupportQuotientArrow A a) = _ at h₁
    rw [h₁]
    dsimp only [p, Iso.trans_hom, Functor.mapIso_hom, q, asIso_hom]
    simp only [Category.assoc, Functor.map_comp]
    have hn := (ProEtale.openImmersionLowerShriekAdjunction B j).counit.naturality
      (supportQuotientConstantComparison A (T := T))
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    exact congrArg
      (fun k ↦ c.hom.app (r.obj F) ≫ d.map (b.hom.app F) ≫ k) hn.symm
  let e := PreservesCokernel.iso D (etaleSupportQuotientArrow A a) ≪≫
    cokernel.mapIso _ _ p q h
  refine ⟨e, ?_⟩
  change D.map (cokernel.π _) ≫ _ = _
  dsimp only [e, Iso.trans_hom]
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  simp only [cokernel.mapIso_hom, cokernel.map, cokernel.π_desc]
  rfl

set_option backward.isDefEq.respectTransparency true in
/-- Both support quotients are tensor-flat and K-flat in degree zero. Their etale
geometric stalks are the coefficient ring on the closed subset, normalized by the
quotient of constant one, and zero on its complement. Comparison is uniquely normalized
by the actual quotient maps.

Source: blueprint support-quotient argument and stage-1 refinement
(blueprint: lem-pur-support-quotient-flat).

Proof:
1. Apply the etale open-closed short exact sequence to the constant ring sheaf
(lem-weil-pbc-open-closed-short-exact). Inverse image preserves constant rings
(prop-weil-pbc-inverse-image-modules-exact). Free Yoneda and sheafification identify
its counit with the defining arrow: both send the generator to one
(lem-weil-pbc-free-yoneda-presheaf-module). Thus the cokernel is canonically a_* A_C,
with the quotient map the unit. The pro-etale ringed open-closed sequence gives the
same identification (lem-weil-pbc-proetale-ringed-open-closed); its quasi-compactness
hypothesis is exactly the displayed assumption on the open complement.
2. A_C is a free rank-one module over itself, hence flat. The open-closed flatness
criterion (lem-sfb-open-closed-flatness) makes a_* A_C flat in both topologies.
The degree-zero complex is bounded above with flat terms, hence K-flat by
lem-pc-bounded-above-flat-kflat-site. The canonical realization functors merely express
these same ordinary sheaves in the ringed-site tensor and K-flat definitions.
3. A closed immersion is finite (lem-weil-pbc-closed-immersion-finite). The finite
stalk formula (lem-weil-pbc-finite-stalk-formula-restriction and
lemma-openclosed-stalk-lowerstar) is a product over the geometric fibre: empty off C,
and a singleton on C. The constant-stalk identification
(lem-weil-pbc-constant-sheaf-geometric-stalk) gives zero and A respectively, and the
unit sends the quotient of constant one to one.
4. Free Yoneda and sheafification give Hom(j_V! A_V,N) = N(V), for V=T or its open
complement. The comparison adjunction identifies these representing objects in the
two topologies, preserving their generators and the inclusion arrow. Exact comparison
inverse image (lem-sf-comparison-pullback-exact) therefore gives an isomorphism of the
cokernels with the displayed quotient-map identity. The pulled-back quotient map is
epic, so the normalized map, and thus its isomorphism, is unique. -/
theorem supportQuotient_flat_kflat_stalk_comparison [QuasiCompact a.openComplement.ι] :
    SheafOfModules.IsFlatOnSite
      ((etaleSumFlatModuleRealization T (ULift.{u + 1, u} A)).obj
        (etaleSupportQuotient A a)) ∧
    SheafOfModules.IsFlatOnSite
      ((ProEtale.finiteCoefficientIntrinsicRealization T A).obj
        (proEtaleSupportQuotient A a)) ∧
    CochainComplex.IsKFlatIndependentCoefficients
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        ((etaleSumFlatModuleRealization T (ULift.{u + 1, u} A)).obj
          (etaleSupportQuotient A a))) ∧
    CochainComplex.IsKFlatIndependentCoefficients
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        ((ProEtale.finiteCoefficientIntrinsicRealization T A).obj
          (proEtaleSupportQuotient A a))) ∧
    (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ T),
      ((t (IsLocalRing.closedPoint Ω) ∈ Set.range a) →
        ∃ e : (pointSmallEtale t).sheafFiber.obj (etaleSupportQuotient A a) ≅
          ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A),
          (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
            (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))).app
              (op (Etale.mk (𝟙 T))) ≫
            (pointSmallEtale t).toPresheafFiber (Etale.mk (𝟙 T))
              (Over.homMk t (Category.comp_id t))
              ((constantSheaf T.smallEtaleTopology
                (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
                  (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A))).obj ≫
            (pointSmallEtale t).sheafFiber.map (etaleSupportQuotientMap A a) ≫ e.hom = 𝟙 _) ∧
      ((t (IsLocalRing.closedPoint Ω) ∉ Set.range a) →
        IsZero ((pointSmallEtale t).sheafFiber.obj (etaleSupportQuotient A a)))) ∧
    (∃! e : (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).obj
          (etaleSupportQuotient A a) ≅ proEtaleSupportQuotient A a,
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).map
          (etaleSupportQuotientMap A a) ≫ e.hom =
        supportQuotientConstantComparison A (T := T) ≫ proEtaleSupportQuotientMap A a) := by
  obtain ⟨e, he⟩ := supportQuotient_comparison A a
  have hE := etale_realization_flat A _ (supportQuotient_fixed_flat A a)
  have hfP := ObjectProperty.prop_of_iso ObjectProperty.flat e
    (ProEtale.flat_comparisonUpperStar_obj (supportQuotient_fixed_flat A a))
  have hP := ProEtale.intrinsicRealization_flat T A _ hfP
  refine ⟨hE, hP, single_kflat_of_flat _ _ hE, single_kflat_of_flat _ _ hP,
    fun Ω _ _ t ↦ supportQuotient_stalk_clauses A a t, e, he, ?_⟩
  intro e' he'
  have : Epi (etaleSupportQuotientMap A a) := by
    dsimp only [etaleSupportQuotientMap]
    infer_instance
  apply Iso.ext
  apply (cancel_epi ((ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).map
      (etaleSupportQuotientMap A a))).mp
  exact he'.trans he.symm

end AlgebraicGeometry.Scheme
