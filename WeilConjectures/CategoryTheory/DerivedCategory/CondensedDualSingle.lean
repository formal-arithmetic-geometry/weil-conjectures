/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.RightDual
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LocallyFreeDualizable

/-! # Derived dual of a dualizable sheaf in one degree

The single-degree base case of the bounded lisse duality argument, stated for any
Grothendieck monoidal coefficient category, hence also native condensed modules.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace DerivedCategory
variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [HasDerivedCategory.{v} A] [Abelian.HasFunctorialFlatResolution A]

/-- The dual of a dualizable object placed in degree `n` lies in degree `-n`.
Source: `lem-fin-lisse-field-dual`, the single-degree base case of Step 2 of
`thm-a1-curve-perverse-heart`
(blueprint: lem-per-condensed-dual-single).

Proof: represent the single object by the single cochain complex `Q`. Every term
is either the given dualizable object or zero. Choose its canonical internal dual
as right dual. The bounded-complex exact-pairing theorem pairs `Q Q` with the
termwise dual complex. Swap the pairing using the derived braiding and identify
internal Hom into the unit with the resulting left dual. The termwise dual is
supported in degree `-n`; its sole term is the internal dual of the original
object. The argument also covers the zero object.
-/
theorem nonempty_ihom_single_unit (E : A) (hE : IsDualizable E) (n : ℤ) :
    Nonempty ((ihom ((singleFunctor A n).obj E)).obj (𝟙_ _) ≅
      (singleFunctor A (-n)).obj ((ihom E).obj (𝟙_ _))) := by
  classical
  let Q := (HomologicalComplex.single A (ComplexShape.up ℤ) n).obj E
  have hc (F : A) (hF : IsDualizable F) :
      Nonempty (ExactPairing ((ihom F).obj (𝟙_ _)) F) := by
    obtain ⟨_⟩ := hF
    let : ExactPairing Fᘁ F := BraidedCategory.exactPairing_swap F Fᘁ
    exact ⟨exactPairingCongrLeft (MonoidalClosed.ihomObjUnitIso Fᘁ F)⟩
  have hl (m : ℤ) : IsDualizable (Q.X m) := by
    by_cases hm : m = n
    · subst hm
      exact hE.of_iso (HomologicalComplex.singleObjXSelf _ _ _).symm
    · exact ⟨hasRightDualOfIsZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ hm)⟩
  let _ (m : ℤ) : HasRightDual (Q.X m) :=
    { rightDual := (ihom (Q.X m)).obj (𝟙_ _)
      exact := letI := (hc _ (hl m)).some
        BraidedCategory.exactPairing_swap _ _ }
  obtain ⟨_⟩ := nonempty_exactPairing_Q_obj_rightDual Q n n
  obtain ⟨_⟩ := nonempty_braidedCategory A
  let := BraidedCategory.exactPairing_swap (DerivedCategory.Q.obj Q)
    (DerivedCategory.Q.obj (CochainComplex.rightDual Q))
  let e : (singleFunctor A n).obj E ≅ DerivedCategory.Q.obj Q :=
    (singleFunctorIsoCompQ A n).app E
  obtain ⟨M, ⟨eM⟩⟩ := CochainComplex.exists_iso_single (CochainComplex.rightDual Q) (-n)
  exact ⟨((MonoidalClosed.internalHom).mapIso e.op.symm).app (𝟙_ _) ≪≫
    MonoidalClosed.ihomObjUnitIso (DerivedCategory.Q.obj (CochainComplex.rightDual Q)) _ ≪≫
    DerivedCategory.Q.mapIso eM ≪≫ ((singleFunctorIsoCompQ A (-n)).app M).symm ≪≫
    (singleFunctor A (-n)).mapIso
      ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (-n) M).symm ≪≫
        (HomologicalComplex.eval _ _ (-n)).mapIso eM.symm ≪≫
        ((MonoidalClosed.internalHom).mapIso (HomologicalComplex.singleObjXIsoOfEq
          (ComplexShape.up ℤ) n E (-(-n)) (neg_neg n)).op).symm.app (𝟙_ _))⟩

/-- Ordinary linear duals of native lisse modules are lisse and detect zero.
Source: the finite-free dual calculation in Step 2 of `thm-a1-curve-perverse-heart`
(blueprint: lem-per-condensed-dual-single).

Proof: normalized local freeness is equivalent to raw local freeness. Its chosen
right dual is locally free by pulling its exact pairing to each finite free
trivialization. In a braided closed category the ordinary internal dual is that
right dual. Swapping the exact pairing identifies its internal dual back with
the original module. Internal Hom out of a zero object is zero, so these two
identifications prove both directions of zero detection, including rank zero.
-/
theorem lisse_dual_properties
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    (E : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hE : IsLisseCoefficientModule Λ E) :
    IsLisseCoefficientModule Λ ((ihom E).obj (𝟙_ _)) ∧
      (IsZero ((ihom E).obj (𝟙_ _)) ↔ IsZero E) := by
  have hraw : IsLocallyFree (condensedRingObj Λ X) E :=
    (isLocallyFree_iff E).mpr hE
  obtain ⟨_⟩ := hraw.isDualizable
  let : ExactPairing Eᘁ E := BraidedCategory.exactPairing_swap E Eᘁ
  let e : (ihom E).obj (𝟙_ _) ≅ Eᘁ := MonoidalClosed.ihomObjUnitIso Eᘁ E
  have hd : IsLocallyFree (condensedRingObj Λ X) ((ihom E).obj (𝟙_ _)) :=
    IsLocallyFree.of_iso e.symm hraw.of_exactPairing
  refine ⟨(isLocallyFree_iff _).mp hd, ?_⟩
  have hz {F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)} (hF : IsZero F) : IsZero ((ihom F).obj (𝟙_ _)) := by
    rw [IsZero.iff_id_eq_zero]
    apply MonoidalClosed.uncurry_injective
    have ht : IsZero (F ⊗ (ihom F).obj (𝟙_ _)) := by
      rw [IsZero.iff_id_eq_zero, ← id_whiskerRight, hF.eq_of_src (𝟙 F) 0,
        MonoidalPreadditive.zero_whiskerRight]
    exact ht.eq_of_src _ _
  constructor
  · intro h
    let ed : (ihom ((ihom E).obj (𝟙_ _))).obj (𝟙_ _) ≅ E :=
      ((MonoidalClosed.internalHom).mapIso e.symm.op).app (𝟙_ _) ≪≫
        MonoidalClosed.ihomObjUnitIso E Eᘁ
    exact (hz h).of_iso ed.symm
  · exact hz

end DerivedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

end AlgebraicGeometry.ProEtale.CondensedRing
