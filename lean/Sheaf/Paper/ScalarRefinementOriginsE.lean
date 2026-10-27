/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
public import Sheaf.Paper.CompactSupportStrictScalarMate
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.FiniteTorAmplitudeSites
import all Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
import all Sheaf.Paper.ProEtaleConstructibleOrigin

/-! E-side finite etale-origin witnesses for strict scalar refinements.

This is the E component of the origin conjunction used by the strict scalar
refinement theorem. Its proof is the finite-coefficient constructible-origin
argument applied independently at each reduction level.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Retain the original geometric hypotheses even though the levelwise proof needs fewer.
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private def quotientScalars (n : ℕ) :
    ULift.{u + 1} (Padic.coefficientExtensionIntegers l E) →+*
      ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)) :=
  (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
    ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
      (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom)

private theorem constant_projection (X : Scheme.{u}) (n : ℕ) :
    integralConstantToCompletionOfUniverses l E X ≫
      (adicLisseForget X).map
        (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) X) =
      integralConstantQuotientOfUniverses l E X n := by
  unfold PurCompactSupport.projection
  simp only [eqToHom_refl, Category.comp_id]
  change limit.lift _ (integralConstantConeOfUniverses l E X) ≫
      limit.π _ (op n) = _
  exact limit.lift_π _ (op n)

private theorem quotient_unit (X : Scheme.{u}) (n : ℕ) :
    scalarUnit (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X ≫
        (integralConstantQuotientOfUniverses l E X n).hom =
      (Functor.const X.ProEtᵒᵖ).map (RingCat.ofHom (quotientScalars l E n)) ≫
        proEtaleModuleScalarUnit X (Padic.coefficientExtensionRing l E (n + 1)) := by
  change Functor.whiskerRight
      (toSheafify (ProEt.topology X) _ ≫
        (sheafifyMap (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).map (CommRingCat.ofHom (quotientScalars l E n)))))
      (forget₂ CommRingCat RingCat) = _
  rw [← toSheafify_naturality]
  rfl

private def fixedFiniteRestriction (X : Scheme.{u}) (n : ℕ) :
    ordinaryFiniteRestriction l E X n ⋙
        fixedRestriction (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X ≅
      proEtaleModuleRestriction X (Padic.coefficientExtensionRing l E (n + 1)) ⋙
        Sheaf.restrictScalars (ProEt.topology X) (quotientScalars l E n) := by
  apply ringUnitLinearizeIso _ _ _ _ _ (quotientScalars l E n)
    (ordinaryFiniteRestriction l E X n)
    (proEtaleModuleRestriction X (Padic.coefficientExtensionRing l E (n + 1)))
    (Iso.refl _)
  intro M U b m
  have h := ConcreteCategory.congr_hom (congr_app (quotient_unit l E X n) U) b
  change ((integralConstantQuotientOfUniverses l E X n).hom.app U
      ((scalarUnit (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X).app U b)) =
    (proEtaleModuleScalarUnit X (Padic.coefficientExtensionRing l E (n + 1))).app U
      (quotientScalars l E n b) at h
  change HSMul.hSMul (β := M.val.obj U)
    ((integralConstantToCompletionOfUniverses l E X ≫
      (adicLisseForget X).map
        (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) X)).hom.app U
      ((scalarUnit (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X).app U b)) m =
    HSMul.hSMul (β := M.val.obj U)
    ((proEtaleModuleScalarUnit X (Padic.coefficientExtensionRing l E (n + 1))).app U
      (quotientScalars l E n b)) m
  rw [constant_projection]
  exact congrArg (fun z : (integralCoefficientSheaf l E X n).obj.obj U ↦
    HSMul.hSMul (β := M.val.obj U) z m) h

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))]
  [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc

/-- E-side origins, one independently chosen witness at each reduction level.
Source: Stacks 09AK--09AL; auxiliary Step 1 of
`lem-pur-compact-support-strict-scalar-refinement`
(blueprint: lem-pur-compact-support-strict-scalar-refinement-origins-e).
Proof: apply the finite-coefficient constructible-origin theorem independently at each level.
Transport the witness through restriction of scalars.
-/
theorem scalar_refinement_origins_E
    (S : CoefficientDerivedSystemCalculus.{u, u} l E X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (_hM : finiteTorConstructibleIntegral l E X M) :
    ∀ n : ℕ, Nonempty (ScalarEtaleOrigin
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X
      ((ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) X n).obj
        ((reduction l E X S).obj M))) := by
  classical
  intro n
  -- Work with the actual finite reduction, using its fixed-scalar encoding.
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let B := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)
  have : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let Λ := ULift.{u + 1, u} A
  let : TopologicalSpace Λ := ⊥
  let : DiscreteTopology Λ := ⟨rfl⟩
  let Q := (scalarReductionDerivedExtension.{u, u} l E X n).obj M
  let U := proEtaleModuleRestriction X A
  let V := fixedRestriction B X
  have : U.IsEquivalence := proEtaleModuleRestriction_isEquivalence X A
  have : U.Additive := Functor.additive_of_preserves_binary_products U
  have : V.IsEquivalence := fixedRestriction_equivalence B X
  have : V.Additive := fixedRestriction_additive B X
  obtain ⟨a, b, hab, hlevels⟩ := _hM.1.2
  have hc (q : ℤ) : ProEtale.IsConstructible Λ
      ((DerivedCategory.homologyFunctor _ q).obj (U.mapDerivedCategory.obj Q)) := by
    exact ProEtale.isConstructible_of_iso
      ((U.mapDerivedCategoryHomologyFunctorIso q).app Q)
      ((proEtaleModuleRestriction_constructible_iff X A _).mp ((hlevels n).1.2 q))
  have hz (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj Q) := by
    by_contra hn
    have hbound := (hlevels n).2 hn
    rcases hq with hq | hq
    · exact (not_lt_of_ge hbound.1) hq
    · exact (not_lt_of_ge hbound.2) hq
  -- The existing constructible-origin proof supplies a bounded etale antecedent.
  obtain ⟨L, hL, ⟨e⟩⟩ := ProEtale.fixedDerivedOrigin X Λ
    (U.mapDerivedCategory.obj Q) hc a b
    (fun q hq ↦ U.isZero_homologyFunctor_mapDerivedCategory_obj (hz q hq))
  have hplus : DerivedCategory.TStructure.t.plus L := by
    obtain ⟨c, d, _, hv⟩ := hL.2
    exact ⟨c, (DerivedCategory.isGE_iff L c).mpr (fun q hq ↦ hv q (Or.inl hq))⟩
  let Lp : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
    ⟨L, hplus⟩
  let ν := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) X
  let W := ProEtale.finiteCoefficientRealization X Λ
  let R := ProEtale.StrictTower.finiteRestriction B X Λ (quotientScalars l E n)
  let T := Sheaf.restrictScalars (ProEt.topology X) (quotientScalars l E n)
  let F := (ProEtale.finiteCoefficientComparison X Λ).mapDerivedCategoryPlus.obj Lp
  have : (ProEtale.StrictTower.C B X Λ (quotientScalars l E n) ⋙
      fixedRestriction B X).Additive :=
    Functor.additive_of_iso (cFixed B X Λ (quotientScalars l E n)).symm
  have : PreservesFiniteLimits (ProEtale.StrictTower.C B X Λ (quotientScalars l E n) ⋙
      fixedRestriction B X) :=
    preservesFiniteLimits_of_natIso (cFixed B X Λ (quotientScalars l E n)).symm
  have : PreservesFiniteColimits (ProEtale.StrictTower.C B X Λ (quotientScalars l E n) ⋙
      fixedRestriction B X) :=
    preservesFiniteColimits_of_natIso (cFixed B X Λ (quotientScalars l E n)).symm
  -- Compare both scalar presentations after the faithful constant-scalar encoding.
  let ce : V.mapDerivedCategory.obj (R.mapDerivedCategory.obj F.obj) ≅
      T.mapDerivedCategory.obj (ν.mapDerivedCategory.obj L) :=
    V.mapDerivedCategory.mapIso (R.mapDerivedCategory.mapIso
      ((Functor.mapDerivedCategoryCompIso ν W).app L)) ≪≫
      (Functor.mapDerivedCategoryCompIso R V).symm.app _ ≪≫
      (Functor.mapDerivedCategoryCompIso W (R ⋙ V)).symm.app
        (ν.mapDerivedCategory.obj L) ≪≫
      (Functor.mapDerivedCategoryNatIso (cFixed B X Λ (quotientScalars l E n))).app
        (ν.mapDerivedCategory.obj L)
  let d := Functor.mapDerivedCategorySquareIso (fixedFiniteRestriction l E X n)
  -- Return to the given calculus and its actual evaluated strict reduction tower.
  let eqv : (finiteRestriction l E X n).obj Q ≅
      (ev B X n).obj ((reduction l E X S).obj M) :=
    ((finiteRestriction l E X n).mapIso ((S.reductionEvaluation n).app M)).symm ≪≫
      ((evaluationRestriction l E X n).app (S.reduction.obj M)).symm
  refine ⟨{ Λ := Λ
            φ := quotientScalars l E n
            F := F
            origin := ⟨Lp, Iso.refl _⟩
            iso := ?_ }⟩
  exact V.mapDerivedCategory.preimageIso
    (ce ≪≫ T.mapDerivedCategory.mapIso e ≪≫ (d.app Q).symm) ≪≫ eqv

end WeilConjectures.PurStrictScalar
