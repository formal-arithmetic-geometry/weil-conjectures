/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FinitePerfectQuotientModelData
public import Sheaf.Paper.ConstantRealizationDerivedScalarExtension

/-! Bridge from the chosen completed derived change to constant realization.

Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 0G7E.
(blueprint: lem-weil-pbc-finite-model-derived-change-bridge).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The selected completed derived-change functor agrees with the derived constant
realization extension on the finite model. The comparison is obtained by uniqueness
of left derived functors, after identifying the underlying ordinary tensor functors.
Source: Stacks Project, sites-cohomology.tex, Tags 06YY and 0G7E.
(blueprint: lem-weil-pbc-finite-model-derived-change-bridge). -/
theorem finiteModel_constantScalarExtension_derivedChangeBridge
    (X : Scheme.{t}) {B C : Type t} [CommRing B] [CommRing C]
    (q : B →+* C)
    [(koszulConstantFunctor X B).PreservesZeroMorphisms]
    [(koszulConstantFunctor X C).PreservesZeroMorphisms]
    (P : CochainComplex (ModuleCat.{t} B) ℤ) :
    Nonempty
      ((completedAdicDerivedChange X (adicConstantMap X q)).obj
          (DerivedCategory.Q.obj (finiteModelConstantComplex X B P)) ≅
        (ConstantScalarRealization.derivedExtension (ProEt.topology X)
          (RingHom.ulift.{t + 1, t + 1} q)).obj
          ((commutativeSiteDerivedConstantModuleFunctor (ProEt.topology X)
            (ULift.{t + 1} B)).obj
            (DerivedCategory.Q.obj
              (((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
                ModuleCat.restrictScalars.{t + 1}
                  (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).mapHomologicalComplex
                    (.up ℤ)).obj P)))) := by
  let D := completedAdicChangeData X (adicConstantMap X q)
  let LF := completedAdicDerivedChange X (adicConstantMap X q)
  let ε := D.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose
  let hLF := D.choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose_spec.1
  obtain ⟨_, _, hAdj⟩ :=
    SheafOfModules.sheafRingDerivedCoefficientAdjunction (adicConstantMap X q)
  obtain ⟨a, ha⟩ := hAdj
    (completedAdicChange X (adicConstantMap X q))
    (completedAdicChangeData X (adicConstantMap X q)).choose_spec.choose
    (completedAdicChangeData X (adicConstantMap X q)).choose_spec.choose_spec.choose
  obtain ⟨d, _⟩ := ha.2 LF ε hLF
  let e : LF ≅
      (ConstantScalarRealization.derivedExtension (ProEt.topology X)
        (RingHom.ulift.{t + 1, t + 1} q)) := by
    exact d.leftAdjointUniq
      (ConstantScalarRealization.derivedAdjunction (ProEt.topology X)
        (RingHom.ulift.{t + 1, t + 1} q))
  let F := commutativeSiteConstantModuleFunctor (ProEt.topology X)
      (ULift.{t + 1} B)
  let K := (((ModuleCat.uliftFunctor.{t + 1, t} B ⋙
    ModuleCat.restrictScalars.{t + 1}
      (ULift.ringEquiv : ULift.{t + 1} B ≃+* B).toRingHom).mapHomologicalComplex
        (.up ℤ)).obj P)
  let Kq := (HomotopyCategory.quotient _ (.up ℤ)).obj K
  let M := F.mapDerivedCategory.obj (DerivedCategory.Qh.obj Kq)
  let c : M ≅ DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) :=
    asIso (F.mapDerivedCategoryFactorsh.hom.app Kq)
  let i₀ : LF.obj (DerivedCategory.Q.obj (finiteModelConstantComplex X B P)) ≅ LF.obj M :=
    LF.mapIso c.symm
  have hLF : LF = completedAdicDerivedChange X (adicConstantMap X q) := by
    rfl
  exact ⟨eqToIso (congrArg (fun F ↦ F.obj
      (DerivedCategory.Q.obj (finiteModelConstantComplex X B P))) hLF.symm) ≪≫
    i₀ ≪≫ e.app M⟩
end AlgebraicGeometry.Scheme
