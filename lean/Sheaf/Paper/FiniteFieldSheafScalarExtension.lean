/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf

import Sheaf.Paper.FiniteFieldLocalTensorModel
import Sheaf.Paper.ProEtaleConstantModuleEncoding
import WeilConjectures.SixFunctors.ProEtale.ScalarExtension

/-!
# Finite-field scalar extension of constructible pro-etale complexes

Source: Stacks Project, Tag 093V, lemma-tensor-product-locally-constant;
finite-field coefficient specialization in the Weil conjectures blueprint
(blueprint: lem-sf-finite-field-sheaf-scalar-extension).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

/-- The map of constant coefficient ring sheaves induced by a field homomorphism.
Source: Stacks Project, Tag 093V (blueprint: lem-sf-finite-field-sheaf-scalar-extension). -/
noncomputable def finiteFieldConstantRingMap
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') : adicLisseConstantRing Y (ULift.{u + 1} k) ⟶
      adicLisseConstantRing Y (ULift.{u + 1} k') :=
  (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f))

/-- Tensor extension of pro-etale module sheaves along a finite-field map.
Source: Stacks Project, Tag 093V (blueprint: lem-sf-finite-field-sheaf-scalar-extension). -/
noncomputable def finiteFieldScalarExtension
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') :
    pbcModules Y (adicLisseConstantRing Y (ULift.{u + 1} k)) ⥤
      pbcModules Y (adicLisseConstantRing Y (ULift.{u + 1} k')) :=
  pbcExtend (finiteFieldConstantRingMap Y f)

/-- Scalar extension is additive, hence preserves zero morphisms.
Source: Stacks Project, Tag 093V, lemma-tensor-product-locally-constant;
finite-field coefficient specialization (blueprint: lem-sf-finite-field-sheaf-scalar-extension). -/
noncomputable instance finiteFieldScalarExtension_additive
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') :
    (finiteFieldScalarExtension Y f).Additive :=
  pbcExtend_additive (finiteFieldConstantRingMap Y f)

/-- Termwise application of scalar extension to a cochain complex.
Source: Stacks Project, Tag 010N (blueprint: lem-sf-finite-field-sheaf-scalar-extension). -/
noncomputable def finiteFieldScalarExtensionComplex
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k')
    (C : CochainComplex
      (pbcModules Y (adicLisseConstantRing Y (ULift.{u + 1} k))) ℤ) :
    CochainComplex (pbcModules Y (adicLisseConstantRing Y (ULift.{u + 1} k'))) ℤ :=
  ((finiteFieldScalarExtension Y f).mapHomologicalComplex (ComplexShape.up ℤ)).obj C

private theorem scalarUnit_naturality
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') :
    (proEtaleModuleScalarUnit Y k) ≫
        ((adicLisseForget Y).map (finiteFieldConstantRingMap Y f)).hom =
      Functor.whiskerRight
        ((Functor.const Y.ProEtᵒᵖ).map
          (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))
        (forget₂ CommRingCat RingCat) ≫ proEtaleModuleScalarUnit Y k' := by
  ext U b
  exact ConcreteCategory.congr_hom
    (congr_app (toSheafify_naturality (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).map
        (CommRingCat.ofHom (RingHom.ulift.{u + 1, u + 1} f)))).symm U) b

private noncomputable def restrictionEncodingIso
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') :
    pbcRestrict (finiteFieldConstantRingMap Y f) ⋙ proEtaleModuleRestriction Y k ≅
      proEtaleModuleRestriction Y k' ⋙
        sheafCompose (ProEt.topology Y)
          (ModuleCat.restrictScalars.{u + 1} (RingHom.ulift.{u + 1, u + 1} f)) := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ?_) ?_)) ?_
  · let P := (((pbcRestrict (finiteFieldConstantRingMap Y f) ⋙
        proEtaleModuleRestriction Y k).obj M).obj.obj U)
    let Q := (((proEtaleModuleRestriction Y k' ⋙
        sheafCompose (ProEt.topology Y)
          (ModuleCat.restrictScalars.{u + 1}
            (RingHom.ulift.{u + 1, u + 1} f))).obj M).obj.obj U)
    change P ≅ Q
    refine (show (P : Type (u + 1)) ≃ₗ[ULift.{u + 1} k] Q from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun b m ↦ ?_ }).toModuleIso
    change (((finiteFieldConstantRingMap Y f).hom.app U).hom
      (((proEtaleModuleScalarUnit Y k).app U).hom b)) •
        (show M.val.obj U from m) =
      (((proEtaleModuleScalarUnit Y k').app U).hom ((RingHom.ulift f) b)) •
        (show M.val.obj U from m)
    exact congrArg (fun a ↦ a • (show M.val.obj U from m))
      (ConcreteCategory.congr_hom (congr_app (scalarUnit_naturality Y f) U) b)
  · intro U V a
    ext m
    rfl
  · intro M N a
    ext U m
    rfl

private noncomputable def scalarExtensionEncodingIso
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k']
    (f : k →+* k') :
    finiteFieldScalarExtension Y f ⋙ proEtaleModuleRestriction Y k' ≅
      proEtaleModuleRestriction Y k ⋙
        ProEtale.sheafExtendScalars (RingHom.ulift.{u + 1, u + 1} f) Y := by
  let E := proEtaleModuleEncoding Y k
  let E' := proEtaleModuleEncoding Y k'
  let L := ProEtale.sheafExtendScalars (RingHom.ulift.{u + 1, u + 1} f) Y
  let R := sheafCompose (ProEt.topology Y)
    (ModuleCat.restrictScalars.{u + 1} (RingHom.ulift.{u + 1, u + 1} f))
  let adj := E.toAdjunction.comp
    ((ProEtale.sheafExtendScalarsAdjunction (RingHom.ulift f) Y).comp E'.symm.toAdjunction)
  let eR : E'.functor ⋙ R ⋙ E.inverse ≅ pbcRestrict (finiteFieldConstantRingMap Y f) :=
    (isoWhiskerRight (restrictionEncodingIso Y f).symm E.inverse) ≪≫
      isoWhiskerLeft _ E.unitIso.symm
  let adj' := adj.ofNatIsoRight eR
  let e := (pbcScalarAdjunction (finiteFieldConstantRingMap Y f)).leftAdjointUniq adj'
  exact isoWhiskerRight e E'.functor ≪≫
    isoWhiskerLeft (E.functor ⋙ L) E'.counitIso

private theorem scalarExtension_exact
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k'] (f : k →+* k') :
    PreservesFiniteLimits (finiteFieldScalarExtension Y f) ∧
      PreservesFiniteColimits (finiteFieldScalarExtension Y f) := by
  have := proEtaleModuleRestriction_isEquivalence Y k
  have := proEtaleModuleRestriction_isEquivalence Y k'
  have hflat : (RingHom.ulift.{u + 1, u + 1} f).Flat := by
    let := (RingHom.ulift.{u + 1, u + 1} f).toAlgebra
    exact inferInstanceAs (Module.Flat (ULift.{u + 1} k) (ULift.{u + 1} k'))
  have := ProEtale.preservesFiniteLimits_sheafExtendScalars Y hflat
  have : PreservesFiniteLimits
      (finiteFieldScalarExtension Y f ⋙ proEtaleModuleRestriction Y k') :=
    preservesFiniteLimits_of_natIso (scalarExtensionEncodingIso Y f).symm
  have : (finiteFieldScalarExtension Y f).IsLeftAdjoint :=
    (pbcScalarAdjunction (finiteFieldConstantRingMap Y f)).isLeftAdjoint
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves
    (finiteFieldScalarExtension Y f) (proEtaleModuleRestriction Y k'), inferInstance⟩

private theorem constructible_iso
    (Y : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    {F G : pbcModules Y (adicLisseConstantRing Y A)} (e : F ≅ G)
    (hF : IsConstructibleProEtaleCoefficientModuleSheaf Y A F) :
    IsConstructibleProEtaleCoefficientModuleSheaf Y A G := by
  obtain ⟨S, hn, hS, hF⟩ := hF
  refine ⟨S, hn, hS, fun i ↦ ?_⟩
  obtain ⟨K, hK, hF⟩ := hF i
  refine ⟨K, hK, fun V g hg ↦ ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := hF V g hg
  exact ⟨M, hM, ⟨(SheafOfModules.overFunctor _ V).mapIso
    ((proEtaleModuleInverseImage (S.immersion i)
      (adicLisseConstantRing Y A)).mapIso e.symm) ≪≫ eM⟩⟩

private theorem finite_tensor_model
    {k k' : Type u} [Field k] [Field k'] [Finite k'] (f : k →+* k')
    (M : ModuleCat.{u + 1} (ULift.{u + 1} k)) [Finite M] :
    Finite ((ModuleCat.extendScalars (RingHom.ulift.{u + 1, u + 1} f)).obj M) := by
  let := (RingHom.ulift.{u + 1, u + 1} f).toAlgebra
  have : Module.Finite (ULift.{u + 1} k) M := Module.Finite.of_finite
  change Finite ((ULift.{u + 1} k') ⊗[ULift.{u + 1} k] M)
  have : Module.Finite (ULift.{u + 1} k')
      ((ULift.{u + 1} k') ⊗[ULift.{u + 1} k] M) := inferInstance
  exact Module.finite_of_finite (ULift.{u + 1} k')

set_option linter.unusedVariables false in
/-- Finite-field scalar extension is exact, preserves finite constructibility with the
same local strata and covers, identifies each local model with its tensor extension, and
commutes with all cohomology objects of cochain complexes.

Source: Stacks Project, Tag 093V, lemma-tensor-product-locally-constant; Tags 0GMW,
03EL and 010N (blueprint: lem-sf-finite-field-sheaf-scalar-extension).
Proof: Regard `k'` as a finite `k`-module. A finite basis identifies sheaf tensor
extension with a finite direct sum, proving preservation of kernels and cokernels.
On every stratum and its pro-etale localization, the tensor of a constant sheaf is
the constant sheaf of the tensor module, with the right-factor `k'` action; finite
stalks and the original finite stratification are therefore preserved. Apply the
exact-functor homology comparison to the three consecutive terms of each complex.
The zero and bounded-interval clauses follow termwise, including the case of an
empty stratum or `r = s`.
-/
theorem finiteFieldSheafScalarExtension
    (Y : Scheme.{u}) {k k' : Type u} [Field k] [Field k'] [Finite k] [Finite k']
    (f : k →+* k') :
    PreservesFiniteLimits (finiteFieldScalarExtension Y f) ∧
      PreservesFiniteColimits (finiteFieldScalarExtension Y f) ∧
      (∀ (F : pbcModules Y (adicLisseConstantRing Y (ULift.{u + 1} k))),
        IsConstructibleProEtaleCoefficientModuleSheaf Y (ULift.{u + 1} k) F →
          IsConstructibleProEtaleCoefficientModuleSheaf Y (ULift.{u + 1} k')
            ((finiteFieldScalarExtension Y f).obj F) ∧
          (∀ (S : LocallyClosedStratification Y) (i : Fin S.n)
              (K : Sieve (⊤_ (S.domain i).ProEt)),
            K ∈ ProEt.topology (S.domain i) (⊤_ (S.domain i).ProEt) →
            ∀ (V : (S.domain i).ProEt) (g : V ⟶ ⊤_ (S.domain i).ProEt), K g →
              ∀ (M : ModuleCat.{u + 1} (ULift.{u + 1} k)),
                Finite M →
                Nonempty ((SheafOfModules.overFunctor _ V).obj
                  ((proEtaleModuleInverseImage (S.immersion i)
                    (adicLisseConstantRing Y (ULift.{u + 1} k))).obj F) ≅
                  (SheafOfModules.overFunctor _ V).obj
                    ((proEtaleModuleInverseImage (S.immersion i)
                      (adicLisseConstantRing Y (ULift.{u + 1} k))).obj
                      ((adicLisseConstantModules Y (ULift.{u + 1} k)).obj M))) →
                Nonempty ((SheafOfModules.overFunctor _ V).obj
                  ((proEtaleModuleInverseImage (S.immersion i)
                    (adicLisseConstantRing Y (ULift.{u + 1} k'))).obj
                    ((finiteFieldScalarExtension Y f).obj F)) ≅
                  (SheafOfModules.overFunctor _ V).obj
                    ((proEtaleModuleInverseImage (S.immersion i)
                      (adicLisseConstantRing Y (ULift.{u + 1} k'))).obj
                      ((adicLisseConstantModules Y (ULift.{u + 1} k')).obj
                        ((ModuleCat.extendScalars
                          (RingHom.ulift.{u + 1, u + 1} f)).obj M))))) ∧
      (∀ (C : CochainComplex
          (pbcModules Y (adicLisseConstantRing Y (ULift.{u + 1} k))) ℤ) (i : ℤ),
        ∃ e : (finiteFieldScalarExtensionComplex Y f C).homology i ≅
            (finiteFieldScalarExtension Y f).obj (C.homology i),
          (∀ (r s : ℤ), r ≤ s →
            (∀ j : ℤ, IsConstructibleProEtaleCoefficientModuleSheaf Y
              (ULift.{u + 1} k) (C.homology j)) →
            (∀ j : ℤ, j < r ∨ s < j → IsZero (C.homology j)) →
            (∀ j : ℤ, (IsConstructibleProEtaleCoefficientModuleSheaf Y
              (ULift.{u + 1} k')
                ((finiteFieldScalarExtensionComplex Y f C).homology j)) ∧
            (∀ j : ℤ, j < r ∨ s < j →
              IsZero ((finiteFieldScalarExtensionComplex Y f C).homology j)))))) := by
  obtain ⟨hlim, hcolim⟩ := scalarExtension_exact Y f
  have : PreservesFiniteLimits (finiteFieldScalarExtension Y f) := hlim
  have : PreservesFiniteColimits (finiteFieldScalarExtension Y f) := hcolim
  have local_model := finiteFieldScalarExtension_localModel Y f
  have hconstruct : ∀ F, IsConstructibleProEtaleCoefficientModuleSheaf Y
      (ULift.{u + 1} k) F → IsConstructibleProEtaleCoefficientModuleSheaf Y
        (ULift.{u + 1} k') ((finiteFieldScalarExtension Y f).obj F) := by
    intro F hF
    obtain ⟨S, hn, hS, hF⟩ := hF
    refine ⟨S, hn, hS, fun i ↦ ?_⟩
    obtain ⟨K, hK, hF⟩ := hF i
    refine ⟨K, hK, fun V g hg ↦ ?_⟩
    obtain ⟨M, hM, eM⟩ := hF V g hg
    have : Finite M := hM
    exact ⟨(ModuleCat.extendScalars (RingHom.ulift.{u + 1, u + 1} f)).obj M,
      finite_tensor_model f M, local_model _ (S.immersion i) F V M eM⟩
  refine ⟨hlim, hcolim, ?_⟩
  intro F hF
  refine ⟨hconstruct F hF, ?_, ?_⟩
  · intro S i K hK V g hg M hM eM
    exact local_model _ (S.immersion i) F V M eM
  · intro C i
    let e : ∀ j, (finiteFieldScalarExtensionComplex Y f C).homology j ≅
        (finiteFieldScalarExtension Y f).obj (C.homology j) :=
      fun j ↦ (C.sc j).mapHomologyIso (finiteFieldScalarExtension Y f)
    refine ⟨e i, ?_⟩
    intro r s hrs hC hzero j
    constructor
    · exact constructible_iso Y (ULift.{u + 1} k') (e j).symm
        (hconstruct _ (hC j))
    · intro j hj
      exact ((finiteFieldScalarExtension Y f).map_isZero (hzero j hj)).of_iso (e j)

end AlgebraicGeometry.Scheme
