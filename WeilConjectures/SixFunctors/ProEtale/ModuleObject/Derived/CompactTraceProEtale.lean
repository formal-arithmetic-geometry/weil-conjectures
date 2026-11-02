/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

import WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedGeometricPointPerfectGeneral
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeTerminalSectionsComparison
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import all WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
import all WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedTensorStalk
import all WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import all Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import all WeilConjectures.Compactification.NagataCompactification
import all Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import all Mathlib.RingTheory.Nilpotent.Defs
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactifFiniteTor
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import all WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.SmallStrictHenselizationIndEtale
import all WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
import all WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonStalk
import all WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricStalkTensorConstantSingle
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
import all WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import all WeilConjectures.AlgebraicGeometry.ConstructibleModuleFiniteStalks
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingConstructibility
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingTensorTor
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import all WeilConjectures.CategoryTheory.RingDerivedScalarExtension.RingIsoPerfectScalarEquivalence
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective

/-!
# The complexes whose traces occur

Source: literature/blueprint/latest/blueprint/sec-trace-formula/
sk-lem-tf-compact-trace/_section.md, node sk-lem-tf-compact-trace
(blueprint: sk-lem-tf-compact-trace).

This is the condensed-coefficient form of the compact-trace finiteness statement, for a
finite commutative `ℓ`-primary coefficient ring `A`, realized as the discrete condensed ring
`Λ ≅ C(-, A)`.  Compact support is the recorded compactification lower-shriek followed by
terminal point scalar sections, and a geometric stalk is the derived pro-étale pullback to
the geometric point followed by those same exact point sections.  The perfectness predicate
is `IsPerfectRingComplex` over the scalar ring `Γ Λ`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local instance 1] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Obj
open CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

private abbrev pointCoyoneda
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :=
  coyonedaSections ((Mod.regularEndRingHom.op).comp
    (RingEquiv.toOpposite (Γ Λ)).toRingHom)

private def sectionsPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k] :
    pointCoyoneda Λ ≅ ((upperStarFromPoint (Spec (.of k))).mapMod Λ) ⋙
      condensedRingCoefficientSections Λ (Spec (.of k)) := by
  let H := (upperStarFromPoint (Spec (.of k))).mapMod Λ
  have : (upperStarFromPoint (Spec (.of k))).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : H.Additive := Functor.additive_of_preserves_binary_products H
  let c₁ := (Mod.regularEndRingHom.op).comp
    (RingEquiv.toOpposite (MonObj.Γ Λ)).toRingHom
  let c₂ := (Mod.regularEndRingHom.op).comp
    ((RingEquiv.toOpposite _).toRingHom.comp
      (condensedRingScalarSections Λ (Spec (.of k))))
  have h (a : MonObj.Γ Λ) : (Iso.refl (H.obj (Mod.regular Λ))).inv ≫
      H.map (c₁ a).unop = (c₂ ((RingHom.id _) a)).unop ≫
        (Iso.refl (H.obj (Mod.regular Λ))).inv := by
    simp only [Iso.refl_inv, Category.id_comp]
    exact Functor.mapMod_map_regularEndRingHom (upperStarFromPoint (Spec (.of k))) Λ a
  let τ := coyonedaSectionsMap (RingHom.id _) c₁ c₂ H (Iso.refl _) h
  have (M : _) : IsIso (τ.app M) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun f ↦ 𝟙 _ ≫ H.map f)
    simpa only [Category.id_comp] using
      (Functor.FullyFaithful.ofFullyFaithful H).map_bijective (Mod.regular Λ) M
  have : IsIso τ := NatIso.isIso_of_isIso_app _
  exact asIso τ

private theorem perfect_iso {R : Type (u + 1)} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{u + 1} R)}
    (e : K ≅ L) (h : _root_.DerivedCategory.IsPerfectRingComplex K) :
    _root_.DerivedCategory.IsPerfectRingComplex L := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨i⟩⟩ := h
  exact ⟨P, a, b, ha, hb, hP, ⟨e.symm ≪≫ i⟩⟩

private theorem point_coarse_perfect
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ell p : ℕ) [Fact ell.Prime] (k : Type u) [Field k] [IsAlgClosed k]
    [CharP k p] (hpell : p ≠ ell) (hΛ : IsAdmissibleCoefficient Λ)
    (K : ConstantModelConstructibleFiniteTor Λ (Spec (.of k))) :
    _root_.DerivedCategory.IsPerfectRingComplex
      ((condensedRingCoefficientSections Λ (Spec (.of k))).rightDerivedFunctor.obj
        K.obj) := by
  obtain ⟨_, _, _, _, _, _, hF, _⟩ :=
    CondensedGeometricPoint.condensed_geometric_point_perfect_general Λ k ell p hpell hΛ
  have hp := hF K
  let X := Spec (.of k)
  let e := ((upperStarFromPoint X).mapMod Λ).asEquivalence
  let S := Evaluation.sections (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u})
  let F := condensedRingCoefficientSections Λ X
  let r := InternalAbelianSheafModule.sectionGlobalEquiv
    (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u}) terminalIsTerminal
  let G := ModuleCat.restrictScalars r.toRingHom
  let := Functor.additive_of_preserves_binary_products e.inverse
  obtain ⟨q⟩ := native_terminalSectionsIso (coherentTopology Profinite.{u}) Λ
    (RingHom.id (Γ Λ)) (⊤_ Profinite.{u}) terminalIsTerminal
  change pointCoyoneda Λ ≅ S ⋙ G at q
  let h : F ≅ e.inverse ⋙ (S ⋙ G) :=
    (Functor.leftUnitor F).symm ≪≫
      Functor.isoWhiskerRight e.counitIso.symm F ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft e.inverse (sectionsPullbackIso Λ k).symm ≪≫
      Functor.isoWhiskerLeft e.inverse q
  let d : F.rightDerivedFunctor ≅
      CondensedGeometricPoint.fiber Λ k ⋙ G.mapDerivedCategory :=
    Functor.rightDerivedFunctorNatIso h ≪≫
      Functor.rightDerivedFunctorCompIso e.inverse (S ⋙ G) ≪≫
      Functor.isoWhiskerRight e.inverse.rightDerivedFunctorIsoMapDerivedCategory
        (S ⋙ G).rightDerivedFunctor ≪≫
      Functor.isoWhiskerLeft e.inverse.mapDerivedCategory
        (Functor.rightDerivedFunctorCompMapDerivedCategoryIso S G) ≪≫
      (Functor.associator _ _ _).symm
  have hr := CategoryTheory.RingDerivedScalarExtension.perfect_restrict
    (CommRingCat.of (Γ Λ)) (CommRingCat.of (condensedScalarRing Λ)) r
    ((CondensedGeometricPoint.fiber Λ k).obj K.obj) hp
  exact perfect_iso (d.app K.obj).symm hr

private theorem point_perfect_of_coarse
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (k : Type u) [Field k] [IsAlgClosed k]
    (h : ∀ K : ConstantModelConstructibleFiniteTor Λ (Spec (.of k)),
      _root_.DerivedCategory.IsPerfectRingComplex
        ((condensedRingCoefficientSections Λ (Spec (.of k))).rightDerivedFunctor.obj K.obj))
    (K : ConstantModelConstructibleFiniteTor Λ (Spec (.of k))) :
    _root_.DerivedCategory.IsPerfectRingComplex
      ((CohomologyTransport.sections Λ (Spec (.of k))).mapDerivedCategory.obj K.obj) := by
  let F := condensedRingCoefficientSections Λ (Spec (.of k))
  let e := InternalAbelianSheafModule.sectionGlobalEquiv
    (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u}) terminalIsTerminal
  let G := ModuleCat.restrictScalars e.symm.toRingHom
  have := (finite_point_sections_exact Λ k).1
  have := (finite_point_sections_exact Λ k).2
  obtain ⟨q⟩ := native_terminalSectionsIso.{u}
    (Scheme.ProEt.topology (Spec (.of k))) (condensedRingObj Λ (Spec (.of k)))
    ((condensedRingScalarSections Λ (Spec (.of k))).comp e.symm.toRingHom)
    (Scheme.ProEt.mk (𝟙 (Spec (.of k))))
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.WeaklyEtale (Spec (.of k)))
  change F ⋙ G ≅ CohomologyTransport.sections Λ (Spec (.of k)) at q
  let r := (Functor.mapDerivedCategoryCompIso F G).symm ≪≫
    Functor.mapDerivedCategoryNatIso q
  have hp := CategoryTheory.RingDerivedScalarExtension.perfect_restrict
    (CommRingCat.of (condensedScalarRing Λ)) (CommRingCat.of (Γ Λ)) e.symm
    (F.rightDerivedFunctor.obj K.obj) (h K)
  exact perfect_iso ((G.mapDerivedCategory.mapIso
    (F.rightDerivedFunctorIsoMapDerivedCategory.app K.obj)) ≪≫ r.app K.obj) hp

private theorem ctf_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (T : Scheme.{u})
    {K L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj Λ T))} (e : K ≅ L)
    (h : (constantModelBoundedConstructible Λ T ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) K) :
    (constantModelBoundedConstructible Λ T ⊓
      _root_.DerivedCategory.finiteTorAmplitude _) L := by
  let := (constantModelConstructibleFiniteTor_wellDefined Λ T).2.1
  let := (constantModelConstructibleFiniteTor_wellDefined Λ T).2.2.2.1
  exact ObjectProperty.prop_of_iso _ e h

private theorem compact_ctf_coefficientIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (h : ∀ K : ConstantModelConstructibleFiniteTor Λ' X,
      (constantModelBoundedConstructible Λ' Y ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        ((rightDerivedLowerShriekOfCompactification Λ' c).obj K.obj))
    (K : ConstantModelConstructibleFiniteTor Λ X) :
    (constantModelBoundedConstructible Λ Y ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
      ((rightDerivedLowerShriekOfCompactification Λ c).obj K.obj) := by
  let e₀ : Λ ≅ Λ' := (Mon.forget _).mapIso e
  have : IsMonHom e₀.inv := inferInstanceAs (IsMonHom e.inv.hom)
  have : IsMonHom e₀.hom := inferInstanceAs (IsMonHom e.hom.hom)
  let H (Z : Scheme.{u}) :
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ' Z) :=
    Mod.comap (coefficientMap e₀.inv Z)
  let J (Z : Scheme.{u}) :
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ' Z) ⥤
      Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z) :=
    Mod.comap (coefficientMap e₀.hom Z)
  have hEq (Z : Scheme.{u}) : (H Z).IsEquivalence :=
    inferInstanceAs (Mod.comapEquivalenceOfIsIso (coefficientMap e₀.inv Z)).functor.IsEquivalence
  have hext (Z : Scheme.{u}) :
      PreservesFiniteLimits (Mod.extendScalars (coefficientMap e₀.inv Z)) :=
    preservesFiniteLimits_of_natIso (Mod.extendScalarsIsoComapInv _).symm
  let io : (openImmersionLowerShriek Λ c.i).mapDerivedCategory ⋙ (H c.Z).mapDerivedCategory ≅
      (H X).mapDerivedCategory ⋙ (openImmersionLowerShriek Λ' c.i).mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (comapOpenImmersionLowerShriekIso e₀.inv c.i) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  let ic : rightDerivedLowerShriekOfCompactification Λ c ⋙ (H Y).mapDerivedCategory ≅
      (H X).mapDerivedCategory ⋙ rightDerivedLowerShriekOfCompactification Λ' c :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (derivedComapLowerStarIso e₀.inv c.g) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight io _ ≪≫
      Functor.associator _ _ _
  have hK := constantModelCtf_coefficientIso e X K
  have ht := ctf_iso Λ' Y (ic.app K.obj).symm (h ⟨_, hK⟩)
  have hj := constantModelCtf_coefficientIso e.symm Y ⟨_, ht⟩
  let α : H Y ⋙ J Y ≅ 𝟭 _ :=
    (Mod.comapComp _ _).symm ≪≫ Mod.comapCongr (by
      rw [← coefficientMap_comp]
      change coefficientMap ((Mon.forget _).map (e.hom ≫ e.inv)) Y = _
      rw [Iso.hom_inv_id]
      exact coefficientMap_id Y) ≪≫ Mod.comapId _
  let β : (H Y).mapDerivedCategory ⋙ (J Y).mapDerivedCategory ≅ 𝟭 _ :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso α ≪≫ Functor.mapDerivedCategoryIdIso _
  exact ctf_iso Λ Y (β.app _) hj

private theorem direct_images_ctf
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (k : Type u) [Field k] [IsAlgClosed k]
    (ℓ : ℕ) [Fact ℓ.Prime] (hchar : ℓ ≠ ringChar k)
    (hΛ : ∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
      Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A)))
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (c : Compactification X.hom) (K : ConstantModelConstructibleFiniteTor Λ X.left) :
    (constantModelBoundedConstructible Λ (Spec (.of k)) ⊓
      _root_.DerivedCategory.finiteTorAmplitude _)
      ((rightDerivedLowerShriekOfCompactification Λ c).obj K.obj) := by
  classical
  obtain ⟨A, hA, htop, hd, hr, hfin, ⟨n, hn⟩, ⟨eA⟩⟩ := hΛ
  let B := ULift.{u} A
  let : TopologicalSpace B := ⊥
  let : DiscreteTopology B := ⟨rfl⟩
  have hb : IsNilpotent (ℓ : B) := by
    refine ⟨n, ?_⟩
    change ULift.up ((ℓ : A) ^ n) = ULift.up (0 : A)
    congr 1
    simpa only [nsmul_eq_mul, _root_.mul_one, Nat.cast_pow] using hn 1
  let e : A ≃+* B := ULift.ringEquiv.symm
  let h : Profinite.continuousMapRingSheaf.{u} A ⟶
      Profinite.continuousMapRingSheafOfUniverse.{u, u} B :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.toRingHom.compLeftContinuous S.unop (by fun_prop)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let v : Profinite.continuousMapRingSheafOfUniverse.{u, u} B ⟶
      Profinite.continuousMapRingSheaf.{u} A :=
    ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          ((e.symm.toRingHom.compLeftContinuous S.unop (by fun_prop)).comp
            ULift.ringEquiv.toRingHom))
       naturality := by intros; rfl }⟩
  let E : Profinite.continuousMapRingSheaf.{u} A ≅
      Profinite.continuousMapRingSheafOfUniverse.{u, u} B :=
    { hom := h
      inv := v
      hom_inv_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S f
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        exact e.apply_symm_apply _ }
  let E' := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso E
  have hmon : IsMonHom E'.hom := Sheaf.isMonHom_sheafCompose_map _ E.hom
  let eb : Mon.mk (Profinite.continuousMapRingObj A) ≅
      Mon.mk (FiniteDiscreteOrdinary.coefficient B) := Mon.mkIso' E'
  exact compact_ctf_coefficientIso (eA ≪≫ eb) c
    (fun L ↦ normalized_compact_ctf ℓ k B hb hchar X.hom c L.obj L.property) K

/-- Let `X` be separated of finite type over `k = F̄_q`, let `A` be a finite commutative
`ℓ`-primary ring with `ℓ ≠ char k` and `K ∈ D_ctf(X, A)`.  Then `RΓ_c(X_proét, K)` and every
geometric stalk `K_x̄` are perfect `A`-complexes, so the traces of their endomorphisms are
defined.  The compact-support complex is formed for every compactification (the chosen
compactification of the source), and the stalk clause ranges over all algebraically closed
geometric points, using the derived pro-étale pullback before exact point scalar sections.

Source: blueprint latest, sk-lem-tf-compact-trace/_section.md, node sk-lem-tf-compact-trace
(blueprint: sk-lem-tf-compact-trace).

Proof: the normalized finite-discrete ordinary equivalence identifies each actual
compactification composite with the ordinary finite-coefficient compactification functor,
which preserves Dctf. Transport along the coefficient isomorphism commutes with exact open
extension and derived proper image, and its inverse reflects Dctf. Exact geometric pullback
preserves the same property for every stalk.
The finite-field cardinality gives characteristic p on k; a geometric point over X
inherits it through its field homomorphism. The general point-realization theorem, which
implements sk-lem-finite for arbitrary admissible coefficients, makes these point objects
perfect. Evaluation at one compares its recorded point fibre with regular-module scalar
sections. Both scalar presentations are related by the terminal-section ring equivalence,
and restriction along that ring equivalence preserves bounded finite projective models.
Thus this proves the compact and every-stalk clauses with their original scalar actions.
The usual perfect-complex categorical trace then applies, as in sk-d-trace. -/
theorem compactTrace_perfect
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : ∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
      Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A)))
    (X : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : ConstantModelConstructibleFiniteTor Λ X.left) :
    ∀ (c : Compactification X.hom),
      _root_.DerivedCategory.IsPerfectRingComplex
        ((condensedRingCompactCoefficientComplex Λ c).obj K.obj) ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (x : Spec (.of Ω) ⟶ X.left),
        _root_.DerivedCategory.IsPerfectRingComplex
          ((CohomologyTransport.sections Λ (Spec (.of Ω))).mapDerivedCategory.obj
            ((upperStar Λ x).mapDerivedCategory.obj K.obj)) := by
  let : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let : Fact (ringChar D.k).Prime :=
    ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  let : Fact (ringChar D.k ≠ ℓ) := ⟨by rw [ringChar.eq D.k D.p]; exact hℓ.symm⟩
  have ha : IsAdmissibleCoefficient Λ := by
    obtain ⟨A, hA, htop, hd, hr, hfin, ⟨n, hn⟩, he⟩ := hΛ
    exact ⟨ℓ, inferInstance, Or.inl ⟨A, hA, hfin, htop, hd, hr, ⟨n,
      by simpa only [nsmul_eq_mul, _root_.mul_one, Nat.cast_pow] using hn 1⟩, he⟩⟩
  intro c
  have hc := direct_images_ctf Λ D.k ℓ (by rw [ringChar.eq D.k D.p]; exact hℓ) hΛ X c K
  constructor
  · exact point_coarse_perfect Λ ℓ D.p D.k hℓ.symm ha
      ⟨_, hc⟩
  · intro Ω _ _ x
    let f : Spec (.of Ω) ⟶ Spec (.of D.k) := x ≫ X.hom
    let r : D.k →+* Ω := (Spec.preimage f).hom
    let : CharP Ω D.p := charP_of_injective_ringHom r.injective D.p
    let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
    let : QuasiSeparatedSpace X.left := quasiSeparatedSpace_of_quasiSeparated X.hom
    have hbc := pullback_bounded_constructible Λ x
      (pullback_constructible Λ x) K.obj K.property.1
    have ht := pullback_tor Λ x K.obj K.property.2
    let e := leftDerivedUpperStarIsoMapDerivedCategory Λ x
    let := (constantModelConstructibleFiniteTor_wellDefined Λ (Spec (.of Ω))).2.1
    let := (constantModelConstructibleFiniteTor_wellDefined Λ (Spec (.of Ω))).2.2.2.1
    let L : ConstantModelConstructibleFiniteTor Λ (Spec (.of Ω)) :=
      ⟨(upperStar Λ x).mapDerivedCategory.obj K.obj,
        (constantModelBoundedConstructible Λ (Spec (.of Ω))).prop_of_iso
          (e.app K.obj) hbc,
        (_root_.DerivedCategory.finiteTorAmplitude _).prop_of_iso (e.app K.obj) ht⟩
    exact point_perfect_of_coarse Λ Ω
      (point_coarse_perfect Λ ℓ D.p Ω hℓ.symm ha) L

end AlgebraicGeometry.ProEtale.CondensedRing
