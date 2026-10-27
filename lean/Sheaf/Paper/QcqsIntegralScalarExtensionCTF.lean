/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.ContinuousIntegralCoefficients
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import Sheaf.Paper.ContinuousIntegralScalarExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import Sheaf.CategoryTheory.ModuleObjects.ScalarTensorCancellation
import Sheaf.Paper.RegularExtensionComparison
import all Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import all Sheaf.Paper.QcqsConstructibleIntegralLatticeTree

/-!
# Integral scalar extension on a qcqs scheme

Source: Hemo--Richarz--Scholbach, Theorem 7.7 and §7.2 for context; the exact-functor,
finite scalar-model and flat-model argument of the DAG node
(blueprint: lem-sfb-qcqs-integral-scalar-extension-ctf).

The assertion below uses ordinary uncompleted unbounded derived categories and the
existing relative module-object tensors. Its two instances are the actual coefficient
inclusions into the finite field and into the finite-subextension-valued algebraic closure.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

section DerivedNames

universe v w

variable {C : Type v} [Category.{w} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{w} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]

/-- The canonical left derived scalar extension, with its module-category structural
arguments shared before specializing to a scheme. Source: the displayed T_F,T in the DAG
(blueprint: lem-sfb-qcqs-integral-scalar-extension-ctf). -/
noncomputable def integralCTFDerived : DerivedCategory (Mod C R) ⥤ DerivedCategory (Mod C S) :=
  (Mod.extendScalars a).leftDerivedFunctor

/-- The canonical derived counit; its invertibility means computation termwise on all
complexes. Source: the termwise clause of the DAG
(blueprint: lem-sfb-qcqs-integral-scalar-extension-ctf). -/
noncomputable def integralCTFCounit :
    DerivedCategory.Qh ⋙ integralCTFDerived a ⟶
      (Mod.extendScalars a).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  (Mod.extendScalars a).leftDerivedFunctorCounit

/-- Shifts transported from exact termwise scalar extension through its canonical derived
comparison. Source: the triangulated clause of the DAG
(blueprint: lem-sfb-qcqs-integral-scalar-extension-ctf). -/
@[instance_reducible]
noncomputable def integralCTFShift (h : PreservesFiniteLimits (Mod.extendScalars a)) :
    (integralCTFDerived a).CommShift ℤ :=
  letI := h
  Functor.CommShift.ofIso (Mod.extendScalars a).leftDerivedFunctorIsoMapDerivedCategory.symm ℤ

end DerivedNames

section

variable (A Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj A] [IsCommMonObj A] [MonObj Λ] [IsCommMonObj Λ]
  (φ : A ⟶ Λ) [IsMonHom φ] (T : Scheme.{u})

/-- The clauses of the integral scalar-extension assertion, packaged for the two
coefficient targets. `IsIso` applies to the canonical derived counit, so the termwise
comparison uses the given scalar-extension functor. The cohomology comparison is a
natural isomorphism of functors, and the final clause retains each specified stratum.
Source: Hemo--Richarz--Scholbach, Theorem 7.7 and §7.2 for context; DAG statement
(blueprint: lem-sfb-qcqs-integral-scalar-extension-ctf). -/
def IntegralScalarExtensionCTF : Prop :=
  ∃ h : PreservesFiniteLimits (Mod.extendScalars (coefficientMap φ T)),
  PreservesFiniteColimits (Mod.extendScalars (coefficientMap φ T)) ∧
  IsIso (integralCTFCounit (coefficientMap φ T)) ∧
  (@Functor.IsTriangulated _ _ _ _ _ _ (integralCTFDerived (coefficientMap φ T))
    (integralCTFShift (coefficientMap φ T) h) _ _ _ _ _ _ _ _) ∧
  (∀ q : ℤ, Nonempty
    ((integralCTFDerived (coefficientMap φ T)) ⋙
        DerivedCategory.homologyFunctor _ q ≅
      DerivedCategory.homologyFunctor _ q ⋙ Mod.extendScalars (coefficientMap φ T))) ∧
  (∀ (J : ConstantModelConstructibleFiniteTor A T) (a b : ℤ),
    DerivedCategory.torAmplitudeIn _ a b J.obj →
      (constantModelBoundedConstructible Λ T ⊓ DerivedCategory.finiteTorAmplitude _)
        ((integralCTFDerived (coefficientMap φ T)).obj J.obj) ∧
      DerivedCategory.torAmplitudeIn _ a b
        ((integralCTFDerived (coefficientMap φ T)).obj J.obj)) ∧
  (∀ (J : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj A T)))
      (q : ℤ) (S : Scheme.Stratification T) (s : Fin S.n),
    HasFiniteConstantLocalModel A (S.domain s)
      ((upperStar A (S.immersion s)).obj ((DerivedCategory.homologyFunctor _ q).obj J)) →
    ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain s), ∀ i : 𝒰.I₀,
      Mod.IsFree (condensedRingObj Λ (𝒰.X i))
        ((upperStar Λ (𝒰.f i)).obj ((upperStar Λ (S.immersion s)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((integralCTFDerived (coefficientMap φ T)).obj J)))))

end

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- A right exact additive functor taking the regular module to the regular module
carries a finite presentation to a finite presentation. -/
private theorem finitePresentation_map
    {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalPreadditive C] [MonoidalPreadditive D]
    {R : C} {B : D} [MonObj R] [MonObj B]
    [PreservesFiniteColimits (MonoidalCategory.tensorLeft R)]
    [PreservesFiniteColimits (MonoidalCategory.tensorLeft B)]
    (G : Mod C R ⥤ Mod D B) [G.Additive] [PreservesFiniteColimits G]
    (e : G.obj (Mod.regular R) ≅ Mod.regular B)
    {M : Mod C R} (hM : Mod.IsFinitelyPresented R M) :
    Mod.IsFinitelyPresented B (G.obj M) := by
  obtain ⟨n, m, f, ⟨h⟩⟩ := hM
  let en (n : ℕ) : G.obj (Mod.finiteFree R n) ≅ Mod.finiteFree B n :=
    G.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫ biproduct.mapIso (fun _ ↦ e)
  refine ⟨n, m, (en m).inv ≫ G.map f ≫ (en n).hom, ⟨?_⟩⟩
  exact G.mapIso h ≪≫ PreservesCokernel.iso G f ≪≫
    cokernel.mapIso _ _ (en m) (en n) (by simp)

section Models

variable {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
  (φ : A ⟶ B) [IsMonHom φ]

/-- The two scalar-extension/pullback composites have canonically isomorphic right
adjoints, hence are isomorphic left adjoints. -/
private noncomputable def pointExtensionIso (X : Scheme.{u}) :
    Mod.extendScalars φ ⋙ (upperStarFromPoint X).mapMod B ≅
      (upperStarFromPoint X).mapMod A ⋙ Mod.extendScalars (coefficientMap φ X) := by
  let F := upperStarFromPoint X
  let adj := pointUpperStarLowerStarAdjunction.comp
    (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  let G := ProEtale.lowerStar Ab.{u + 1} (toSpecZ X) ⋙ pointLowerStar
  let a := (Mod.extendRestrictAdjunction φ).comp (adj.mapModAdjunction B)
  let b := (adj.mapModAdjunction A).comp
    (Mod.extendRestrictAdjunction (F.map φ))
  have e : Mod.comap (F.map φ) ⋙
      (G.mapMod (F.obj A) ⋙ Mod.comap (adj.unitAlgHom A)) ≅
      (G.mapMod (F.obj B) ⋙ Mod.comap (adj.unitAlgHom B)) ⋙ Mod.comap φ :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (G.mapModComapIso (F.map φ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapComp _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapCongr (adj.unit.naturality φ).symm) ≪≫
    Functor.isoWhiskerLeft _ (Mod.comapComp _ _) ≪≫
    (Functor.associator _ _ _).symm
  exact a.leftAdjointUniq (b.ofNatIsoRight e)

private theorem localModel_extension (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj A X))
    (hM : HasFiniteConstantLocalModel A X M) :
    HasFiniteConstantLocalModel B X
      ((Mod.extendScalars (coefficientMap φ X)).obj M) := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨e⟩⟩ := hU i
  refine ⟨(Mod.extendScalars φ).obj P,
    finitePresentation_map (Mod.extendScalars φ) (Mod.regularExtensionIso φ) hP, ⟨?_⟩⟩
  exact ((pullIso φ (U.f i)).app M).symm ≪≫
    (Mod.extendScalars (coefficientMap φ (U.X i))).mapIso e ≪≫
    ((pointExtensionIso φ (U.X i)).app P).symm

private theorem localModel_iso {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel B X M) :
    HasFiniteConstantLocalModel B X N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨h⟩⟩ := hU i
  exact ⟨P, hP, ⟨(upperStar B (U.f i)).mapIso e.symm ≪≫ h⟩⟩

private theorem integralCTF_of_models (T : Scheme.{u})
    [CompactSpace T] [QuasiSeparatedSpace T]
    [PreservesFiniteLimits (Mod.extendScalars (coefficientMap φ T))]
    (hf : ∀ (X : Scheme.{u})
      (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X)),
      HasFiniteConstantLocalModel B X M →
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
        Mod.IsFree (condensedRingObj B (U.X i)) ((upperStar B (U.f i)).obj M)) :
    IntegralScalarExtensionCTF A B φ T := by
  let G := Mod.extendScalars (coefficientMap φ T)
  have : G.PreservesFlat := Mod.extendScalars_preservesFlat _
  let e := G.leftDerivedFunctorIsoMapDerivedCategory
  let : G.leftDerivedFunctor.CommShift ℤ := Functor.CommShift.ofIso e.symm ℤ
  let := Functor.CommShift.ofIso_compatibility e.symm ℤ
  have ht : G.leftDerivedFunctor.IsTriangulated :=
    Functor.isTriangulated_of_iso e.symm
  refine ⟨inferInstance, inferInstance, ?_, ht, ?_, ?_, ?_⟩
  · exact G.isIso_leftDerivedFunctorCounit
  · intro q
    exact ⟨(G.leftDerivedFunctorHomologyFunctorIso q).symm⟩
  · intro J a b hJ
    have hTor : DerivedCategory.torAmplitudeIn _ a b
        ((integralCTFDerived (coefficientMap φ T)).obj J.obj) :=
      (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso (e.app J.obj).symm
        (DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj G hJ)
    refine ⟨⟨⟨?_, ?_⟩, a, b, hTor⟩, hTor⟩
    · exact DerivedCategory.TStructure.t.bounded.prop_of_iso (e.app J.obj).symm
        (G.bounded_mapDerivedCategory_obj J.property.1.1)
    · intro q
      obtain ⟨S, hS⟩ := (show IsFiniteConstantStratified A T
          ((DerivedCategory.homologyFunctor _ q).obj J.obj) from by
        simpa only [IsConstantModelConstructible, if_pos
          (show CompactSpace T ∧ QuasiSeparatedSpace T from ⟨inferInstance, inferInstance⟩)]
          using J.property.1.2 q)
      rw [IsConstantModelConstructible, if_pos
        (show CompactSpace T ∧ QuasiSeparatedSpace T from ⟨inferInstance, inferInstance⟩)]
      refine ⟨S, fun s ↦ ?_⟩
      exact localModel_iso
        ((pullIso φ (S.immersion s)).app _ ≪≫
          (upperStar B (S.immersion s)).mapIso
            ((G.leftDerivedFunctorHomologyFunctorIso q).app J.obj))
        (localModel_extension φ _ _ (hS s))
  · intro J q S s h
    apply hf
    exact localModel_iso
      ((pullIso φ (S.immersion s)).app _ ≪≫
        (upperStar B (S.immersion s)).mapIso
          ((G.leftDerivedFunctorHomologyFunctorIso q).app J))
      (localModel_extension φ _ _ h)

end Models

/-- Integral scalar extension to either allowed rational coefficient ring is flat,
computed termwise, triangulated, compatible with cohomology, and preserves the same
Tor interval and finite-model constructibility, with locally finite free cohomology
on every original model stratum.

Source: Hemo--Richarz--Scholbach, Theorem 7.7 and §7.2 for context; the ordinary
finite-model argument in the DAG (blueprint: lem-sfb-qcqs-integral-scalar-extension-ctf).

Proof:
1. Integral rationalization is exact by `integralScalarExtension_exact`. The algebraic
   closure case is its composite with the exact finite-subfield inclusion. The coefficient
   map composition equation and `Mod.extendScalarsComp` identify this composite with the
   required extension. Scalar extension is a left adjoint, hence preserves finite colimits.
2. The canonical exact-functor comparison identifies derived extension with termwise
   extension, makes the derived counit invertible, and gives the natural cohomology
   comparison. Transport its shifts to obtain the specified triangulated structure.
3. Scalar extension preserves finite presentations: apply it to the finite-free cokernel
   presentation and use `Mod.regularExtensionIso`. Pullback commutes with coefficient
   extension by `pullIso`; pullback from the point commutes with it by uniqueness of left
   adjoints. Thus each original finite constant local model extends to a finite constant
   local model. Over either target field, the existing finite-matrix Gaussian elimination
   helper `lattice_scalar_free` makes that model finite free, including rank zero.
   The original stratification and cover suffice; `models_free_cover` transports the
   scalar presentation to the module on its cover.
4. Internal scalar extension preserves flat modules by `Mod.extendScalars_preservesFlat`.
   The existing `DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj` applies the exact
   functor to a flat model supported in [a,b], preserving both flatness and that support.
   The canonical derived comparison transfers the resulting Tor interval. The exact
   cohomology comparison preserves boundedness, and Step 3 preserves constructibility.
   This gives D_ctf and the same specified interval, without a section-module comparison.
-/
theorem qcqs_integral_scalar_extension_ctf
    (ℓ : ℕ) [Fact ℓ.Prime] (F : PadicAlgCl.FiniteIntermediateField ℓ)
    (T : Scheme.{u}) [CompactSpace T] [QuasiSeparatedSpace T] :
    IntegralScalarExtensionCTF (integralCoeff ℓ F) (Profinite.continuousMapRingObj F)
      (integralScalarMap ℓ F) T ∧
    IntegralScalarExtensionCTF (integralCoeff ℓ F) (Profinite.padicAlgClRingObj ℓ)
      (integralScalarMap ℓ F ≫ Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) T := by
  constructor
  · apply integralCTF_of_models
    intro X M hM
    exact models_free_cover _ M
      (lattice_scalar_free (Profinite.continuousMapRingSheaf F.1)
        (ULift.{u + 1} F.1) (finite_point_scalars ℓ F)) hM
  · have : PreservesFiniteLimits
        (Mod.extendScalars (coefficientMap
          (integralScalarMap ℓ F ≫ Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) T)) := by
      let e := Mod.extendScalarsIsoOfEq (coefficientMap_comp (integralScalarMap ℓ F)
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) T)
      exact preservesFiniteLimits_of_natIso (e ≪≫ Mod.extendScalarsComp _ _).symm
    apply integralCTF_of_models
    intro X M hM
    exact models_free_cover _ M
      (lattice_scalar_free (Profinite.padicAlgClCondensedRing ℓ)
        (ULift.{u + 1} (PadicAlgCl ℓ)) (closure_point_scalars ℓ)) hM

end AlgebraicGeometry.ProEtale.CondensedRing
