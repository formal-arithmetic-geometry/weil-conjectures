/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C9
-/
module

public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.Localization.Away.Basic
import WeilConjectures.AlgebraicGeometry.TildePreservesFiniteLimits
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Principal-open comparison for a supplied affine model

Source: Stacks Project, Tags 01HV, 01IB and 06Z0.
(blueprint: lem-sc-affine-principal-model-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- Restricting an affine sheaf model to a principal open is exact associated
sheafification of its scalar extension; this functor preserves finite free objects.
Source: Stacks Project, Tags 01HV, 01IB and 06Z0.
(blueprint: lem-sc-affine-principal-model-comparison).

Proof: Put A = Gamma(X,U), B = A_f and j = Spec(B) -> Spec(A). The composite
p = j followed by the affine-chart inverse and U -> X is an open immersion.
Let V be its open image and e : Spec(B) = V its canonical isomorphism. Since
f is outside the prime of s, s is in V. Take F = tilde_B followed by restriction
along e inverse. Tilde is exact (localization is exact), as is restriction,
so F preserves finite limits and colimits. Tilde of a finite free module is
the finite free structure-sheaf module, and restriction preserves this module.
To compare models, factor V -> X through U and use the over-site equivalences.
The tilde-pullback isomorphism for A -> B identifies the further restriction
of tilde_A M with tilde_B (B tensor_A M), naturally in M and its differentials.
Exact functors descend through quasi-isomorphisms. Their localization comparison
and the supplied eM give the displayed derived isomorphism. If f is a unit this
is the whole affine open; f = 0 is excluded at the specified prime. No boundedness,
flatness, perfection or cohomological splitting is assumed here. -/
theorem affine_principal_model_comparison (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (K : schemeDerivedCategory X) (s : X)
    (U : X.Opens) (hsU : s ∈ U) (hU : IsAffineOpen U)
    (M : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op U))) ℤ)
    (eM : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj
          (((Scheme.affinePerfectSheafification X U hU).mapHomologicalComplex
            (.up ℤ)).obj M)))
    (f : X.presheaf.obj (.op U)) (hf : f ∉ (hU.isoSpec.hom ⟨s, hsU⟩).asIdeal) :
    ∃ V : X.Opens, s ∈ V ∧
      ∃ F : ModuleCat.{u} (Localization.Away f) ⥤
        SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace),
        ∃ hF : F.Additive, PreservesFiniteLimits F ∧ PreservesFiniteColimits F ∧
        (∀ m : ℕ, Nonempty (F.obj
          (ModuleCat.of (Localization.Away f) (ULift.{u} (Fin m) →₀ Localization.Away f)) ≅
          SheafOfModules.free (R := moduleRings V.toScheme.toRingedSpace)
            (ULift.{u} (Fin m)))) ∧
        letI : F.Additive := hF
        Nonempty
          (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V) ⋙
            Equivalence.functor
              (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
              (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
              (Scheme.Modules.overEquiv V)).mapDerivedCategory.obj K ≅
            DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
              ((RingTensorCohomology.extend _ (Localization.Away f)).obj M))) := by
  classical
  let A := X.presheaf.obj (.op U)
  let B : CommRingCat.{u} := .of (Localization.Away f)
  let φ : A ⟶ B := CommRingCat.ofHom (algebraMap A (Localization.Away f))
  let j := Spec.map φ
  have : IsOpenImmersion j := IsOpenImmersion.of_isLocalization f
  let g := j ≫ hU.isoSpec.inv
  let p := g ≫ U.ι
  let V := p.opensRange
  let e : Spec B ≅ V.toScheme := p.isoOpensRange
  have hsV : s ∈ V := by
    have hs : hU.isoSpec.hom ⟨s, hsU⟩ ∈ j.opensRange := by
      rw [Scheme.Hom.opensRange_localizationAway]
      exact hf
    obtain ⟨t, ht⟩ := hs
    refine ⟨t, ?_⟩
    have hgt : g t = ⟨s, hsU⟩ := by
      simpa [g] using congrArg hU.isoSpec.inv ht
    change U.ι (g t) = s
    rw [hgt]
    rfl
  let q := e.inv ≫ g
  have hq : q ≫ U.ι = V.ι := by
    change e.inv ≫ (g ≫ U.ι) = V.ι
    exact p.isoOpensRange_inv_comp
  have hchart : q ≫ hU.isoSpec.hom = e.inv ≫ j := by
    simp [q, g, Category.assoc]
  let T : ModuleCat.{u} B ⥤
      SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace) := tilde.functor B
  let S : SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) :=
    Scheme.Modules.restrictFunctor e.inv
  let F := T ⋙ S
  have : PreservesFiniteLimits T := tilde_preserves_finite_limits (Localization.Away f)
  have : T.IsLeftAdjoint := (tilde.adjunction (R := B)).isLeftAdjoint
  have : S.IsLeftAdjoint := (Scheme.Modules.restrictAdjunction e.inv).isLeftAdjoint
  have : PreservesLimitsOfSize.{u, u} S :=
    Scheme.Modules.preservesLimitsOfSize_restrictFunctor e.inv
  have : PreservesFiniteLimits S := inferInstance
  have : T.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  have : S.Additive := ⟨by intros; rfl⟩
  have hFadd : F.Additive := inferInstance
  let := hFadd
  refine ⟨V, hsV, F, hFadd, inferInstance, inferInstance, ?_, ?_⟩
  · intro m
    exact ⟨S.mapIso (tildeFinsupp (R := B) (ULift.{u} (Fin m))) ≪≫
      (SheafOfModules.mapFreeIso S (ULift.{u} (Fin m))
        (Scheme.Modules.restrictUnitIso e.inv).symm).symm⟩
  · let EU : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
        SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
      (Scheme.Modules.overEquiv U).functor
    let RU := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
    let RQ : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) ⥤
        SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) :=
      Scheme.Modules.restrictFunctor q
    have : RQ.Additive := ⟨by intros; rfl⟩
    have : PreservesLimitsOfSize.{u, u} RQ :=
      Scheme.Modules.preservesLimitsOfSize_restrictFunctor q
    have : PreservesFiniteLimits RQ := inferInstance
    have : RQ.IsLeftAdjoint := (Scheme.Modules.restrictAdjunction q).isLeftAdjoint
    have : EU.Additive := Functor.additive_of_preserves_binary_products _
    let Φ : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) ⥤
        SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace) :=
      EU ⋙ RQ
    have : Φ.Additive := inferInstanceAs (EU ⋙ RQ).Additive
    have : PreservesFiniteLimits Φ := comp_preservesFiniteLimits EU RQ
    have : PreservesFiniteColimits Φ := comp_preservesFiniteColimits EU RQ
    let RV := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
        (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv V)
    let θ : RV ≅ RU ⋙ Φ :=
      Scheme.Modules.overFunctorEquiv V ≪≫
        (Scheme.Modules.restrictFunctorCongr hq).symm ≪≫
        Scheme.Modules.restrictFunctorComp q U.ι ≪≫
        Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv U).symm
          (Scheme.Modules.restrictFunctor q) ≪≫
        Functor.associator RU EU (Scheme.Modules.restrictFunctor q)
    let TA := tilde.functor A
    let H := Scheme.Modules.restrictFunctor hU.isoSpec.hom
    let EI := (Scheme.Modules.overEquiv U).inverse
    let ec : Scheme.affinePerfectSheafification X U hU ⋙ EU ≅ TA ⋙ H :=
      Functor.associator TA (H ⋙ EI) EU ≪≫
        Functor.isoWhiskerLeft TA
          (Functor.associator H EI EU ≪≫
            Functor.isoWhiskerLeft H (Scheme.Modules.overEquiv U).counitIso ≪≫
            Functor.rightUnitor H)
    let em : Scheme.affinePerfectSheafification X U hU ⋙ Φ ≅
        ModuleCat.extendScalars φ.hom ⋙ F :=
      (Functor.associator _ EU (Scheme.Modules.restrictFunctor q)).symm ≪≫
        Functor.isoWhiskerRight ec (Scheme.Modules.restrictFunctor q) ≪≫
        Functor.associator TA H (Scheme.Modules.restrictFunctor q) ≪≫
        Functor.isoWhiskerLeft TA
          ((Scheme.Modules.restrictFunctorComp q hU.isoSpec.hom).symm ≪≫
            Scheme.Modules.restrictFunctorCongr hchart ≪≫
            Scheme.Modules.restrictFunctorComp e.inv j) ≪≫
        (Functor.associator TA (Scheme.Modules.restrictFunctor j) S).symm ≪≫
        Functor.isoWhiskerRight
          (Functor.isoWhiskerLeft TA (Scheme.Modules.restrictFunctorIsoPullback j) ≪≫
            Scheme.Modules.tildePullbackIso φ) S ≪≫
        Functor.associator (ModuleCat.extendScalars φ.hom) T S
    let DΦ : DerivedCategory
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ⥤
        schemeDerivedCategory.{u, w} V.toScheme := Φ.mapDerivedCategory
    let dθ : RV.mapDerivedCategory ≅ RU.mapDerivedCategory ⋙ DΦ :=
      Functor.mapDerivedCategoryNatIso θ ≪≫ Functor.mapDerivedCategoryCompIso RU Φ
    exact ⟨dθ.app K ≪≫ DΦ.mapIso eM.some ≪≫
      Φ.mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex em (.up ℤ)).app M)⟩

end AlgebraicGeometry
