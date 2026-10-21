/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V6
-/
module

public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import Mathlib.RingTheory.PrincipalIdealDomain
import Sheaf.CategoryTheory.InternalSectionModuleFlat
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Flatness of continuous coefficients over discrete constant scalars

Source: Stacks Project, Tags 093J, 03EI, 03EP and 08FC; the torsion-free flatness criterion
for a principal ideal domain (blueprint: lem-sfb-constant-to-continuous-scalar-flat).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteConstantModel

/-- The canonical map from discrete constant scalars to continuous functions is flat over
any principal ideal domain.

Source: Stacks Project, Tags 093J, 03EI, 03EP and 08FC, together with torsion-free flatness
criterion for a principal ideal domain.
(blueprint: lem-sfb-constant-to-continuous-scalar-flat).

Proof: the sheafification unit induces a ring homomorphism from A into every section
ring of the constant sheaf. Its composite with φ acts by ordinary scalar multiplication,
by hφ. Continuous A-valued functions on each profinite test object are torsion-free
pointwise, hence flat over the PID A. For any finite relation over the sheafified constant
ring, local surjectivity of the sheafification unit lifts its coefficients to A on a common
covering sieve. Restrict the relation there and apply the ordinary equational criterion
for flatness. Map the resulting finite factorization matrix into the section ring; the
scalar-action calculation verifies its equations. The local equational criterion gives
flatness of the section module. Transport it to internal flatness through the tensor
comparison equivalence, and identify extension of scalars followed by forgetful with
tensoring by the restricted regular module followed by forgetful. Since forgetful is exact
and reflects finite limits, extension of scalars preserves them. The argument includes
empty finite relations and empty profinite test objects. No completeness is used. -/
theorem constantToContinuous_preservesFiniteLimits
    (A : Type u) [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    [IsCommMonObj ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)))]
    (φ : (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} A)) ⟶ Profinite.continuousCoefficientRingObj A)
    [IsMonHom φ]
    (hφ : ∀ (S : Profinite.{u}ᵒᵖ) (a : ULift.{u + 1} A),
      (((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
        _ _ φ).app S) a = ULift.up (ContinuousMap.const S.unop a.down)) :
    PreservesFiniteLimits (Mod.extendScalars φ) := by
  let J := coherentTopology Profinite.{u}
  let P := (Functor.const Profinite.{u}ᵒᵖ).obj
    (AddCommGrpCat.of (ULift.{u + 1} A))
  let R := (constantSheaf J Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} A))
  let : MonObj P := (Functor.const Profinite.{u}ᵒᵖ).monObjObj
    (AddCommGrpCat.of (ULift.{u + 1} A))
  let : MonObj R.obj := (sheafToPresheaf J Ab.{u + 1}).monObjObj R
  let η : P ⟶ R.obj := toSheafify J P
  have hη : IsMonHom η := by
    have h := (sheafificationAdjunction J Ab.{u + 1}).isMonHom_unitAlgHom P
    have he : (inferInstance : MonObj R) =
        (presheafToSheaf J Ab.{u + 1}).monObjObj P :=
      Functor.monObjObj_comp (Functor.const Profinite.{u}ᵒᵖ)
        (presheafToSheaf J Ab.{u + 1}) (AddCommGrpCat.of (ULift.{u + 1} A))
    have he' := congrArg (fun m : MonObj R ↦
      @Functor.monObjObj _ _ _ _ _ _ (sheafToPresheaf J Ab.{u + 1}) _ R m) he
    exact @IsMonHom.of_eq _ _ _ _ _ _ _ _ _ _ rfl he'.symm h
  let RR := InternalAbelianSheafModule.sectionRingSheaf J R
  let ι (S : Profinite.{u}ᵒᵖ) : A →+* RR.obj.obj S :=
    { ((η.app S).hom.comp
        (ULift.moduleEquiv.symm : A ≃ₗ[A] ULift.{u + 1} A).toAddMonoidHom) with
      map_one' := by
        have h := congr_app (IsMonHom.one_hom (f := η)) S
        change (η.app S) (ULift.up (1 : A)) = _
        have he := ConcreteCategory.congr_hom h (ULift.up (1 : ℤ))
        change (η.app S) (ULift.up ((1 : ℤ) : A)) = (1 : RR.obj.obj S) at he
        simpa using he
      map_mul' := fun a b ↦ ConcreteCategory.congr_hom
        (congr_app (IsMonHom.mul_hom (f := η)) S) (ULift.up a ⊗ₜ[ℤ] ULift.up b) }
  let N := (Mod.comap φ).obj (Mod.regular (Profinite.continuousCoefficientRingObj A))
  let M := (InternalAbelianSheafModule.sectionModuleFunctor J R).obj N
  have hsmul (S : Profinite.{u}ᵒᵖ) (a : A) (s : M.val.obj S) :
      ι S a • s = a • (show ULift.{u + 1} C(S.unop, A) from s) := by
    have he := hφ S (ULift.up a)
    change (φ.hom.app S) ((η.app S) (ULift.up a)) = _ at he
    change ((φ.hom.app S) ((η.app S) (ULift.up a))) = _ at he
    let : MonObj (Profinite.continuousCoefficientRingObj A).obj := inferInstanceAs
      (MonObj (Profinite.continuousCoefficientRingPresheaf A ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1}))
    have hm := Sheaf.μ_comp_map_mul (Profinite.continuousCoefficientRingObj A)
    let F := sheafToPresheaf J Ab.{u + 1}
    change ((Functor.LaxMonoidal.μ F R (Profinite.continuousCoefficientRingObj A) ≫
      F.map (φ ▷ (Profinite.continuousCoefficientRingObj A) ≫ MonObj.mul)).app S).hom
        (((η.app S) (ULift.up a)) ⊗ₜ[ℤ]
          (show ULift.{u + 1} C(S.unop, A) from s)) = _
    rw [F.map_comp, ← Functor.LaxMonoidal.μ_natural_left_assoc, hm]
    change (show ULift.{u + 1} C(S.unop, A) from
      (φ.hom.app S) ((η.app S) (ULift.up a))) *
        (show ULift.{u + 1} C(S.unop, A) from s) = _
    rw [he]
    rfl
  have hflat (S : Profinite.{u}ᵒᵖ) : Module.Flat A (ULift.{u + 1} C(S.unop, A)) := by
    have : Module.IsTorsionFree A (ULift.{u + 1} C(S.unop, A)) := by
      apply Module.IsTorsionFree.of_smul_eq_zero
      intro a f h
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        apply ULift.ext
        apply ContinuousMap.ext
        intro x
        have hx : a * f.down x = 0 := congrArg (fun g ↦ g.down x) h
        exact (mul_eq_zero.mp hx).resolve_left ha
    infer_instance
  have hlifts (U : Profinite.{u}) (n : ℕ) (a : Fin n → RR.obj.obj (op U)) :
      ∃ S : Sieve U, S ∈ J U ∧ ∀ V (f : V ⟶ U), S f →
        ∃ c : Fin n → A, ∀ i, ι (op V) (c i) = RR.obj.map f.op (a i) := by
    induction n with
    | zero =>
      refine ⟨⊤, J.top_mem U, ?_⟩
      intro V f hf
      exact ⟨Fin.elim0, fun i ↦ Fin.elim0 i⟩
    | succ n ih =>
      obtain ⟨S, hS, hs⟩ := ih (fun i ↦ a i.succ)
      refine ⟨Presheaf.imageSieve η (a 0) ⊓ S,
        J.intersection_covering (Presheaf.imageSieve_mem J η (a 0)) hS, ?_⟩
      intro V f hf
      obtain ⟨c, hc⟩ := hs V f hf.2
      obtain ⟨c₀, hc₀⟩ := hf.1
      refine ⟨Fin.cons c₀.down c, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j ↦ hc j) i
      exact hc₀
  have hN : ObjectProperty.flat N := by
    apply (InternalAbelianSheafModule.flat_iff_sectionModule J R N).mpr
    apply (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, u + 1}
      RR M).mpr
    intro U n a s hs
    obtain ⟨S, hS, hl⟩ := hlifts U n a
    refine ⟨S, hS, ?_⟩
    intro V f hf
    obtain ⟨c, hc⟩ := hl V f hf
    let s' : Fin n → ULift.{u + 1} C(V, A) := fun i ↦ M.val.map f.op (s i)
    have he : ∑ i, c i • s' i = 0 := by
      have h := congrArg (fun z ↦ M.val.map f.op z) hs
      simp only [map_sum, M.val.map_smul, map_zero] at h
      change (∑ i, RR.obj.map f.op (a i) • M.val.map f.op (s i)) = 0 at h
      simpa only [← hc, hsmul] using h
    have := hflat (op V)
    obtain ⟨l, b, t, hst, hcb⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero he
    refine ⟨l, (fun i j ↦ ι (op V) (b i j)), t, ?_, ?_⟩
    · intro i
      simpa only [hsmul] using hst i
    · intro j
      simpa only [hc, map_sum, map_mul, map_zero] using
        congrArg (ι (op V)) (hcb j)
  have ht : PreservesFiniteLimits (tensorLeft N) :=
    (ObjectProperty.flat_iff_preservesFiniteLimits N).mp hN
  have : PreservesFiniteLimits (Mod.extendScalars φ ⋙ Mod.forget _) :=
    preservesFiniteLimits_of_natIso (Mod.extendForgetTensorIso φ).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (Mod.extendScalars φ) (Mod.forget _)

end AlgebraicGeometry.ProEtale.FiniteConstantModel
