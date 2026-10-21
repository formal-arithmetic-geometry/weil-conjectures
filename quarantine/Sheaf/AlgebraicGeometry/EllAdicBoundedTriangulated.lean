/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.Paper.IntegralConstructibleSerre
public import Sheaf.UpstreamExtra.WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory

/-! # Triangulated closure for the ell-adic finiteness coefficient class

The field cases use local finite freeness. The integral cases use the integral Serre
criterion. These are exactly the heart-closure inputs in the last step of blueprint
`lem-sfb-dc-tensor-preserves`.
-/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private lemma continuous_lf (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X))
    (hM : IsLocallyFinitelyPresented (condensedRingObj (Profinite.continuousMapRingObj E) X) M) :
    ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i,
      Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((upperStar Ab.{u + 1} (U.f i)).mapMod
          (condensedRingObj (Profinite.continuousMapRingObj E) X)).obj M) := by
  let E' := ULift.{u} E
  let : NormedField E' :=
    { (inferInstance : NormedCommRing E'), (inferInstance : Field E') with
      norm_mul a b := norm_mul a.down b.down }
  have : IsCommMonObj (Profinite.continuousCoefficientRingObj E') :=
    Sheaf.isCommMonObj_sheafCompose_obj
      (coherentTopology Profinite.{u}) (Profinite.continuousCoefficientRingSheaf E')
      (by
        intro S a b
        apply ULift.ext
        change (a.down * b.down : C(S.unop, E')) = b.down * a.down
        exact mul_comm a.down b.down)
  let e := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (liftCoefficientIso E)
  let φ := (upperStarFromPoint X).map e.hom
  have : IsMonHom e.hom := Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (liftCoefficientIso E).hom
  have : IsMonHom φ := inferInstance
  have h := exists_finiteFree_cover_of_condensedField_lfp ℓ E' X
    ((Mod.comap (inv φ)).obj M) (lfp_comap (inv φ) hM)
  exact locally_free_of_iso (locally_free_comap φ h)
    ((Mod.comapEquivalenceOfIsIso φ).counitIso.app M)


private lemma triangulated_of_serre
    (X : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    (hk : ∀ (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
      (f : M ⟶ N), IsConstructibleModuleObject R M →
      IsConstructibleModuleObject R N →
      IsConstructibleModuleObject R (kernel f) ∧
      IsConstructibleModuleObject R (cokernel f))
    (he : ∀ S : ShortComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R),
      S.ShortExact → IsConstructibleModuleObject R S.X₁ →
      IsConstructibleModuleObject R S.X₃ → IsConstructibleModuleObject R S.X₂) :
    (boundedConstructible R).IsTriangulated := by
  let : ObjectProperty.IsClosedUnderKernels (IsConstructibleModuleObject R) :=
    ⟨by
      rintro _ ⟨f, s, hs, hf⟩
      exact _root_.constructible_of_iso (R := R) (limit.isoLimitCone ⟨s, hs⟩)
        (hk _ _ f hf.1 hf.2).1⟩
  let : ObjectProperty.IsClosedUnderCokernels (IsConstructibleModuleObject R) :=
    ⟨by
      rintro _ ⟨f, s, hs, hf⟩
      exact _root_.constructible_of_iso (R := R) (colimit.isoColimitCocone ⟨s, hs⟩)
        (hk _ _ f hf.1 hf.2).2⟩
  let : ObjectProperty.IsClosedUnderExtensions (IsConstructibleModuleObject R) := ⟨he _⟩
  exact isTriangulated_boundedConstructible_of_serre R

namespace CondensedRing

/-- The bounded constructible module-object category is triangulated for every ell-adic
finiteness coefficient. Field presentations become locally free, so the constructible
heart is Serre; the integral cases are the integral constructible Serre theorem. Applying
homology to distinguished triangles gives triangulated closure.
Source: Bhatt--Scholze, Proposition 6.8.11(1),(3), and the heart-closure inputs in
`lem-sfb-dc-tensor-preserves`, step 10.
(blueprint: lem-sfb-dc-ell-adic-triangulated) -/
theorem isTriangulated_boundedConstructible_ellAdic
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {ℓ : ℕ} [h : IsEllAdicFinitenessCoefficient ℓ Λ]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    (boundedConstructible (condensedRingObj Λ X)).IsTriangulated := by
  cases h with
  | continuous E =>
    obtain ⟨hk, he⟩ := condensed_constructible_serre_of_locally_free freeEpiLocalSplitting
      (Profinite.continuousMapRingObj E) (continuous_lf ℓ E) X
    exact triangulated_of_serre X _ hk he
  | integral E =>
    let := PadicAlgCl.normedFieldOfAlgebra ℓ E
    let : NormedAlgebra ℚ_[ℓ] E :=
      { norm_smul_le c x := by
          change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
            ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
            PadicAlgCl.norm_extends] }
    obtain ⟨hker, hcok, hext⟩ := integralConstructible_serre ℓ E X
    change ObjectProperty.IsClosedUnderKernels
      (IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) at hker
    change ObjectProperty.IsClosedUnderCokernels
      (IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) at hcok
    change ObjectProperty.IsClosedUnderExtensions
      (IsConstructibleModuleObject
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X)) at hext
    exact isTriangulated_boundedConstructible_of_serre _
  | algebraicClosure =>
    obtain ⟨hk, he⟩ := isConstructibleModuleObject_serre_padicAlgCl X ℓ
    exact triangulated_of_serre X _ hk he
  | unitBall E O hO =>
    have h : O = continuousIntegers ℓ E := by
      ext x
      rw [hO]
      change ‖x‖ ≤ 1 ↔ ‖x‖₊ ≤ 1
      simpa only [NNReal.coe_one, coe_nnnorm] using
        (NNReal.coe_le_coe : (‖x‖₊ : ℝ) ≤ ((1 : NNReal) : ℝ) ↔ ‖x‖₊ ≤ 1)
    subst O
    obtain ⟨hker, hcok, hext⟩ := integralConstructible_serre ℓ E X
    exact isTriangulated_boundedConstructible_of_serre _

end CondensedRing
end AlgebraicGeometry.ProEtale
