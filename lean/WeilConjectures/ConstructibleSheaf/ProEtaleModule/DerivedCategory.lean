/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.Paper.IntegralConstructibleSerre
import Sheaf.Paper.ConstructibleCokernelsExtensions
import Sheaf.Paper.FiniteDiscreteConstructibleKernels

/-!

# Bounded constructible derived categories of sheaves of modules on the pro-étale site

Let `A` be a closed symmetric monoidal Grothendieck abelian category, `X` a scheme, `R` a
commutative ring object of `Sheaf (Scheme.ProEt.topology X) A`. The derived category of
sheaves of `R`-modules is
```
D(X_proét, R) := DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R).
```
The *bounded constructible* derived category `ProEtale.BoundedConstructible R` is the full
subcategory of `D(X_proét, R)` (`ProEtale.boundedConstructible R`) consisting of the complexes
`K` such that

1. `K` is bounded, i.e. `Hⁱ(K) = 0` for `i` outside a finite interval (for the canonical
   t-structure, see `ProEtale.mem_boundedConstructible_iff`);
2. every cohomology sheaf `Hⁱ(K)` is constructible (`ProEtale.IsConstructibleModuleObject R`).

Morphisms are computed in `D(X_proét, R)`. For `R = 𝒪_{E,X}` this is `D_cons(X_proét, 𝒪_E)`;
for `R = E_X` it is `D_cons(X_proét, E)`.
No derived completeness condition is imposed.

## Sorried input

For the coefficient rings `Λ_X = p_X^* Λ` of Deligne's finiteness theorems
(`Λ = 𝒪̲_E, E̲, ℚ̲̄_ℓ` or a finite `ℓ`-power torsion ring,
`AlgebraicGeometry.ProEtale.CondensedRing.IsFinitenessCoefficient`), the bounded constructible
complexes on a topologically noetherian scheme form a triangulated subcategory
(`ProEtale.isTriangulated_boundedConstructible`). This rests on the fact that constructible
sheaves of `Λ_X`-modules on such a scheme are closed under kernels, cokernels and extensions
(Bhatt–Scholze, Section 6.8), which is not formalized; the instance is `sorry`ed. It is false
for a general commutative ring object `R`: for `X = Spec k̄` and `R` the constant sheaf of the
non-coherent ring `k[x₁, x₂, …]/(x₁xᵢ)ᵢ`, the cone of `x₁ : R ⟶ R` has `H⁻¹` the constant sheaf
of the ideal `(x₂, x₃, …)`, which is not finitely generated. Noetherianity is assumed only there:
the definition `ProEtale.boundedConstructible` makes sense on any scheme. The derived category
itself uses the `sorry`ed instances of
`WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory`.

-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory MonObj Limits

namespace AlgebraicGeometry.ProEtale

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  {X : Scheme.{u}}
  (R : Sheaf (Scheme.ProEt.topology X) A) [MonObj R] [IsCommMonObj R]

/-- The bounded constructible complexes of sheaves of `R`-modules on `X`: the complexes `K`
which are bounded for the canonical t-structure and all of whose cohomology sheaves `Hⁿ(K)`
are constructible. -/
noncomputable def boundedConstructible :
    ObjectProperty (DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)) :=
  DerivedCategory.TStructure.t.bounded ⊓ fun K ↦ ∀ n : ℤ,
    IsConstructibleModuleObject R ((DerivedCategory.homologyFunctor _ n).obj K)

omit [IsCommMonObj R] in
/-- A complex is bounded constructible iff its cohomology sheaves vanish outside a finite
interval `[a, b]` and are all constructible. -/
lemma mem_boundedConstructible_iff
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) A) R)) :
    boundedConstructible R K ↔
      (∃ a b : ℤ, ∀ i : ℤ, (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
      ∀ n : ℤ, IsConstructibleModuleObject R ((DerivedCategory.homologyFunctor _ n).obj K) := by
  refine and_congr_left' ⟨?_, ?_⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨a, b, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff K a).1 ha i hi
    · exact (DerivedCategory.isLE_iff K b).1 hb i hi
  · rintro ⟨a, b, h⟩
    exact ⟨⟨a, (DerivedCategory.isGE_iff K a).2 fun i hi ↦ h i (Or.inl hi)⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).2 fun i hi ↦ h i (Or.inr hi)⟩⟩

/-- The bounded constructible derived category `D_cons(X_proét, R)`. -/
abbrev BoundedConstructible : Type _ :=
  (boundedConstructible R).FullSubcategory

open Opposite Functor.LaxMonoidal Functor.OplaxMonoidal
open scoped CategoryTheory.Obj ZeroObject

private lemma constructible_zero
    (X : Scheme.{u}) (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] :
    IsConstructibleModuleObject R (0 : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  refine ⟨S, fun a ↦ ?_⟩
  refine ⟨.singleton (𝟙 _) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨0, 0, 𝟙 _, ⟨?_⟩⟩
  exact (((ProEtale.upperStar Ab.{u + 1} _).mapMod _).map_isZero
    (((ProEtale.upperStar Ab.{u + 1} _).mapMod R).map_isZero (isZero_zero _))).iso
      (isZero_cokernel_of_epi (𝟙 _))

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
  have : ObjectProperty.IsClosedUnderIsomorphisms (IsConstructibleModuleObject R) :=
    ⟨fun e hM ↦ _root_.constructible_of_iso e hM⟩
  have : ObjectProperty.ContainsZero (IsConstructibleModuleObject R) :=
    ⟨0, isZero_zero _, constructible_zero X R⟩
  change (DerivedCategory.TStructure.t.bounded ⊓
    DerivedCategory.homologyProperty (IsConstructibleModuleObject R)).IsTriangulated
  infer_instance

open CondensedRing in
open scoped CategoryTheory.Obj in
-- The prime `ℓ` occurs only in the hypothesis `IsFinitenessCoefficient ℓ Λ`; it is found from
-- that instance, so the synthesis order is not the default one.
set_option synthInstance.checkSynthOrder false in
/-- For the coefficient rings `Λ_X` of Deligne's finiteness theorems (`Λ = 𝒪̲_E, E̲, ℚ̲̄_ℓ` or a
finite `ℓ`-power torsion ring), the bounded constructible complexes on a topologically noetherian
scheme form a triangulated subcategory. -/
instance isTriangulated_boundedConstructible
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {ℓ : ℕ} [Fact ℓ.Prime] [IsFinitenessCoefficient ℓ Λ] (X : Scheme.{u})
    [TopologicalSpace.NoetherianSpace X] :
    (boundedConstructible (condensedRingObj Λ X)).IsTriangulated := by
  cases (inferInstance : IsFinitenessCoefficient ℓ Λ) with
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
    exact triangulated_of_serre X _
      (fun M N f hM hN ↦ ⟨ObjectProperty.prop_kernel _ f hM hN,
        ObjectProperty.prop_cokernel _ f hM hN⟩)
      (fun S hS h₁ h₃ ↦ ObjectProperty.prop_X₂_of_shortExact _ hS h₁ h₃)
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
    exact triangulated_of_serre X _
      (fun M N f hM hN ↦ ⟨ObjectProperty.prop_kernel _ f hM hN,
        ObjectProperty.prop_cokernel _ f hM hN⟩)
      (fun S hS h₁ h₃ ↦ ObjectProperty.prop_X₂_of_shortExact _ hS h₁ h₃)
  | torsion T n hn =>
    obtain ⟨hc, he⟩ := constructible_cokernels_extensions X
      (condensedRingObj (Profinite.continuousMapRingObj T) X)
    exact triangulated_of_serre X _
      (fun M N f hM hN ↦ ⟨finiteDiscrete_constructible_kernel T X M N f hM hN,
        ObjectProperty.prop_cokernel _ f hM hN⟩)
      (fun S hS h₁ h₃ ↦ ObjectProperty.prop_X₂_of_shortExact _ hS h₁ h₃)


end AlgebraicGeometry.ProEtale
