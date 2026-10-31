/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.ConstantRingSheaf
public import WeilConjectures.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import WeilConjectures.CategoryTheory.ConstantModuleFiniteTypeReflection
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.ProEtaleCoefficients.ConstantModuleObjectLocalGeneration

/-! Sectionwise finite type from constructibility of a constant internal module.

This is Step 2 (the one-point stratum and local generation) of the three-step proof
of `constantKernelConstructibilityReflection`.  It packages the comparison from
an internal constant module object and its finite presentations on pro-etale
pullbacks to finite type of the sectionwise constant module sheaf.

Source: literature/blueprint/latest/blueprint/sec-proetale-coefficients/
  sk-prop-sf-open-closed-triangle/det-def-sfb-bounded-constructible.proof.md,
  Counterexample construction: reduction to finite type on the separably closed point.
(blueprint: lem-sfb-constant-kernel-sectionwise-finite-type)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Constructibility of a constant module on a separably closed point gives
finite type for its sectionwise constant module sheaf.

Proof. A constructibility stratification `(X_a)` of the one-point scheme `X = Spec k` has a
stratum `X_a = X`; its immersion `g_a : Z_a → X` is an open immersion onto `X` followed by a
closed immersion `Spec (k/I) → Spec k` with `I ≠ k`, so `I = 0` and `g_a` is an isomorphism.
Local finite presentation of `g_a^* P̲` gives a pro-etale covering `{u_i : U_i → Z_a}` and
epimorphisms `(u_i^* g_a^* R)^{n_i} → u_i^* g_a^* P̲` (cokernel maps of finite presentations).
The family `{g_a ∘ u_i}` covers `X`, and `constantModuleObjectLocalGeneration` turns each
epimorphism into `n_i` sections of the sectionwise constant module over `U_i` generating it on
the slice over `U_i`. Pulling the covering back to any object `V` gives local generators over
`V ×_X U_i`, so the sectionwise constant module sheaf is of finite type.
Source: blueprint det-def-sfb-bounded-constructible, Counterexample construction
(blueprint: lem-sfb-constant-kernel-sectionwise-finite-type). -/
theorem constantKernel_sectionwiseFiniteType
    (k : Type u) [Field k] [IsSepClosed k]
    (X : Scheme.{u})
    (hX : X = Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))
    {B : Type (u + 1)} [CommRing B]
    {P : Type (u + 1)} [AddCommGroup P] [Module B P]
    (hconstructible : IsConstructibleModuleObject
      (Sheaf.constRingSheaf (Scheme.ProEt.topology X) B)
      (((presheafToSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).mapMod
          (Presheaf.constRingObj (C := X.ProEt) B)).obj
        (Presheaf.toMod B
          ((Functor.const X.ProEtᵒᵖ).obj (ModuleCat.of B P))))) :
    SheafOfModules.IsFiniteType.{u + 1, u, u + 1}
      ((siteConstantModuleFunctorGeneral (Scheme.ProEt.topology X) B).obj
        (ModuleCat.of B P)) := by
  classical
  subst X
  rcases hconstructible with ⟨S, hS⟩
  have hpoint : Nonempty (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) := by
    exact ⟨(PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance).some⟩
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp
    (S.iUnion_stratum_eq_univ.symm ▸ Set.mem_univ (Classical.choice hpoint))
  rw [← S.range_immersion a] at ha
  obtain ⟨z, hz⟩ := ha
  let : Nonempty (S.domain a) := ⟨z⟩
  let : IsIso (S.immersion a) := IsImmersion.isIso_of_nonempty _
  obtain ⟨𝒰, h𝒰⟩ := hS a
  let : ∀ i, WeaklyEtale (𝒰.f i) := fun i => 𝒰.forgetQc.map_prop i
  let 𝒱₀ : Scheme.Cover (Scheme.propQCPrecoverage @WeaklyEtale)
      (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
    𝒰.pushforward (S.immersion a)
      (Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance)
  let 𝒱 : Scheme.Cover.{u + 1} (Scheme.propQCPrecoverage @WeaklyEtale)
      (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))) :=
    𝒱₀.reindex (Equiv.ulift : ULift.{u + 1} 𝒱₀.I₀ ≃ 𝒱₀.I₀)
  let : ∀ i, WeaklyEtale (𝒱.f i) := fun i => 𝒱.forgetQc.map_prop i
  let W : 𝒱.I₀ → (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))).ProEt :=
    fun i => Scheme.ProEt.mk (𝒱.f i)
  have hcov : (Scheme.ProEt.topology _).CoversTop W := by
    let hT : IsTerminal (Scheme.ProEt.mk (𝟙
        (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))) :=
      Scheme.ProEt.isTerminalMkId _
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ _ hT]
    let ff : ∀ i, W i ⟶ Scheme.ProEt.mk (𝟙 _) := fun i =>
      MorphismProperty.Over.homMk (𝒱.f i) (Category.comp_id _)
    rw [← Sieve.ofArrows_eq_ofObjects hT W ff]
    apply Precoverage.generate_mem_toGrothendieck
    rw [Scheme.ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    change 𝒱.presieve₀ ∈ Scheme.proetalePrecoverage _
    exact 𝒱.mem₀
  dsimp [Mod.IsFinitelyPresented] at h𝒰
  let F := (siteConstantModuleFunctorGeneral
    (Scheme.ProEt.topology (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))) B).obj
      (ModuleCat.of B P)
  choose n m f he using h𝒰
  let e := fun i => Classical.choice (he i)
  let p := fun i => cokernel.π (f i) ≫ (e i).inv
  have hp (i : 𝒰.I₀) : Epi (p i) := by dsimp [p]; infer_instance
  let : ∀ i, Epi (p i) := hp
  let : ∀ i, WeaklyEtale (𝒰.f i ≫ S.immersion a) := fun i => inferInstance
  have hgen (i : 𝒰.I₀) := constantModuleObjectLocalGeneration
    (S.immersion a) (𝒰.f i) B P (n i) (p i)
  choose s t ht hst using hgen
  let q : SheafOfModules.LocalGeneratorsData.{u + 1} F := {
    I := 𝒱.I₀
    X := W
    coversTop := hcov
    generators := fun i ↦ by
      simpa [F, W, localGenerationRestrictedModule] using
        ({ I := ULift.{u + 1} (Fin (n i.down))
           s := t i.down
           epi := ht i.down } :
          (localGenerationRestrictedModule _ (Scheme.ProEt.mk (𝒱.f i)) B P).GeneratingSections) }
  have hq : q.IsFiniteType := by
    constructor
    intro i
    apply SheafOfModules.GeneratingSections.IsFiniteType.mk
    dsimp [q]
    infer_instance
  exact ⟨q, hq⟩

end AlgebraicGeometry.ProEtale
