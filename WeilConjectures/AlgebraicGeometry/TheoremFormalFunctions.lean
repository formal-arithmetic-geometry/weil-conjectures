/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.AlgebraicGeometry.MLCohomologyPowersIdeal
import WeilConjectures.AlgebraicGeometry.FormalFunctionsPowerKernel
import WeilConjectures.Algebra.Module.AdicCompletionStableRanges
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-! # The theorem on formal functions

The index n represents the positive level n+1. The comparison is specified on every
limit projection, so the asserted isomorphism is the canonical one, not an arbitrary
isomorphism of the two modules. The degree-zero assertion uses actual global sections.
H^p and Γ are A-modules by restriction of scalars along (ΓSpecIso A).inv ≫ f.appTop.

## References

* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The canonical maps on quotients induce an A-linear isomorphism of inverse limits.
-/
theorem theorem_formal_functions {A : Type v} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) (p : ℕ) :
    ∃ θ : ∀ n : ℕ,
        ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F ⧸
          (I ^ (n + 1) • ⊤ : Submodule A ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F))) →ₗ[A]
        (RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
          (formalModuleQuotient J (n + 1) F),
      (∀ n : ℕ, (θ n).comp
        (Submodule.mkQ (I ^ (n + 1) • ⊤ : Submodule A
          ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F))) =
          ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
          (formalModuleQuotientπ J (n + 1) F)).hom) ∧
      (∀ (n m : ℕ) (h : n ≤ m),
        ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
          (formalModuleQuotientMap J (𝟙 F) (Nat.succ_le_succ h))).hom.comp (θ m) =
        (θ n).comp (AdicCompletion.transitionMap I
          ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F)
          (Nat.succ_le_succ h))) ∧
      ∃ e : ModuleCat.of A (AdicCompletion I ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F)) ≅
          limit (formalCompletionSystem J F ⋙
            (RingedSpace.moduleCohomology X.toRingedSpace p ⋙ ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)),
        ∀ n : ℕ, e.hom ≫
          limit.π (formalCompletionSystem J F ⋙
            (RingedSpace.moduleCohomology X.toRingedSpace p ⋙ ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)) (op n) =
          ModuleCat.ofHom ((θ n).comp
            (AdicCompletion.eval I ((RingedSpace.moduleCohomology X.toRingedSpace p ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F) (n + 1))) := by
  let C := RingedSpace.moduleCohomology X.toRingedSpace p ⋙
    ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom
  let H := C.obj F
  let M := formalCompletionSystem J F ⋙ C
  let ρ : ∀ n : ℕ, H →ₗ[A] M.obj (op n) :=
    fun n ↦ (C.map (formalModuleQuotientπ J (n + 1) F)).hom
  have hkill (n : ℕ) : (I ^ (n + 1) • ⊤ : Submodule A H) ≤ (ρ n).ker :=
    formalFunctions_power_le_ker I f J hJ F p (n + 1)
  let θ : ∀ n : ℕ, (H ⧸ (I ^ (n + 1) • ⊤ : Submodule A H)) →ₗ[A]
      M.obj (op n) := fun n ↦ (I ^ (n + 1) • (⊤ : Submodule A H)).liftQ (ρ n) (hkill n)
  have hθ (n : ℕ) : (θ n).comp (Submodule.mkQ (I ^ (n + 1) • ⊤)) = ρ n :=
    Submodule.liftQ_mkQ _ _ _
  have hρ (n m : ℕ) (h : n ≤ m) :
      (M.map (homOfLE h).op).hom.comp (ρ m) = ρ n := by
    change (C.map (formalModuleQuotientπ J (m + 1) F) ≫
      C.map (formalModuleQuotientMap J (𝟙 F) (Nat.succ_le_succ h))).hom = _
    rw [← C.map_comp]
    simp [formalModuleQuotientMap, formalModuleQuotientπ, ρ]
  have htrans (n m : ℕ) (h : n ≤ m) :
      (M.map (homOfLE h).op).hom.comp (θ m) =
        (θ n).comp (AdicCompletion.transitionMap I H (Nat.succ_le_succ h)) := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ := (I ^ (m + 1) • (⊤ : Submodule A H)).mkQ_surjective x
    have hleft := LinearMap.congr_fun (hθ m) y
    have hright := LinearMap.congr_fun (hθ n) y
    have hrho := LinearMap.congr_fun (hρ n m h) y
    simpa [LinearMap.comp_apply, AdicCompletion.transitionMap, Submodule.factorPow,
      Submodule.factor, Submodule.mapQ_apply] using
        (congrArg (M.map (homOfLE h).op).hom hleft).trans (hrho.trans hright.symm)
  obtain ⟨c, hker, hrange, _⟩ := ml_cohomology_powers_ideal f I F hF p
  subst J
  have hk (n : ℕ) : (ρ (n + c)).ker ≤ I ^ (n + 1) • (⊤ : Submodule A H) := by
    have hexp : n + c + 1 - c = n + 1 := by omega
    simpa [ρ, C, H, M, hexp] using
      hker (n + c + 1) (by omega) (by omega)
  have hi (n : ℕ) :
      Set.range (M.map (homOfLE (Nat.le_add_right n c)).op).hom =
        Set.range (ρ n) := by
    simpa [ρ, C, M, formalCompletionSystem, Set.range,
      ModuleCat.restrictScalars, ModuleCat.RestrictScalars.obj',
      ModuleCat.RestrictScalars.map'] using!
      hrange (n + 1) (n + c + 1) (by omega) (by omega)
  obtain ⟨e, he⟩ := adicCompletion_iso_of_stable_ranges I H M ρ θ hθ htrans c hk hi
  exact ⟨θ, hθ, htrans, e, he⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The degree-zero formal-functions isomorphism for global sections.
-/
theorem globalSections_formal_functions {A : Type v} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) {X : Scheme.{v}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (J : X.IdealSheafData)
    (hJ : J = (Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)).comap f)
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) :
    ∃ θ : ∀ n : ℕ,
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F ⧸
          (I ^ (n + 1) • ⊤ : Submodule A ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F))) →ₗ[A]
        (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj
          (formalModuleQuotient J (n + 1) F),
      (∀ n : ℕ, (θ n).comp
        (Submodule.mkQ (I ^ (n + 1) • ⊤ : Submodule A
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F))) =
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
          (formalModuleQuotientπ J (n + 1) F)).hom) ∧
      (∀ (n m : ℕ) (h : n ≤ m),
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).map
          (formalModuleQuotientMap J (𝟙 F) (Nat.succ_le_succ h))).hom.comp (θ m) =
        (θ n).comp (AdicCompletion.transitionMap I
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F)
          (Nat.succ_le_succ h))) ∧
      ∃ e : ModuleCat.of A (AdicCompletion I ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F)) ≅
          limit (formalCompletionSystem J F ⋙
            (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙ ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)),
        ∀ n : ℕ, e.hom ≫
          limit.π (formalCompletionSystem J F ⋙
            (RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙ ModuleCat.restrictScalars
            ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom)) (op n) =
          ModuleCat.ofHom ((θ n).comp
            (AdicCompletion.eval I ((RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
          ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom).obj F) (n + 1))) := by
  let R := ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom
  let C := RingedSpace.moduleCohomology X.toRingedSpace 0 ⋙ R
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙ R
  let : PreservesFiniteLimits (RingedSpace.globalSectionsFunctor X.toRingedSpace) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings X.toRingedSpace) (op ⊤)))
  let α : C ≅ G := Functor.isoWhiskerRight
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedZeroIsoSelf R
  let a := (α.app F).toLinearEquiv
  obtain ⟨θ₀, hθ₀, _, e₀, he₀⟩ := theorem_formal_functions I f J hJ F hF 0
  let θ : ∀ n : ℕ,
      (G.obj F ⧸ (I ^ (n + 1) • ⊤ : Submodule A (G.obj F))) →ₗ[A]
        G.obj (formalModuleQuotient J (n + 1) F) :=
    fun n ↦ (α.hom.app (formalModuleQuotient J (n + 1) F)).hom.comp
      ((θ₀ n).comp ((a.symm.toLinearMap.reduceModIdeal (I ^ (n + 1))).restrictScalars A))
  have hθ (n : ℕ) : (θ n).comp
      (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A (G.obj F)))) =
      (G.map (formalModuleQuotientπ J (n + 1) F)).hom := by
    ext x
    change (α.hom.app _).hom
      (θ₀ n ((I ^ (n + 1) • (⊤ : Submodule A (C.obj F))).mkQ (a.symm x))) = _
    have hh := LinearMap.congr_fun (hθ₀ n) (a.symm x)
    change θ₀ n ((I ^ (n + 1) • (⊤ : Submodule A (C.obj F))).mkQ (a.symm x)) =
      (C.map (formalModuleQuotientπ J (n + 1) F)).hom (a.symm x) at hh
    rw [hh]
    have hn := ConcreteCategory.congr_hom
      (α.hom.naturality (formalModuleQuotientπ J (n + 1) F)) (a.symm x)
    change (α.hom.app _).hom ((C.map (formalModuleQuotientπ J (n + 1) F)).hom
      (a.symm x)) = (G.map (formalModuleQuotientπ J (n + 1) F)).hom
        (a (a.symm x)) at hn
    simpa only [a.apply_symm_apply] using hn
  have hρ (n m : ℕ) (h : n ≤ m) :
      (G.map (formalModuleQuotientMap J (𝟙 F) (Nat.succ_le_succ h))).hom.comp
        (G.map (formalModuleQuotientπ J (m + 1) F)).hom =
        (G.map (formalModuleQuotientπ J (n + 1) F)).hom := by
    change (G.map (formalModuleQuotientπ J (m + 1) F) ≫
      G.map (formalModuleQuotientMap J (𝟙 F) (Nat.succ_le_succ h))).hom = _
    rw [← G.map_comp]
    simp [formalModuleQuotientMap, formalModuleQuotientπ]
  have htrans (n m : ℕ) (h : n ≤ m) :
      (G.map (formalModuleQuotientMap J (𝟙 F) (Nat.succ_le_succ h))).hom.comp (θ m) =
        (θ n).comp (AdicCompletion.transitionMap I (G.obj F) (Nat.succ_le_succ h)) := by
    apply LinearMap.ext
    intro x
    obtain ⟨y, rfl⟩ :=
      (I ^ (m + 1) • (⊤ : Submodule A (G.obj F))).mkQ_surjective x
    have hleft := LinearMap.congr_fun (hθ m) y
    have hright := LinearMap.congr_fun (hθ n) y
    have hrho := LinearMap.congr_fun (hρ n m h) y
    simpa [LinearMap.comp_apply, AdicCompletion.transitionMap, Submodule.factorPow,
      Submodule.factor, Submodule.mapQ_apply] using
        (congrArg (G.map (formalModuleQuotientMap J (𝟙 F)
          (Nat.succ_le_succ h))).hom hleft).trans (hrho.trans hright.symm)
  let b : ModuleCat.of A (AdicCompletion I (G.obj F)) ≅
      ModuleCat.of A (AdicCompletion I (C.obj F)) :=
    ((AdicCompletion.congr I a.symm).restrictScalars A).toModuleIso
  let w := Functor.isoWhiskerLeft (formalCompletionSystem J F) α
  let e := b ≪≫ e₀ ≪≫ HasLimit.isoOfNatIso w
  refine ⟨θ, hθ, htrans, e, ?_⟩
  intro n
  change e.hom ≫ limit.π (formalCompletionSystem J F ⋙ G) (op n) =
    ModuleCat.ofHom ((θ n).comp (AdicCompletion.eval I (G.obj F) (n + 1)))
  dsimp only [e, Iso.trans_hom]
  simp only [Category.assoc, HasLimit.isoOfNatIso_hom_π]
  rw [← Category.assoc e₀.hom, he₀]
  apply ModuleCat.hom_ext
  ext x
  rfl

end AlgebraicGeometry
