/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.Filtration
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernelAffineStalkFiltration

/-! # Stalk presentations of stabilized kernel images

Stacks Project, Tag 087X.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

private theorem intersection_filtration_bound
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (K : Ideal R) (N : ModuleCat.{u} R) [Module.Finite R N] (L : Submodule R N) :
    ∃ b : ℕ, ∀ (n d : ℕ), b ≤ d →
      (K ^ (n + d + 1) • (⊤ : Submodule R N)).comap L.subtype ≤
        K ^ (n + 1) • (⊤ : Submodule R L) := by
  obtain ⟨b, hb⟩ := K.exists_pow_inf_eq_pow_smul L
  refine ⟨b, fun n d hd ↦ ?_⟩
  apply (Submodule.map_le_map_iff_of_injective L.subtype_injective _ _).mp
  rw [Submodule.map_comap_subtype, Submodule.map_smul'', Submodule.map_subtype_top,
    inf_comm, hb (n + d + 1) (by omega)]
  exact (smul_mono_right _ inf_le_right).trans
    (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)))

/-- The stabilized image system has compatible surjective stalk presentations with an
eventually bounded kernel filtration.
(Stacks, Tag 087X). -/
theorem coherentFormalModule_kernel_stalk_presentation
    {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (F H : CoherentFormalModule X I) (α : F ⟶ H)
    (c : ℕ) (S : ℕᵒᵖ ⥤ X.Modules) (j : S ⟶ F.obj)
    (hc : ∀ (l m : ℕ) (h : m + c ≤ l),
      Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op l)) ≫
            F.obj.map (homOfLE (Nat.le_trans (Nat.le_add_right m c) h)).op)) =
        Subobject.mk
          (Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
            F.obj.map (homOfLE (Nat.le_add_right m c)).op)))
    (hS : ∀ m : ℕ, ∃ e : S.obj (op m) ≅
      Abelian.image (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op),
      e.hom ≫ Abelian.image.ι (kernel.ι (α.hom.app (op (m + c))) ≫
        F.obj.map (homOfLE (Nat.le_add_right m c)).op) = j.app (op m)) :
    ∃ b : ℕ, ∀ x : X,
      ∀ e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
          (SheafOfModules.unit X.ringCatSheaf) ≅
          ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x),
      (∀ (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)),
        e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
          U x hx r) = X.presheaf.germ U x hx r) →
      let T := RingedSpace.moduleStalkFunctor X.toRingedSpace x
      let J : Ideal (X.presheaf.stalk x) := LinearMap.range (T.map I.toModulesι ≫ e.hom).hom
      ∃ M : ModuleCat.{u} (X.presheaf.stalk x),
        ∃ p : ∀ m : ℕ, M →ₗ[X.presheaf.stalk x] T.obj (S.obj (op m)),
          (∀ m : ℕ, Function.Surjective (p m)) ∧
          (∀ (a b : ℕ) (h : a ≤ b) (z : M),
            (T.map (S.map (homOfLE h).op)).hom (p b z) = p a z) ∧
          (∀ (d : ℕ), max c b ≤ d → ∀ n : ℕ,
            LinearMap.ker (p (n + d)) ≤
              J ^ (n + 1) • (⊤ : Submodule (X.presheaf.stalk x) M)) := by
  classical
  have local_bound (U : X.affineOpens) : ∃ b : ℕ, ∀ (x : X), x ∈ U.1 →
      ∀ e : (RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj
          (SheafOfModules.unit X.ringCatSheaf) ≅
          ModuleCat.of (X.presheaf.stalk x) (X.presheaf.stalk x),
      (∀ (V : X.Opens) (hx : x ∈ V) (r : Γ(X, V)),
        e.hom (TopCat.Presheaf.germ (SheafOfModules.unit X.ringCatSheaf).val.presheaf
          V x hx r) = X.presheaf.germ V x hx r) →
      let T := RingedSpace.moduleStalkFunctor X.toRingedSpace x
      let J : Ideal (X.presheaf.stalk x) := LinearMap.range (T.map I.toModulesι ≫ e.hom).hom
      ∃ M : ModuleCat.{u} (X.presheaf.stalk x),
        ∃ p : ∀ m : ℕ, M →ₗ[X.presheaf.stalk x] T.obj (S.obj (op m)),
          (∀ m : ℕ, Function.Surjective (p m)) ∧
          (∀ (a b : ℕ) (h : a ≤ b) (z : M),
            (T.map (S.map (homOfLE h).op)).hom (p b z) = p a z) ∧
          (∀ (d : ℕ), b ≤ d → ∀ n : ℕ,
            LinearMap.ker (p (n + d)) ≤
              J ^ (n + 1) • (⊤ : Submodule (X.presheaf.stalk x) M)) := by
    let A := Γ(X, U.1)
    let R := AdicCompletion (I.ideal U) A
    let K := (I.ideal U).map (algebraMap A R)
    have : IsNoetherianRing A := IsLocallyNoetherian.component_noetherian U
    have : IsNoetherianRing R := AdicCompletion.isNoetherianRing (I.ideal U)
    obtain ⟨N, hN, L, hmodel⟩ :=
      coherentFormalModule_kernel_affine_stalk_filtration I F H α c S j hc hS U
    have : Module.Finite R N := hN
    obtain ⟨b, hb⟩ := intersection_filtration_bound K N L
    refine ⟨b, ?_⟩
    intro x hx e he
    obtain ⟨M, p, hp, ht, φ, hφ, hk⟩ := hmodel x hx e he
    refine ⟨M, p, hp, ht, ?_⟩
    intro d hd n
    rw [hk, ← hφ (n + 1)]
    exact φ.monotone (hb n d hd)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun U : X.affineOpens ↦ (U.1 : Set X)) (fun U ↦ U.1.isOpen) (by
      intro x _
      obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hx⟩)
  choose b hb using local_bound
  refine ⟨s.sup b, ?_⟩
  intro x e he
  obtain ⟨U, hx⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
  obtain ⟨hUs, hxU⟩ := Set.mem_iUnion.mp hx
  obtain ⟨M, p, hp, ht, hk⟩ := hb U x hxU e he
  refine ⟨M, p, hp, ht, ?_⟩
  intro d hd n
  exact hk d ((Finset.le_sup hUs).trans ((le_max_right c (s.sup b)).trans hd)) n

end AlgebraicGeometry
