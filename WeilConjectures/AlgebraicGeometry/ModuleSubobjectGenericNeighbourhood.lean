/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.ConstructibleSheaf.GenericConstancy
import WeilConjectures.AlgebraicGeometry.ModuleGenericGenerators
import WeilConjectures.AlgebraicGeometry.LocalSystemGenericZeroMap
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Local constancy of a module subsheaf near a component generic point -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A subsheaf of a finite locally constant module sheaf is locally constant near each
component generic point (Stacks, Tag 09BH). -/
theorem exists_open_locallyConstant_of_mono_at_genericPoint
    {X : Scheme.{u}} [IsNoetherian X] {Λ : Type (u + 1)} [CommRing Λ]
    [IsNoetherianRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) [Mono φ] [IsFiniteLocallyConstantSheaf G]
    (η : X) (hη : η ∈ genericPoints X) :
    ∃ U : X.Opens, η ∈ U ∧
      IsLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F) := by
  classical
  obtain ⟨U, hU, Y, f, hf, hsurj, hirr, ξ, hgen, _, H, ψ, hmono, hH, hψ⟩ :=
    exists_generic_generating_locallyConstant_subsheaf φ η hη
  have := hf
  have := hsurj
  have := hirr
  have := hmono
  have := hH
  let G' := (Etale.upperStar (ModuleCat.{u + 1} Λ) (f ≫ U.ι)).obj G
  let φ' := (Etale.upperStar (ModuleCat.{u + 1} Λ) (f ≫ U.ι)).map φ
  have : Mono φ' := by dsimp [φ']; infer_instance
  have : IsFiniteLocallyConstantSheaf G' := IsFiniteLocallyConstantSheaf.upperStar (f ≫ U.ι) G
  have : IsFiniteLocallyConstantSheaf (Limits.cokernel (ψ ≫ φ')) :=
    IsFiniteLocallyConstantSheaf.cokernel (ψ ≫ φ')
  have hzero : φ' ≫ Limits.cokernel.π (ψ ≫ φ') = 0 := by
    apply eq_zero_of_generic_sheafFiber_eq_zero ξ hgen
    intro Ω _ _ s hs
    have := hψ Ω s hs
    apply (cancel_epi ((pointSmallEtale s).sheafFiber.map ψ)).mp
    rw [← Functor.map_comp, ← Category.assoc, Limits.cokernel.condition,
      Functor.map_zero, Limits.comp_zero]
  let r := Abelian.monoLift (ψ ≫ φ') φ' hzero
  have hr : r ≫ ψ = 𝟙 _ := by
    apply (cancel_mono φ').mp
    rw [Category.id_comp, Category.assoc]
    exact Abelian.monoLift_comp (ψ ≫ φ') φ' hzero
  have hψr : ψ ≫ r = 𝟙 _ := by
    apply (cancel_mono ψ).mp
    simp [Category.assoc, hr]
  let e : H ≅ (Etale.upperStar (ModuleCat.{u + 1} Λ) (f ≫ U.ι)).obj F :=
    ⟨ψ, r, hψr, hr⟩
  have : IsLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (f ≫ U.ι)).obj F) :=
    IsLocallyConstantSheaf.of_iso e
  let FU := (Etale.upperStar (ModuleCat.{u + 1} Λ) U.ι).obj F
  have : IsLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj FU) :=
    IsLocallyConstantSheaf.of_iso ((Etale.upperStarComp _ f U.ι).app F)
  let cover : Cover.{u} etalePrecoverage U.toScheme :=
    .singleton f ((singleton_mem_precoverage_iff _ f).mpr ⟨f.surjective, hf⟩)
  have : ∀ i, IsLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (cover.f i)).obj FU) := fun _ ↦
    inferInstanceAs (IsLocallyConstantSheaf ((Etale.upperStar _ f).obj FU))
  exact ⟨U, hU, IsLocallyConstantSheaf.of_cover cover FU⟩

end AlgebraicGeometry.Scheme
