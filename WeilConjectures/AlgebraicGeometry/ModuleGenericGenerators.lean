/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.EtaleGenericIrreducibleNeighbourhood
import WeilConjectures.AlgebraicGeometry.NoetherianConstantSubsheafGeneric

/-! # Generic generators inside a module subsheaf -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Lift the generic generators of a module subsheaf to a finite locally constant subsheaf
near a generic point (Stacks, Tag 09BH). -/
theorem exists_generic_generating_locallyConstant_subsheaf
    {X : Scheme.{u}} [IsNoetherian X] {Λ : Type (u + 1)} [CommRing Λ]
    [IsNoetherianRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) [Mono φ] [IsFiniteLocallyConstantSheaf G]
    (η : X) (hη : η ∈ genericPoints X) :
    ∃ (U : X.Opens) (_hU : η ∈ U) (Y : Scheme.{u}) (f : Y ⟶ U.toScheme),
      Etale f ∧ Surjective f ∧ IrreducibleSpace Y ∧
      ∃ (ξ : Y), IsGenericPoint ξ Set.univ ∧ U.ι (f ξ) = η ∧
      ∃ (H : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
        (ψ : H ⟶ (Etale.upperStar (ModuleCat.{u + 1} Λ) (f ≫ U.ι)).obj F),
        Mono ψ ∧ IsFiniteLocallyConstantSheaf H ∧
        ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
          s (IsLocalRing.closedPoint Ω) = ξ →
          Epi ((pointSmallEtale s).sheafFiber.map ψ) := by
  classical
  let : JointlySurjective etalePrecoverage :=
    inferInstanceAs (JointlySurjective (precoverage @Etale))
  obtain ⟨⟨𝒰, hc⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := G)
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq η
  have hfi : Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨W, hyW, hW, hygen⟩ :=
    Etale.exists_isGenericPoint_open_of_isGenericPoint (𝒰.f i) η hη y hy
  let := hW
  let g : W.toScheme ⟶ X := W.ι ≫ 𝒰.f i
  have hg : Etale g := by dsimp [g]; infer_instance
  have hconst : ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj G).IsConstant
      (𝒰.X i).smallEtaleTopology :=
    (isConstant_over_iff_upperStar _ (𝒰.etalePrecoverageToEtale i) G).mp (hc i)
  let := hconst
  have hconst' := Sheaf.IsConstant.upperStar (ModuleCat.{u + 1} Λ) W.ι
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj G)
  let := hconst'
  have hG : ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj G).IsConstant
      W.toScheme.smallEtaleTopology :=
    Sheaf.isConstant_congr _
      (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) W.ι).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj G))
      ((Etale.upperStarComp _ W.ι (𝒰.f i)).app G).symm
  let := IsFiniteSheaf.upperStar g G
  obtain ⟨V, hyV, H, ψ, hψ, hH, hgen⟩ :=
    exists_open_generic_generating_subsheaf_of_mono_constant
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).map φ) hG ⟨y, hyW⟩ hygen
  let ξ : V.toScheme := ⟨⟨y, hyW⟩, hyV⟩
  let : Nonempty V.toScheme := ⟨ξ⟩
  let : IrreducibleSpace V.toScheme := V.ι.isOpenEmbedding.irreducibleSpace
  have hξ : IsGenericPoint ξ Set.univ := by
    rw [isGenericPoint_iff_specializes]
    intro z
    simp only [Set.mem_univ, iff_true]
    exact (subtype_specializes_iff _ _).mpr (hygen.specializes (Set.mem_univ z.val))
  let e : V.toScheme ⟶ X := V.ι ≫ g
  have he : Etale e := by dsimp [e]; infer_instance
  have heξ : e ξ = η := by simpa [e, g, ξ] using hy
  let U : X.Opens := ⟨Set.range e, e.isOpenMap.isOpen_range⟩
  have hηU : η ∈ U := ⟨ξ, heξ⟩
  have hrange : Set.range e ⊆ Set.range U.ι := by
    rw [Opens.range_ι]
    exact Set.Subset.rfl
  let f : V.toScheme ⟶ U.toScheme := IsOpenImmersion.lift U.ι e hrange
  have hfac : f ≫ U.ι = e := IsOpenImmersion.lift_fac _ _ _
  have hf : Etale f := by
    have : Etale (f ≫ U.ι) := hfac.symm ▸ he
    exact Etale.of_comp f U.ι
  have hsurj : Surjective f := by
    constructor
    intro z
    obtain ⟨w, hw⟩ := z.property
    refine ⟨w, ?_⟩
    apply U.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hfac]
    exact hw
  let := hψ
  let κ : (Etale.upperStar (ModuleCat.{u + 1} Λ) V.ι).obj
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj F) ≅
      (Etale.upperStar (ModuleCat.{u + 1} Λ) (f ≫ U.ι)).obj F :=
    ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) V.ι g).app F).symm ≪≫
      eqToIso (congrArg (fun q ↦ (Etale.upperStar (ModuleCat.{u + 1} Λ) q).obj F) hfac.symm)
  refine ⟨U, hηU, V.toScheme, f, hf, hsurj, inferInstance, ξ, hξ, ?_,
    H, ψ ≫ κ.hom, inferInstance, hH, ?_⟩
  · rw [← Scheme.Hom.comp_apply, hfac]
    exact heξ
  · intro Ω _ _ s hs
    rw [(pointSmallEtale s).sheafFiber.map_comp ψ κ.hom]
    exact (epi_comp_iff_of_isIso _ _).mpr (hgen Ω s hs)

end AlgebraicGeometry.Scheme
