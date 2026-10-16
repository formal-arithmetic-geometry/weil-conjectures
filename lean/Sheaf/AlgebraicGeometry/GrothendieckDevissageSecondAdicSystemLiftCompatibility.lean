/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import all Sheaf.AlgebraicGeometry.GrothendieckExistenceSupportedHom
import all Sheaf.AlgebraicGeometry.IdealPowerProductRestrictionZero

/-! # Lifting the comparison map of the second adic system

Source: Stacks Project, Tag 088A, construction of the maps G_e → H/K^e H.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- Full faithfulness of supported completion, transported through closed pushforward. -/
private theorem supported_completion_bijective
    {X Z : Scheme.{u}} [IsNoetherian X] (j : Z ⟶ X) [IsClosedImmersion j]
    (I : X.IdealSheafData)
    (he : (@completion Z (isNoetherian_of_locallyOfFiniteType j) (I.comap j)).IsEquivalence)
    (F G : CoherentModules X)
    (hF : CoherentModuleSupportedOn F j) (hG : CoherentModuleSupportedOn G j) :
    Function.Bijective (formalCompletionMap I : (F.obj ⟶ G.obj) → _) := by
  classical
  let : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType j
  obtain ⟨E, ⟨β⟩⟩ := closedImmersion_coherent_equivalence j
  let Fs := (⟨F, hF⟩ : ObjectProperty.FullSubcategory
    (fun L : CoherentModules X ↦ CoherentModuleSupportedOn L j))
  let Gs := (⟨G, hG⟩ : ObjectProperty.FullSubcategory
    (fun L : CoherentModules X ↦ CoherentModuleSupportedOn L j))
  let FZ := E.inverse.obj Fs
  let GZ := E.inverse.obj Gs
  let A := ObjectProperty.ι (fun L : CoherentModules X ↦ CoherentModuleSupportedOn L j) ⋙
    ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace)
  let a : F.obj ≅ (Scheme.Modules.pushforward j).obj FZ.obj :=
    (A.mapIso (E.counitIso.app Fs)).symm ≪≫ β.app FZ
  let b : G.obj ≅ (Scheme.Modules.pushforward j).obj GZ.obj :=
    (A.mapIso (E.counitIso.app Gs)).symm ≪≫ β.app GZ
  let P := Scheme.Modules.pushforward j
  obtain ⟨hP⟩ := (Functor.FullyFaithful.nonempty_iff_map_bijective P).mpr
    ((closedImmersion_pushforward_fullyFaithful j).2)
  let C := completion Z (I.comap j)
  let := he
  let U := ObjectProperty.ι (RingedSpace.IsCoherent Z.toRingedSpace)
  have hC : C.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful C
  have hCV := hC.comp (ObjectProperty.fullyFaithfulι (IsCoherentFormalModule (I.comap j)))
  obtain ⟨θ, _⟩ := (closedImmersion_coherentFormal_equivalence j I).2
  have hH : (U ⋙ P ⋙ formalCompletionFunctor I).FullyFaithful :=
    (hCV.comp (hP.whiskeringRight ℕᵒᵖ)).ofIso θ.symm
  have hcomposite := hH.map_bijective FZ GZ
  have hPcoh := ((ObjectProperty.fullyFaithfulι
    (RingedSpace.IsCoherent Z.toRingedSpace)).comp hP).map_bijective FZ GZ
  have hquot : Function.Bijective
      ((formalCompletionFunctor I).map : (P.obj FZ.obj ⟶ P.obj GZ.obj) → _) := by
    constructor
    · intro v w h
      obtain ⟨v', rfl⟩ := hPcoh.surjective v
      obtain ⟨w', rfl⟩ := hPcoh.surjective w
      exact congrArg (U ⋙ P).map (hcomposite.injective h)
    · intro v
      obtain ⟨w, hw⟩ := hcomposite.surjective v
      exact ⟨(U ⋙ P).map w, hw⟩
  exact map_bijective_of_isos (formalCompletionFunctor I) a b hquot

/-- Raising an annihilating power preserves annihilation. -/
private theorem annihilated_higher_power
    {X : Scheme.{u}} (K : X.IdealSheafData) (F : X.Modules)
    {a b : ℕ} (h : a ≤ b)
    (hz : IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι a).2 F)) :
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι b).2 F) := by
  obtain ⟨k, hk⟩ := formalModuleQuotient_factor K (𝟙 F) h
  have hi := hz.eq_zero_of_src
    (Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι a).2 F)
  have : Mono (Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι b).2 F) := by
    dsimp [Scheme.idealModuleProductι]
    infer_instance
  apply IsZero.of_mono_eq_zero
    (Scheme.idealModuleProductι (Scheme.idealSheafPower K.toModulesι b).2 F)
  simpa [hi] using hk

/-- Supported completion gives a Hom bijection for any two bounded K-torsion modules. -/
private theorem torsion_completion_bijective
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (F G : CoherentModules X) (a b : ℕ)
    (hF : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower K.toModulesι (a + 1)).2 F.obj))
    (hG : IsZero (Scheme.idealModuleProduct
      (Scheme.idealSheafPower K.toModulesι (b + 1)).2 G.obj)) :
    Function.Bijective (formalCompletionMap I : (F.obj ⟶ G.obj) → _) := by
  sorry

/-- Construct a comparison map for an already algebraized second-ideal system.
Source: Stacks Project, Tag 088A (lemma-existence-tricky), construction of
G_e → H/K^e H, using the closed-immersion equivalence of Tag 087T.
https://stacks.math.columbia.edu/tag/088A
(blueprint: lem-weil-pbc-devissage-second-adic-system-lift-compatibility).

Proof: Coherent modules killed by powers of K descend to a common closed thickening.
Closed pushforward is fully faithful and commutes naturally with I-completion.
The assumed completion equivalence on that thickening therefore gives a bijection
on Hom sets for the ambient I-completion. Form the doubly natural morphism τ by
composing σ, the K-reduction of α, and θ inverse. The terms N_e and H/K^(e+1)H
are coherent and annihilated by K^(e+1), so surjectivity lifts τ_e uniquely to d_e.
For adjacent indices, the two composites of d with the transitions have equal
I-completions by naturality of τ. Both endpoints are killed by a common higher
power of K, so injectivity makes the composites equal. Assemble these adjacent
compatible maps as a natural transformation δ. Its component lifting equations,
composed with θ, give precisely the displayed squares. The maps are uniquely
specified by their completions; no arbitrary witness or square hypothesis is used. -/
theorem grothendieckDevissage_secondAdicSystem_lift_compatibility
    {X : Scheme.{u}} [IsNoetherian X] (I K : X.IdealSheafData)
    (M : CoherentFormalModule X I)
    (hthick : ∀ (e : ℕ), 1 ≤ e →
      ∀ (hZ : IsNoetherian (K ^ e).subscheme),
        Functor.IsEquivalence
          (@completion ((K ^ e).subscheme) hZ (I.comap (K ^ e).subschemeι)))
    (H : CoherentModules X) (α : M ⟶ (completion X I).obj H)
    (θ : formalCompletionSystem K H.obj ⋙ formalCompletionFunctor I ≅
      (formalCompletionSystem I H.obj ⋙ formalCompletionFunctor K).flip)
    {N : CoherentFormalModule X K}
    (σ : N.obj ⋙ formalCompletionFunctor I ≅
      (M.obj ⋙ formalCompletionFunctor K).flip) :
    ∃ (δ : N ⟶ (completion X K).obj H), ∀ e n : ℕ,
      (σ.hom.app (op e)).app (op n) ≫
          formalModuleQuotientMap K (α.hom.app (op n)) (Nat.le_refl (e + 1)) =
        formalModuleQuotientMap I (δ.hom.app (op e)) (Nat.le_refl (n + 1)) ≫
          (θ.hom.app (op e)).app (op n) := by
  sorry

end AlgebraicGeometry
