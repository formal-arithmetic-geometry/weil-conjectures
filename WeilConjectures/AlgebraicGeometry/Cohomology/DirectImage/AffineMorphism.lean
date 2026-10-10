/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

/-!
# Higher direct images along affine morphisms

The higher direct images along an affine morphism vanish, and the cohomology of a coherent
sheaf on a proper scheme over a field is finite dimensional.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}
variable (f : X ⟶ T) (ℱ : X.Modules)

section AffineMorphism

/-- **The higher direct images along an affine morphism vanish.** Let `f : X ⟶ T` be affine
and `ℱ` a quasi-coherent `𝒪_X`-module. Then `R^q f_* ℱ = 0` for `q > 0`: the higher direct
images commute with restriction to an affine open `V` of `T`, over which their sections are
`H^q(f⁻¹ V, ℱ)`, and these vanish since `f⁻¹ V` is affine
(`AlgebraicGeometry.Scheme.Modules.subsingleton_H_succ_of_isAffine`).

(blueprint: `lem-pc-affine-morphism-hi`) -/
theorem isZero_higherDirectImage_of_isAffineHom (f : X ⟶ T) [IsAffineHom f]
    [HasInjectiveResolutions X.Modules] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] {q : ℕ} (hq : 0 < q) :
    IsZero ((higherDirectImage f q).obj ℱ) := by
  obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  refine isZero_of_forall_affineOpens _ fun V ↦ ?_
  have := isGrothendieckAbelian (f ⁻¹ᵁ V.1).toScheme
  have : IsAffine V.1.toScheme := V.2
  have : IsAffine (f ⁻¹ᵁ V.1).toScheme := V.2.preimage f
  obtain ⟨e⟩ := nonempty_higherDirectImage_iso_restrict f ℱ V.1.ι (f ⁻¹ᵁ V.1).ι (f ∣_ V.1)
    (isPullback_morphismRestrict f V.1).flip (q + 1)
  obtain ⟨e'⟩ := nonempty_sections_higherDirectImage_iso_H (f ∣_ V.1)
    ((Modules.pullback (f ⁻¹ᵁ V.1).ι).obj ℱ) (q + 1)
  have := subsingleton_H_succ_of_isAffine ((Modules.pullback (f ⁻¹ᵁ V.1).ι).obj ℱ) q
  have : Subsingleton Γ((higherDirectImage (f ∣_ V.1) (q + 1)).obj
      ((Modules.pullback (f ⁻¹ᵁ V.1).ι).obj ℱ), ⊤) := e'.toEquiv.subsingleton
  have : Subsingleton Γ(((higherDirectImage f (q + 1)).obj ℱ).restrict V.1.ι, ⊤) :=
    (asIso (e.hom.app ⊤)).addCommGroupIsoToAddEquiv.toEquiv.symm.subsingleton
  have : Subsingleton Γ((higherDirectImage f (q + 1)).obj ℱ, V.1.ι ''ᵁ ⊤) :=
    (((higherDirectImage f (q + 1)).obj ℱ).restrictAppIso V.1.ι ⊤).addCommGroupIsoToAddEquiv
      |>.toEquiv.symm.subsingleton
  rwa [Scheme.Opens.ι_image_top] at this

/-- **The pushforward along an affine morphism is quasi-coherent.** For `f : X ⟶ T` affine and
`ℱ` quasi-coherent, `f_* ℱ = R⁰ f_* ℱ` is quasi-coherent
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_higherDirectImage`).

(blueprint: `lem-pc-affine-morphism-hi`) -/
theorem isQuasicoherent_pushforward_of_isAffineHom (f : X ⟶ T) [IsAffineHom f] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] :
    ((pushforward f).obj ℱ).IsQuasicoherent := by
  have := isGrothendieckAbelian X
  have : PreservesFiniteLimits (pushforward f) :=
    have := (pullbackPushforwardAdjunction f).rightAdjoint_preservesLimits.{0, 0}
    inferInstance
  exact (SheafOfModules.isQuasicoherent T.ringCatSheaf).prop_of_iso
    ((Functor.rightDerivedZeroIsoSelf (pushforward f)).app ℱ)
    (isQuasicoherent_higherDirectImage f ℱ 0)

end AffineMorphism

section Finiteness

variable {k : Type u} [Field k] [X.Over (Spec (.of k))]

/-- **Finiteness of coherent cohomology.** On a scheme `X` proper over a field `k`, the
cohomology groups `H^q(X, ℱ)` of a coherent `𝒪_X`-module `ℱ` are finite-dimensional over `k`.
Coherence is spelled as quasi-coherence together with finite presentation.

This is the case `T = Spec k` of the finiteness of the higher direct images along a proper
morphism to a Noetherian affine scheme
(`AlgebraicGeometry.Scheme.Modules.finite_sections_higherDirectImage`), transported along the
identification `Γ(Spec k, R^q f_* ℱ) ≅ H^q(X, ℱ)`
(`AlgebraicGeometry.Scheme.Modules.exists_bijective_semilinearMap_sections_higherDirectImage_H`).
-/
@[stacks 02O5]
theorem finiteDimensional_H_of_isProper [IsProper (X ↘ Spec (.of k))] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    FiniteDimensional k (ℱ.H q) := by
  classical
  have := isGrothendieckAbelian X
  have : IsNoetherianRing Γ(Spec (.of k), ⊤) :=
    isNoetherianRing_of_ringEquiv _ (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm
  obtain ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H
    (X ↘ Spec (.of k)) ℱ q
  obtain ⟨s, hs⟩ := (finite_sections_higherDirectImage (X ↘ Spec (.of k)) ℱ q).fg_top
  have key (x) (hx : x ∈ Submodule.span Γ(Spec (.of k), ⊤) (s : Set _)) :
      e x ∈ Submodule.span k (e '' s) := by
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | smul a x _ hx =>
      obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2 a
      have hc : c • e x = e ((Scheme.ΓSpecIso (.of k)).inv c • x) := by
        rw [smul_H_eq_globalSectionsRingHom_smul, e.map_smulₛₗ]
        rfl
      rw [← hc]
      exact Submodule.smul_mem _ c hx
  refine ⟨⟨s.image e, eq_top_iff.2 fun y _ ↦ ?_⟩⟩
  obtain ⟨x, rfl⟩ := he.2 y
  rw [Finset.coe_image]
  exact key x (hs ▸ Submodule.mem_top)

end Finiteness

end AlgebraicGeometry.Scheme.Modules
