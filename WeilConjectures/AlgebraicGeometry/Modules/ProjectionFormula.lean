/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.PicardFunctor

/-!
# Pullback, tensor products and the projection formula

We record how the pullback of `𝒪`-modules along a morphism of schemes `g : X ⟶ Y` interacts with
the tensor product, and the projection formula `g_* (g^* N) ≅ g_* 𝒪_X ⊗ N` for an invertible
`𝒪_Y`-module `N`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.nonempty_pullback_tensorObj_iso`: the pullback of a tensor
  product is the tensor product of the pullbacks.
- `AlgebraicGeometry.Scheme.Modules.nonempty_pullback_tensorPow_iso`: the pullback of a tensor
  power is the tensor power of the pullback.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible.tensorObj`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible.tensorPow`: tensor products and tensor powers of
  invertible modules are invertible.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible.isQuasicoherent`: an invertible module is
  quasi-coherent.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible.of_sheafOfModules`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible.sheafOfModules_isInvertible`: the two notions of
  invertibility, `AlgebraicGeometry.Scheme.Modules.IsInvertible` and
  `SheafOfModules.IsInvertible`, agree.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj`,
  `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_tensorObj`: twisting by an invertible
  module preserves quasi-coherence and finite presentation.
- `AlgebraicGeometry.Scheme.Modules.nonempty_pushforward_tensorObj_pullback_iso`: the projection
  formula `g_* M ⊗ N ≅ g_* (M ⊗ g^* N)` for an invertible module `N`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_pushforward_pullback_iso`: its case `M = 𝒪_X`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_pushforward_pullback_iso_self`: if `g_* 𝒪_X ≅ 𝒪_Y`,
  then `g_* (g^* N) ≅ N` for every invertible `𝒪_Y`-module `N`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

section Tensor

/-- **The pullback of a tensor product is the tensor product of the pullbacks.** For
`g : X ⟶ Y` and `𝒪_Y`-modules `M` and `N`, `g^* (M ⊗ N) ≅ g^* M ⊗ g^* N`: the pullback is the
sheafification of the presheaf pullback, which is a base change of modules and so commutes with
tensor products. -/
theorem nonempty_pullback_tensorObj_iso (g : X ⟶ Y) (M N : Y.Modules) :
    Nonempty ((pullback g).obj (M ⊗ N) ≅ (pullback g).obj M ⊗ (pullback g).obj N) :=
  sorry

/-- **The pullback of a tensor power is the tensor power of the pullback.**
`g^* (M^{⊗ m}) ≅ (g^* M)^{⊗ m}`. -/
theorem nonempty_pullback_tensorPow_iso (g : X ⟶ Y) (M : Y.Modules) (m : ℕ) :
    Nonempty ((pullback g).obj (M.tensorPow m) ≅ ((pullback g).obj M).tensorPow m) := by
  induction m with
  | zero => exact ⟨pullbackObjUnitIso g⟩
  | succ m ih =>
    obtain ⟨e⟩ := nonempty_pullback_tensorObj_iso g M (M.tensorPow m)
    exact ⟨e ≪≫ (Iso.refl _ ⊗ᵢ ih.some)⟩

/-- **A tensor product of invertible modules is invertible.** If `M` and `N` are trivial near a
point `x`, so is `M ⊗ N`, since restriction to an open commutes with tensor products. -/
instance IsInvertible.tensorObj (M N : X.Modules) [M.IsInvertible] [N.IsInvertible] :
    (M ⊗ N).IsInvertible where
  exists_isoUnit x := by
    obtain ⟨U, hU, ⟨e⟩⟩ := IsInvertible.exists_isoUnit (M := M) x
    obtain ⟨V, hV, ⟨e'⟩⟩ := IsInvertible.exists_isoUnit (M := N) x
    refine ⟨U ⊓ V, ⟨hU, hV⟩, ?_⟩
    have hW (P : X.Modules) {W : X.Opens} (hW : U ⊓ V ≤ W)
        (eP : (Modules.pullback W.ι).obj P ≅ SheafOfModules.unit _) :
        Nonempty ((Modules.pullback (U ⊓ V).ι).obj P ≅ SheafOfModules.unit _) :=
      ⟨(pullbackCongr (X.homOfLE_ι hW).symm).app P ≪≫ (pullbackComp _ _).symm.app P ≪≫
        (Modules.pullback (X.homOfLE hW)).mapIso eP ≪≫ pullbackObjUnitIso _⟩
    obtain ⟨eM⟩ := hW M inf_le_left e
    obtain ⟨eN⟩ := hW N inf_le_right e'
    obtain ⟨t⟩ := nonempty_pullback_tensorObj_iso (U ⊓ V).ι M N
    exact ⟨t ≪≫ (eM ⊗ᵢ eN) ≪≫ λ_ _⟩

/-- **A tensor power of an invertible module is invertible.** -/
instance IsInvertible.tensorPow (M : X.Modules) [M.IsInvertible] (m : ℕ) :
    (M.tensorPow m).IsInvertible := by
  induction m with
  | zero => exact isInvertible_tensorUnit
  | succ m ih => exact IsInvertible.tensorObj M (M.tensorPow m)

end Tensor

section Comparison

/-- A sheaf of modules which is invertible in the sense of `SheafOfModules.IsInvertible` (locally
free of rank one) is invertible in the sense of `AlgebraicGeometry.Scheme.Modules.IsInvertible`
(locally isomorphic to `𝒪_X`). -/
lemma IsInvertible.of_sheafOfModules (M : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} M] :
    M.IsInvertible where
  exists_isoUnit x := by
    obtain ⟨U, hx, ⟨e⟩⟩ := exists_mem_over_iso_unit M x
    exact ⟨U, hx, ⟨pullbackIotaUnitIsoOfOverIso e⟩⟩

/-- Conversely, an invertible module in the sense of
`AlgebraicGeometry.Scheme.Modules.IsInvertible` is invertible in the sense of
`SheafOfModules.IsInvertible`. -/
lemma IsInvertible.sheafOfModules_isInvertible (M : X.Modules) [M.IsInvertible] :
    SheafOfModules.IsInvertible.{u, u, u} M := by
  choose U hU e using fun x : X ↦ IsInvertible.exists_isoUnit (M := M) x
  refine SheafOfModules.isInvertible_of_forall_over_unit (M := M) U ?_ ?_
  · rw [Opens.coversTop_iff]
    exact IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hU x⟩)
  · exact fun x ↦ ⟨overIsoUnitOfPullbackIotaIso (e x).some⟩

end Comparison

section Quasicoherent

/-- **An invertible module is quasi-coherent**, being locally isomorphic to the structure
sheaf. -/
instance IsInvertible.isQuasicoherent (M : X.Modules) [M.IsInvertible] : M.IsQuasicoherent := by
  choose U hU e using fun x : X ↦ IsInvertible.exists_isoUnit (M := M) x
  have (x : X) : (M.over (U x)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over (U x))).prop_of_iso
      (overIsoUnitOfPullbackIotaIso (e x).some).symm
      (SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf.over (U x)))
  refine SheafOfModules.IsQuasicoherent.of_coversTop M U ?_
  rw [Opens.coversTop_iff]
  exact IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hU x⟩)

/-- If an invertible module `N` is trivial on an open `U`, then `(M ⊗ N)|_U ≅ M|_U`. -/
lemma nonempty_over_tensorObj_iso (M N : X.Modules) {U : X.Opens}
    (e : (pullback U.ι).obj N ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    Nonempty ((M ⊗ N).over U ≅ M.over U) := by
  obtain ⟨t⟩ := nonempty_pullback_tensorObj_iso U.ι M N
  exact ⟨(overEquiv U).functor.preimageIso (overEquivObjOverIso (M ⊗ N) U ≪≫ t ≪≫
    (Iso.refl _ ⊗ᵢ e) ≪≫ ρ_ _ ≪≫ (overEquivObjOverIso M U).symm)⟩

/-- **Twisting by an invertible module preserves quasi-coherence.** Locally `N ≅ 𝒪_X`, so
`M ⊗ N` is locally isomorphic to `M`, and quasi-coherence is a local property. -/
theorem isQuasicoherent_tensorObj (M N : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] [N.IsInvertible] :
    (M ⊗ N).IsQuasicoherent := by
  choose U hU e using fun x : X ↦ IsInvertible.exists_isoUnit (M := N) x
  have (x : X) : ((M ⊗ N).over (U x)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over (U x))).prop_of_iso
      (nonempty_over_tensorObj_iso M N (e x).some).some.symm
      (SheafOfModules.isQuasicoherent_over M (U x))
  refine SheafOfModules.IsQuasicoherent.of_coversTop (tensorObj M N) U ?_
  rw [Opens.coversTop_iff]
  exact IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hU x⟩)

/-- **Twisting by an invertible module preserves finite presentation.** Locally `N ≅ 𝒪_X`, so
`M ⊗ N` is locally isomorphic to `M`, and finite presentation is a local property. -/
theorem isFinitePresentation_tensorObj (M N : X.Modules)
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) M] [N.IsInvertible] :
    (M ⊗ N).IsFinitePresentation := by
  choose U hU e using fun x : X ↦ IsInvertible.exists_isoUnit (M := N) x
  have (x : X) : SheafOfModules.IsFinitePresentation.{u} (M.over (U x)) :=
    SheafOfModules.isFinitePresentation_pushforward_of_isLeftAdjoint (Over.forget (U x)) (𝟙 _)
      (Iso.refl _)
  have (x : X) : ((M ⊗ N).over (U x)).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (X.ringCatSheaf.over (U x))).prop_of_iso
      (nonempty_over_tensorObj_iso M N (e x).some).some.symm (this x)
  refine SheafOfModules.IsFinitePresentation.of_coversTop (tensorObj M N) U ?_
  rw [Opens.coversTop_iff]
  exact IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hU x⟩)

end Quasicoherent

section ProjectionFormula

/-- **The projection formula** for an invertible module. For `g : X ⟶ Y`, an `𝒪_X`-module `M`
and an invertible `𝒪_Y`-module `N`, `g_* M ⊗ N ≅ g_* (M ⊗ g^* N)`. The natural map is the
adjoint of `g^* (g_* M ⊗ N) ≅ g^* g_* M ⊗ g^* N ⟶ M ⊗ g^* N`; on an open `V` of `Y` on which
`N ≅ 𝒪_Y`, both sides are `g_* M` and the map is the identity, so it is an isomorphism.

For a closed immersion `g` of locally noetherian schemes this is the last assertion of the
blueprint lemma, used to identify `i_* (ℱ ⊗ 𝒪_X(m))` with `(i_* ℱ)(m)`.

(blueprint: `lem-pc-closed-immersion-coherent-cohomology`) -/
theorem nonempty_pushforward_tensorObj_pullback_iso (g : X ⟶ Y) (M : X.Modules) (N : Y.Modules)
    [N.IsInvertible] :
    Nonempty ((pushforward g).obj M ⊗ N ≅ (pushforward g).obj (M ⊗ (pullback g).obj N)) :=
  sorry

/-- **The projection formula** for the structure sheaf. For `g : X ⟶ Y` and an invertible
`𝒪_Y`-module `N`, `g_* (g^* N) ≅ g_* 𝒪_X ⊗ N`: this is
`AlgebraicGeometry.Scheme.Modules.nonempty_pushforward_tensorObj_pullback_iso` for `M = 𝒪_X`. -/
theorem nonempty_pushforward_pullback_iso (g : X ⟶ Y) (N : Y.Modules) [N.IsInvertible] :
    Nonempty ((pushforward g).obj ((pullback g).obj N) ≅
      (pushforward g).obj (𝟙_ X.Modules) ⊗ N) := by
  obtain ⟨e⟩ := nonempty_pushforward_tensorObj_pullback_iso g (𝟙_ X.Modules) N
  exact ⟨(pushforward g).mapIso (λ_ _).symm ≪≫ e.symm⟩

/-- If `g_* 𝒪_X ≅ 𝒪_Y`, then `g_* (g^* N) ≅ N` for every invertible `𝒪_Y`-module `N`: by the
projection formula `g_* (g^* N) ≅ g_* 𝒪_X ⊗ N ≅ 𝒪_Y ⊗ N ≅ N`. -/
theorem nonempty_pushforward_pullback_iso_self (g : X ⟶ Y)
    (e : (pushforward g).obj (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules) (N : Y.Modules) [N.IsInvertible] :
    Nonempty ((pushforward g).obj ((pullback g).obj N) ≅ N) := by
  obtain ⟨e'⟩ := nonempty_pushforward_pullback_iso g N
  exact ⟨e' ≪≫ (e ⊗ᵢ Iso.refl N) ≪≫ λ_ N⟩

end ProjectionFormula

end AlgebraicGeometry.Scheme.Modules
