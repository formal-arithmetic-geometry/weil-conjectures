/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Modules.HomOfBasis
public import WeilConjectures.AlgebraicGeometry.Modules.Rigidification
public import WeilConjectures.AlgebraicGeometry.Seesaw

/-!
# Direct images of invertible modules trivial over an open cover of the base

Let `f : P ⟶ T` be a morphism of schemes such that `f^♯ : Γ(T, V) → Γ(P, f⁻¹ V)` is bijective
for every open `V ⊆ T`, i.e. `𝒪_T ≅ f_* 𝒪_P`. If an `𝒪_P`-module `L` is trivial on `f⁻¹ Uᵢ` for
an open cover `(Uᵢ)` of `T`, then `f_* L` is invertible and the counit `f^* f_* L ⟶ L` is an
isomorphism. This applies to the projection `P ×_K T ⟶ T` for `P` proper and geometrically
integral over a field `K`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isIso_of_forall_exists_isFreeGenerator`: a morphism of
  modules sending local free generators to free generators is an isomorphism.
- `AlgebraicGeometry.Scheme.Modules.isInvertible_pushforward_and_isIso_counit`: the statement
  for a morphism `f` with `𝒪_T ≅ f_* 𝒪_P`.
- `AlgebraicGeometry.isInvertible_pushforward_snd_and_isIso_counit`: the statement for the
  projection `P ×_K T ⟶ T`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- If `f^♯ : Γ(T, A) → Γ(P, f⁻¹ A)` is an isomorphism for all affine opens `A ⊆ T`, then
`f^♯ : Γ(T, V) → Γ(P, f⁻¹ V)` is bijective for all opens `V ⊆ T`. -/
lemma Scheme.Hom.bijective_app_of_isIso_app_of_isAffineOpen {P T : Scheme.{u}} (f : P ⟶ T)
    (h : ∀ A : T.Opens, IsAffineOpen A → IsIso (f.app A)) (V : T.Opens) :
    Function.Bijective (f.app V) := by
  let φ : T.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj P.sheaf := ⟨f.c⟩
  have : IsIso φ := by
    apply TopCat.Sheaf.isIso_iff_isIso_basis (B := fun A : T.affineOpens ↦ A.1)
    · simpa only [Subtype.range_coe] using T.isBasis_affineOpens
    intro A
    exact h A.1 A.2
  have : IsIso f.c := (TopCat.Sheaf.forget _ _).map_isIso φ
  exact ConcreteCategory.bijective_of_isIso (f.app V)

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- A morphism `φ : M ⟶ N` of `𝒪_X`-modules is an isomorphism if every point has an open
neighbourhood `W` and a free generator `a` of `M` over `W` such that `φ a` is a free generator
of `N` over `W`. -/
lemma isIso_of_forall_exists_isFreeGenerator {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ (W : X.Opens) (a : Γ(M, W)), x ∈ W ∧ IsFreeGenerator a ∧
      IsFreeGenerator (φ.app W a)) : IsIso φ := by
  let S := {V : X.Opens // ∃ (W : X.Opens) (a : Γ(M, W)) (_ : V ≤ W), IsFreeGenerator a ∧
    IsFreeGenerator (φ.app W a)}
  refine isIso_of_bijective_app_of_basis (O := fun V : S ↦ V.1) ?_ φ ?_
  · refine TopologicalSpace.Opens.isBasis_iff_nbhd.2 fun {U x} hx ↦ ?_
    obtain ⟨W, a, hxW, ha, hφa⟩ := h x
    exact ⟨U ⊓ W, ⟨⟨U ⊓ W, W, a, inf_le_right, ha, hφa⟩, rfl⟩, ⟨hx, hxW⟩, inf_le_left⟩
  · rintro ⟨V, W, a, hVW, ha, hφa⟩
    have hcomp : (fun r : Γ(X, V) ↦ r • N.presheaf.map (homOfLE hVW).op (φ.app W a)) =
        φ.app V ∘ fun r : Γ(X, V) ↦ r • M.presheaf.map (homOfLE hVW).op a := by
      funext r
      simp [Hom.app_smul, Hom.app_presheaf_map]
    exact (Function.Bijective.of_comp_iff _ (ha V hVW)).1 (hcomp ▸ hφa V hVW)

variable {P T : Scheme.{u}} (f : P ⟶ T)

/-- If `f^♯ : Γ(T, V) → Γ(P, f⁻¹ V)` is bijective for all opens `V`, a free generator of an
`𝒪_P`-module `M` over `f⁻¹ U` is a free generator of `f_* M` over `U`. -/
lemma isFreeGenerator_pushforward (hf : ∀ V : T.Opens, Function.Bijective (f.app V))
    {M : P.Modules} {U : T.Opens} {m : Γ(M, f ⁻¹ᵁ U)} (hm : IsFreeGenerator m) :
    IsFreeGenerator (M := (pushforward f).obj M) (U := U) m := by
  intro V hV
  exact (hm _ (f.preimage_mono hV)).comp (hf V)

/-- The counit `f^* f_* L ⟶ L` sends the pullback of a section `m` of `f_* L` over `U` to `m`. -/
lemma counit_app_pullbackSection (L : P.Modules) {U : T.Opens}
    (m : Γ((pushforward f).obj L, U)) :
    ((pullbackPushforwardAdjunction f).counit.app L).app (f ⁻¹ᵁ U) (pullbackSection f m) = m := by
  have h := (pullbackPushforwardAdjunction f).right_triangle_components L
  exact congrArg (fun ψ ↦ (Hom.app ψ U) m) h

/-- Let `f : P ⟶ T` be such that `f^♯ : Γ(T, V) → Γ(P, f⁻¹ V)` is bijective for all opens `V`,
and let `L` be an `𝒪_P`-module which is trivial on `f⁻¹ Uᵢ` for an open cover `(Uᵢ)` of `T`.
Then `f_* L` is invertible and the counit `f^* f_* L ⟶ L` is an isomorphism. -/
theorem isInvertible_pushforward_and_isIso_counit
    (hf : ∀ V : T.Opens, Function.Bijective (f.app V)) (L : P.Modules) {ι : Type*}
    (U : ι → T.Opens) (hU : ⨆ i, U i = ⊤)
    (hL : ∀ i, Nonempty ((pullback (f ⁻¹ᵁ U i).ι).obj L ≅ SheafOfModules.unit _)) :
    ((pushforward f).obj L).IsInvertible ∧
      IsIso ((pullbackPushforwardAdjunction f).counit.app L) := by
  have hmem (t : T) : ∃ i, t ∈ U i :=
    TopologicalSpace.Opens.mem_iSup.1 (hU.ge (Set.mem_univ t))
  have hgen (i : ι) : ∃ m : Γ(L, f ⁻¹ᵁ U i), IsFreeGenerator m :=
    exists_isFreeGenerator_of_pullback_ι_iso L _ (hL i).some
  choose m hm using hgen
  have hinv : ((pushforward f).obj L).IsInvertible := by
    refine ⟨fun t ↦ ?_⟩
    obtain ⟨i, hi⟩ := hmem t
    exact ⟨U i, hi, nonempty_pullback_ι_iso_unit_of_isFreeGenerator _
      (isFreeGenerator_pushforward f hf (hm i))⟩
  refine ⟨hinv, isIso_of_forall_exists_isFreeGenerator _ fun x ↦ ?_⟩
  obtain ⟨i, hi⟩ := hmem (f x)
  -- a free generator `e` of `f^* f_* L` near `x`, inside `f⁻¹ Uᵢ`
  obtain ⟨W', hxW', ⟨d⟩⟩ :=
    IsInvertible.exists_isoUnit (M := (pullback f).obj ((pushforward f).obj L)) x
  obtain ⟨e', he'⟩ := exists_isFreeGenerator_of_pullback_ι_iso _ _ d
  let W : P.Opens := W' ⊓ f ⁻¹ᵁ U i
  have hW' : W ≤ W' := inf_le_left
  have hWU : W ≤ f ⁻¹ᵁ U i := inf_le_right
  set ε := (pullbackPushforwardAdjunction f).counit.app L
  set e := ((pullback f).obj ((pushforward f).obj L)).presheaf.map (homOfLE hW').op e'
  have he : IsFreeGenerator e := he'.map hW'
  set mW := L.presheaf.map (homOfLE hWU).op (m i)
  have hmW : IsFreeGenerator mW := (hm i).map hWU
  -- the pullback of `m i` is `r • e`, and `ε e = s • mW` with `r * s = 1`
  let mi : Γ((pushforward f).obj L, U i) := m i
  obtain ⟨r, hr⟩ := he.exists_smul_eq (((pullback f).obj ((pushforward f).obj L)).presheaf.map
    (homOfLE hWU).op (pullbackSection f mi))
  obtain ⟨s, hs⟩ := hmW.exists_smul_eq (ε.app W e)
  have hεp : ε.app W (r • e) = mW := by
    rw [hr]
    exact (Hom.app_presheaf_map ε (homOfLE hWU) _).trans
      (congrArg (L.presheaf.map (homOfLE hWU).op) (counit_app_pullbackSection f L mi))
  have hrs : (r * s) • mW = (1 : Γ(P, W)) • mW := by
    rw [one_smul, mul_smul, hs, ← Hom.app_smul, hεp]
  have hunit : IsUnit s :=
    IsUnit.of_mul_eq_one r ((mul_comm s r).trans (hmW.smul_left_injective hrs))
  refine ⟨W, e, ⟨hxW', hi⟩, he, ?_⟩
  rw [← hs]
  exact hmW.units_smul hunit.unit

end Scheme.Modules

open Scheme.Modules

variable {K : Type u} [Field K]

/-- Let `P` be proper and geometrically integral over a field `K`, let `T` be a `K`-scheme and
let `f : P ×_K T ⟶ T` be the projection. If an `𝒪_{P ×_K T}`-module `L` is trivial on
`P ×_K Uᵢ` for an open cover `(Uᵢ)` of `T`, then `f_* L` is invertible and the evaluation map
`f^* f_* L ⟶ L` is an isomorphism. -/
theorem isInvertible_pushforward_snd_and_isIso_counit (P T : Over (Spec (.of K)))
    [IsProper P.hom] [GeometricallyIntegral P.hom] (L : (P ⊗ T).left.Modules) {ι : Type*}
    (U : ι → T.left.Opens) (hU : ⨆ i, U i = ⊤)
    (hL : ∀ i, Nonempty ((Scheme.Modules.pullback ((snd P T).left ⁻¹ᵁ U i).ι).obj L ≅
      SheafOfModules.unit _)) :
    ((pushforward (snd P T).left).obj L).IsInvertible ∧
      IsIso ((pullbackPushforwardAdjunction (snd P T).left).counit.app L) := by
  let : P.left.Over (Spec (.of K)) := ⟨P.hom⟩
  have : CompactSpace P.left := QuasiCompact.compactSpace_of_compactSpace P.hom
  have : QuasiSeparatedSpace P.left := quasiSeparatedSpace_of_quasiSeparated P.hom
  have : Scheme.GlobalSectionsBijective K P.left :=
    have : IsProper (P.left ↘ Spec (.of K)) := inferInstanceAs (IsProper P.hom)
    have : GeometricallyIntegral (P.left ↘ Spec (.of K)) :=
      inferInstanceAs (GeometricallyIntegral P.hom)
    .of_geometricallyIntegral (k := K) (X := P.left)
  have H : IsPullback (pullback.fst P.hom T.hom) (pullback.snd P.hom T.hom)
      (P.left ↘ Spec (.of K)) T.hom :=
    IsPullback.of_hasPullback P.hom T.hom
  refine isInvertible_pushforward_and_isIso_counit _
    (Scheme.Hom.bijective_app_of_isIso_app_of_isAffineOpen _ fun _ hA ↦
      Scheme.GlobalSectionsBijective.isIso_app_of_isPullback H hA) L U hU hL

end AlgebraicGeometry
