/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Morphisms into a locally constant sheaf are determined on a dense open

Let `j : U ⟶ X` be an open immersion with dense image and `M` a locally constant sheaf of
`Λ`-modules on the small étale site of `X`. Two morphisms `L ⟶ M` which agree after restriction
along `j` agree.

A section `b` of `M` over an étale `V ⟶ X` is, étale-locally on `V`, a constant section `n` of
a constant sheaf. Near a point of `V` lying over `U` its germ vanishes, because the stalks of
`M` at the geometric points of `U` are those of `j^* M`. Since `V ⟶ X` is open, every nonempty
étale neighbourhood meets the preimage of `U`, and a constant section vanishing on a nonempty
étale scheme is zero. Hence `b` vanishes locally, hence vanishes.

## Main statements

- `AlgebraicGeometry.Etale.upperStar_map_injective_of_isLocallyConstantSheaf`
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ] {X U : Scheme.{u}} (j : U ⟶ X)

/-- A constant section of the constant sheaf of modules that vanishes on a nonempty étale
`X`-scheme is zero: two constant sections agree after sheafification only locally, and the
empty sieve does not cover a nonempty scheme. -/
lemma eq_zero_of_toSheafify_app_eq_zero {N : ModuleCat.{u + 1} Λ} {W : X.Etale}
    [Nonempty W.left] (n : N)
    (h : (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)).app (op W) n = 0) :
    n = 0 := by
  have hW := (X.smallEtaleTopology.W_toSheafify
    ((Functor.const X.Etaleᵒᵖ).obj N)).isLocallyInjective
  have hmem := Presheaf.equalizerSieve_mem X.smallEtaleTopology
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)) n 0
    (h.trans (map_zero _).symm)
  by_contra hn
  refine bot_not_mem_smallEtaleTopology W (X.smallEtaleTopology.superset_covering ?_ hmem)
  intro V g hg
  exact hn hg

/-- A nonempty étale `X`-scheme has a point over an open with dense image, étale morphisms
being open. -/
lemma exists_apply_mem_range_of_dense (hj : Dense (Set.range j.base)) (W : X.Etale)
    [Nonempty W.left] : ∃ w : W.left, W.hom w ∈ Set.range j.base := by
  have : Etale W.hom := W.prop
  obtain ⟨x, ⟨w, -, rfl⟩, hx⟩ := hj.inter_open_nonempty _ (W.hom.isOpenMap _ isOpen_univ)
    ⟨_, Set.mem_image_of_mem _ (Set.mem_univ (Classical.arbitrary W.left))⟩
  exact ⟨w, hx⟩

variable {L M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} {χ : L ⟶ M}

/-- The stalk of `χ` at a geometric point factoring through `j` vanishes when `j^* χ` does. -/
lemma sheafFiber_map_comp_eq_zero (hχ : ((j)^*[ModuleCat.{u + 1} Λ]).map χ = 0)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ U) :
    (pointSmallEtale (t ≫ j)).sheafFiber.map χ = 0 := by
  have h := (upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) j t).hom.naturality χ
  rw [Functor.comp_map, hχ, Functor.map_zero, zero_comp] at h
  exact (cancel_epi ((upperStarCompSheafFiberIso _ j t).hom.app L)).1 (h.symm.trans comp_zero.symm)

/-- A section of the form `χ a` vanishes on a nonempty étale neighbourhood of every point lying
over `U`, when `j^* χ` vanishes: its germ there is the image of the germ of `a` under the
vanishing stalk of `χ`. -/
lemma exists_map_eq_zero_of_mem_range [IsOpenImmersion j]
    (hχ : ((j)^*[ModuleCat.{u + 1} Λ]).map χ = 0)
    {W : X.Etale} (a : ToType (L.obj.obj (op W))) (w : W.left)
    (hw : W.hom w ∈ Set.range j.base) :
    ∃ (W' : X.Etale) (g : W' ⟶ W), Nonempty W'.left ∧
      M.obj.map g.op (χ.hom.app (op W) a) = 0 := by
  let s' := W.left.algClosurePoint w
  have hs : Set.range (s' ≫ W.hom).base ⊆ Set.range j.base := by
    rintro _ ⟨x, rfl⟩
    simpa [s'] using hw
  let t := IsOpenImmersion.lift j (s' ≫ W.hom) hs
  have ht : t ≫ j = s' ≫ W.hom := IsOpenImmersion.lift_fac _ _ _
  let Φ := pointSmallEtale (t ≫ j)
  let x : Φ.fiber.obj W := Over.homMk s' ht.symm
  have h0 : Φ.toPresheafFiber W x M.obj (χ.hom.app (op W) a) =
      Φ.toPresheafFiber W x M.obj 0 := by
    rw [map_zero]
    have := ConcreteCategory.congr_hom (Φ.toPresheafFiber_naturality χ.hom W x) a
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    rw [← this]
    exact ConcreteCategory.congr_hom (sheafFiber_map_comp_eq_zero j hχ t) _
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨W', g, y, -, hy⟩ := (Φ.toPresheafFiber_eq_iff' W x _ _).1 h0
  exact ⟨W', g, ⟨y.left (IsLocalRing.closedPoint _)⟩, by simpa using hy⟩

/-- **Morphisms into a locally constant sheaf are determined on a dense open.** For an open
immersion `j : U ⟶ X` with dense image and a locally constant sheaf `M` of `Λ`-modules on the
small étale site of `X`, restriction along `j` is injective on morphisms `L ⟶ M`. -/
theorem upperStar_map_injective_of_isLocallyConstantSheaf [IsOpenImmersion j]
    (hj : Dense (Set.range j.base))
    [IsLocallyConstantSheaf M] :
    Function.Injective fun φ : L ⟶ M ↦ ((j)^*[ModuleCat.{u + 1} Λ]).map φ := by
  intro φ ψ h
  rw [← sub_eq_zero]
  have hχ : ((j)^*[ModuleCat.{u + 1} Λ]).map (φ - ψ) = 0 := by
    rw [Functor.map_sub, sub_eq_zero]
    exact h
  generalize φ - ψ = χ at hχ ⊢
  obtain ⟨⟨𝒰, hc⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := M)
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  refine Sheaf.hom_ext (NatTrans.ext (funext fun V ↦ ModuleCat.hom_ext
    (LinearMap.ext fun a ↦ ?_)))
  induction V using Opposite.rec with | op V => ?_
  change χ.hom.app (op V) a = 0
  set b := χ.hom.app (op V) a
  -- the sieve of étale `V`-schemes on which `b` vanishes covers `V`
  let S : Sieve V :=
    { arrows W g := M.obj.map g.op b = 0
      downward_closed {W W'} g hg g' := by
        rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hg, map_zero] }
  refine Sheaf.isSeparated M V S ?_ b 0 fun W g hg ↦ by rw [map_zero]; exact hg
  rw [mem_smallEtaleTopology_iff]
  intro v
  -- a member `Uᵢ` of the trivialising cover through the image of `v`
  obtain ⟨i, u, hu⟩ := 𝒰.exists_eq (V.hom v)
  set Ui := 𝒰.etalePrecoverageToEtale i
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  have : Etale V.hom := V.prop
  let W₁ : X.Etale := Scheme.Etale.mk (pullback.fst V.hom (𝒰.f i) ≫ V.hom)
  let g₁ : W₁ ⟶ V := MorphismProperty.Over.homMk (pullback.fst V.hom (𝒰.f i))
  let h₁ : W₁ ⟶ Ui := MorphismProperty.Over.homMk (pullback.snd V.hom (𝒰.f i))
    pullback.condition.symm
  obtain ⟨w₁, hw₁, -⟩ := Scheme.Pullback.exists_preimage_pullback v u hu.symm
  -- `M` is constant over `Uᵢ`
  have := hc i
  obtain ⟨N, ⟨e₀⟩⟩ := (M.over Ui).mem_essImage_of_isConstant (J := X.smallEtaleTopology.over Ui)
  let e : M.over Ui ≅ ((constantSheaf X.smallEtaleTopology _).obj N).over Ui :=
    e₀.symm ≪≫ constantSheafOverIso X.smallEtaleTopology _ Ui N
  set NX := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N
  have hnat {W W'' : Over Ui} (k : W'' ⟶ W) (y : ToType (M.obj.obj (op W.left))) :
      e.hom.hom.app (op W'') (M.obj.map k.left.op y) =
        NX.obj.map k.left.op (e.hom.hom.app (op W) y) :=
    ConcreteCategory.congr_hom (e.hom.hom.naturality k.op) y
  let W₁' : Over Ui := Over.mk h₁
  let c : ToType (NX.obj.obj (op W₁)) := e.hom.hom.app (op W₁') (M.obj.map g₁.op b)
  -- `c` is locally constant
  have hsurj := (X.smallEtaleTopology.W_toSheafify
    ((Functor.const X.Etaleᵒᵖ).obj N)).isLocallySurjective
  obtain ⟨W₂, g₂, ⟨n, hn⟩, w₂, hw₂⟩ := (mem_smallEtaleTopology_iff _).1
    (Presheaf.imageSieve_mem X.smallEtaleTopology
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)) c) w₁
  have : Nonempty W₂.left := ⟨w₂⟩
  -- the constant `n` vanishes, by looking near a point over `U`
  have hn0 : n = 0 := by
    obtain ⟨w, hw⟩ := exists_apply_mem_range_of_dense j hj W₂
    obtain ⟨W₃, g₃, hW₃, h₃⟩ := exists_map_eq_zero_of_mem_range j hχ
      (L.obj.map (g₂ ≫ g₁).op a) w hw
    have : Nonempty W₃.left := hW₃
    refine eq_zero_of_toSheafify_app_eq_zero (N := N) (W := W₃) n ?_
    have hχa : χ.hom.app (op W₂) (L.obj.map (g₂ ≫ g₁).op a) = M.obj.map (g₂ ≫ g₁).op b := by
      rw [← ConcreteCategory.comp_apply, χ.hom.naturality]
      rfl
    have hb : M.obj.map (g₃ ≫ g₂).op (M.obj.map g₁.op b) = 0 := by
      have e₁ : M.obj.map (g₃ ≫ g₂).op (M.obj.map g₁.op b) =
          M.obj.map g₃.op (M.obj.map (g₂ ≫ g₁).op b) := by
        simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, Category.assoc]
      rw [e₁, ← hχa, h₃]
    have := hnat (W := W₁') (W'' := Over.mk ((g₃ ≫ g₂) ≫ h₁)) (Over.homMk (g₃ ≫ g₂))
      (M.obj.map g₁.op b)
    have h₄ : (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)).app (op W₃) n =
        NX.obj.map (g₃ ≫ g₂).op c := by
      rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      erw [← hn]
      exact ConcreteCategory.congr_hom
        ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj N)).naturality g₃.op) n
    rw [h₄]
    refine this.symm.trans ?_
    change e.hom.hom.app (op (Over.mk ((g₃ ≫ g₂) ≫ h₁))) (M.obj.map (g₃ ≫ g₂).op _) = 0
    rw [hb]
    exact LinearMap.map_zero _
  -- hence `b` vanishes on `W₂`
  let W₂' : Over Ui := Over.mk (g₂ ≫ h₁)
  have h₅ : e.hom.hom.app (op W₂') (M.obj.map g₂.op (M.obj.map g₁.op b)) = 0 := by
    refine (hnat (W := W₁') (W'' := W₂') (Over.homMk g₂) (M.obj.map g₁.op b)).trans ?_
    change NX.obj.map g₂.op c = 0
    erw [← hn, hn0]
    exact map_zero _
  have hinj := (((sheafToPresheaf _ _).mapIso e).app (op W₂')).toLinearEquiv.injective
  refine ⟨W₂, g₂ ≫ g₁, ?_, w₂, ?_⟩
  · change M.obj.map (g₂ ≫ g₁).op b = 0
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    exact hinj (h₅.trans (LinearMap.map_zero _).symm)
  · change (g₂.left ≫ g₁.left) w₂ = v
    rw [Scheme.Hom.comp_apply, hw₂]
    exact hw₁

end Etale

end AlgebraicGeometry
