/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.DivisorSequence
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Connecting
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# The generic Kummer residue sheaf

Let `C` be a smooth integral curve over an algebraically closed field `k`, let `n` be invertible
in `k` and let `η : Spec k(C) ⟶ C` be the generic point. Then the valuations at the closed points
induce an isomorphism of étale sheaves

```
  R¹η_* μₙ ≅ ⨁_{x ∈ C closed} i_{x*} ℤ/n.
```

We do not use the stalk formula for strict henselisations. Instead:

1. `R¹η_* 𝔾ₘ = 0` (`AlgebraicGeometry.Scheme.epi_lowerStar_map_cokernelπ_upperStar_gmSheaf`,
   Hilbert 90 on the generic fibres), so the long exact sequence of right derived functors of
   `η_*` applied to the Kummer sequence of `Spec k(C)` identifies `R¹η_* μₙ` with the cokernel of
   `n` on `η_* 𝔾ₘ`;
2. the divisor sequence `0 → 𝔾ₘ → η_* 𝔾ₘ → ⨁_x i_{x*} ℤ → 0` and the surjectivity of `n` on
   `𝔾ₘ` of `C` (Kummer) identify this with the cokernel of `n` on `⨁_x i_{x*} ℤ`, the identification
   being induced by the divisor map;
3. finally the cokernel of `n` on `i_{x*} ℤ` is `i_{x*} ℤ/n`, since `i_{x*}` is exact for a closed
   point `x`.

Here `R¹η_*` is the first right derived functor `Functor.rightDerived` of
`η_* = Etale.lowerStar AddCommGrpCat η`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory.Limits.CokernelCofork

section Preadditive

variable {C : Type*} [Category* C] [Preadditive C]

/-- A cokernel of an endomorphism `f'` of `Y` gives one of an endomorphism `f` of `X` which is
conjugate to `f'` by an isomorphism `e : X ≅ Y`. -/
noncomputable def isColimitOfπOfIso {X Y Z : C} {f : X ⟶ X} {f' : Y ⟶ Y} (e : X ≅ Y)
    (he : f ≫ e.hom = e.hom ≫ f') {π : Y ⟶ Z} (w : f' ≫ π = 0)
    (h : IsColimit (CokernelCofork.ofπ π w)) :
    IsColimit (CokernelCofork.ofπ (f := f) (e.hom ≫ π)
      (by rw [← Category.assoc, he, Category.assoc, w, comp_zero])) :=
  have : Epi π := epi_of_isColimit_cofork h
  IsColimit.ofπ' _ _ fun {A} k hk ↦ by
    have hk2 : f' ≫ e.inv ≫ k = 0 := by
      rw [← Category.assoc, show f' ≫ e.inv = e.inv ≫ f by
        rw [Iso.comp_inv_eq, Category.assoc, he, Iso.inv_hom_id_assoc], Category.assoc, hk,
        comp_zero]
    have hd : π ≫ h.desc (CokernelCofork.ofπ (e.inv ≫ k) hk2) = e.inv ≫ k :=
      Cofork.IsColimit.π_desc h
    exact ⟨h.desc (CokernelCofork.ofπ (e.inv ≫ k) hk2), by
      rw [Category.assoc, hd]
      exact Iso.hom_inv_id_assoc _ _⟩

/-- **Cokernels of `n` commute with coproducts.** If `q i : P i ⟶ P' i` is a cokernel of
multiplication by `n` on `P i` for every `i`, then the induced map `∐ P ⟶ ∐ P'` is a cokernel of
multiplication by `n` on `∐ P`, for any colimit cofans. -/
noncomputable def isColimitOfπNsmulOfCofan {ι : Type*} {P P' : ι → C} (n : ℕ)
    (q : ∀ i, P i ⟶ P' i) (w : ∀ i, (n • 𝟙 (P i)) ≫ q i = 0)
    (hq : ∀ i, IsColimit (CokernelCofork.ofπ (q i) (w i))) {c : Cofan P} (hc : IsColimit c)
    {c' : Cofan P'} (hc' : IsColimit c') :
    IsColimit (CokernelCofork.ofπ (f := n • 𝟙 c.pt)
      (Cofan.IsColimit.desc hc fun i ↦ q i ≫ c'.inj i) (Cofan.IsColimit.hom_ext hc _ _ fun i ↦ by
        simp only [Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul,
          Cofan.IsColimit.fac, comp_zero]
        rw [← Preadditive.nsmul_comp, show n • q i = 0 by simpa using w i, zero_comp])) :=
  have hk (i : ι) {A : C} (k : c.pt ⟶ A) (hk : (n • 𝟙 c.pt) ≫ k = 0) :
      (n • 𝟙 (P i)) ≫ c.inj i ≫ k = 0 := by
    simp only [Preadditive.nsmul_comp, Category.id_comp] at hk ⊢
    rw [← Preadditive.comp_nsmul, hk, comp_zero]
  IsColimit.ofπ _ _
    (fun {A} k hk' ↦ Cofan.IsColimit.desc hc' fun i ↦
      (hq i).desc (CokernelCofork.ofπ (c.inj i ≫ k) (hk i k hk')))
    (fun {A} k hk' ↦ Cofan.IsColimit.hom_ext hc _ _ fun i ↦ by
      rw [← Category.assoc, Cofan.IsColimit.fac, Category.assoc, Cofan.IsColimit.fac]
      exact Cofork.IsColimit.π_desc (hq i))
    (fun {A} k hk' m hm ↦ Cofan.IsColimit.hom_ext hc' _ _ fun i ↦ by
      have : Epi (q i) := epi_of_isColimit_cofork (hq i)
      rw [← cancel_epi (q i), Cofan.IsColimit.fac]
      have hd : q i ≫ (hq i).desc (CokernelCofork.ofπ (c.inj i ≫ k) (hk i k hk')) =
          c.inj i ≫ k := Cofork.IsColimit.π_desc (hq i)
      rw [hd, ← hm, ← Category.assoc, ← Category.assoc, Cofan.IsColimit.fac])

end Preadditive

variable {C : Type*} [Category* C]

/-- **Cokernels of compatible endomorphisms of a short exact sequence.** Let `a`, `b`, `c` be
endomorphisms of the terms of a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, compatible with its
maps, with `a` an epimorphism. Then a cokernel `π` of `c` gives the cokernel `g ≫ π` of `b`. -/
noncomputable def isColimitOfπOfShortExact [Abelian C] {S : ShortComplex C} (hS : S.ShortExact)
    {a : S.X₁ ⟶ S.X₁} {b : S.X₂ ⟶ S.X₂} {c : S.X₃ ⟶ S.X₃} (hab : a ≫ S.f = S.f ≫ b)
    (hbc : b ≫ S.g = S.g ≫ c) [Epi a] {Z : C} {π : S.X₃ ⟶ Z} (w : c ≫ π = 0)
    (h : IsColimit (CokernelCofork.ofπ π w)) :
    IsColimit (CokernelCofork.ofπ (f := b) (S.g ≫ π)
      (by rw [← Category.assoc, hbc, Category.assoc, w, comp_zero])) :=
  have : Epi π := epi_of_isColimit_cofork h
  have : Epi S.g := hS.epi_g
  IsColimit.ofπ' _ _ fun {A} k hk ↦ by
    have hfk : S.f ≫ k = 0 := (cancel_epi a).1 (by
      rw [← Category.assoc, hab, Category.assoc, hk, comp_zero, comp_zero])
    let k' := hS.exact.gIsCokernel.desc (CokernelCofork.ofπ k hfk)
    have hk' : S.g ≫ k' = k := Cofork.IsColimit.π_desc hS.exact.gIsCokernel
    have hck : c ≫ k' = 0 := (cancel_epi S.g).1 (by
      rw [← Category.assoc, ← hbc, Category.assoc, hk', hk, comp_zero])
    have hd : π ≫ h.desc (CokernelCofork.ofπ k' hck) = k' := Cofork.IsColimit.π_desc h
    exact ⟨h.desc (CokernelCofork.ofπ k' hck), by rw [Category.assoc, hd, hk']⟩

end CategoryTheory.Limits.CokernelCofork

namespace AlgebraicGeometry.Scheme

section Generic

variable (X : Scheme.{u}) [IsIntegral X]

/-- `η_*` along the generic point, on abelian étale sheaves. -/
noncomputable abbrev genericLowerStar :
    Sheaf (Spec X.functionField).smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Etale.lowerStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField

/-- **`R¹η_* 𝔾ₘ = 0`** along the generic point `η` of an integral regular noetherian scheme, for
the first right derived functor of `η_*`. -/
theorem isZero_rightDerived_one_genericLowerStar_upperStar_gmSheaf [IsNoetherian X]
    [IsRegular X] :
    IsZero ((X.genericLowerStar.rightDerived 1).obj
      ((Etale.upperStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj X.gmSheaf)) := by
  let := HasDerivedCategory.standard (Sheaf (Spec X.functionField).smallEtaleTopology
    AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  set F := X.genericLowerStar
  set A := (Etale.upperStar AddCommGrpCat.{u + 1} X.fromSpecFunctionField).obj X.gmSheaf
  let ι := Injective.ι A
  have hS : (ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel ι) inferInstance inferInstance
  have hepi : Epi (F.map (cokernel.π ι)) := X.epi_lowerStar_map_cokernelπ_upperStar_gmSheaf ι
  have hepi0 : Epi ((F.rightDerived 0).map (cokernel.π ι)) := by
    have h : (F.rightDerived 0).map (cokernel.π ι) = F.rightDerivedZeroIsoSelf.hom.app _ ≫
        F.map (cokernel.π ι) ≫ F.rightDerivedZeroIsoSelf.inv.app _ := by
      simp
    rw [h]
    infer_instance
  have h0 : hS.rightDerivedδ F 0 = 0 :=
    (cancel_epi ((F.rightDerived 0).map (cokernel.π ι))).1 (by
      rw [hS.comp_rightDerivedδ F 0, comp_zero])
  have hI : IsZero ((F.rightDerived (0 + 1)).obj (Injective.under A)) :=
    F.isZero_rightDerived_obj_injective_succ 0 _
  have hδ : Epi (hS.rightDerivedδ F 0) := (hS.rightDerivedδ_exact₃ F 0).epi_f (hI.eq_of_tgt _ _)
  rw [h0] at hδ
  exact IsZero.of_epi_zero ((F.rightDerived 0).obj (cokernel ι)) _

/-- **`R¹η_* μₙ` is the cokernel of `n` on `η_* 𝔾ₘ`.** Let `X` be an integral regular noetherian
scheme with generic point `η`, and let `n` be invertible in `k(X)`. The connecting morphism
`δ : η_* 𝔾ₘ ⟶ R¹η_* μₙ` of the long exact sequence of right derived functors of `η_*` applied to
the Kummer sequence of `Spec k(X)` is a cokernel of `n : η_* 𝔾ₘ ⟶ η_* 𝔾ₘ`, since `R¹η_* 𝔾ₘ = 0`
(`AlgebraicGeometry.Scheme.isZero_rightDerived_one_genericLowerStar_upperStar_gmSheaf`). -/
theorem exists_isColimit_rightDerived_one_rootsOfUnitySheaf [IsNoetherian X] [IsRegular X]
    (n : ℕ) (hn : IsUnit (n : X.functionField)) :
    ∃ (δ : X.genericGm ⟶ (X.genericLowerStar.rightDerived 1).obj
        ((Spec X.functionField).rootsOfUnitySheaf n)) (w : (n • 𝟙 X.genericGm) ≫ δ = 0),
      Nonempty (IsColimit (CokernelCofork.ofπ δ w)) := by
  let := HasDerivedCategory.standard (Sheaf (Spec X.functionField).smallEtaleTopology
    AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  set F := X.genericLowerStar
  have hn' : IsUnit (n : Γ(Spec X.functionField, ⊤)) := by
    simpa using hn.map (ΓSpecIso X.functionField).inv.hom
  have hK := (Spec X.functionField).kummerSequence_shortExact n hn'
  have := X.isIso_upperStarGmSheafToGmSheaf_fromSpecFunctionField
  have hG : IsZero ((F.rightDerived (0 + 1)).obj (Spec X.functionField).gmSheaf) :=
    X.isZero_rightDerived_one_genericLowerStar_upperStar_gmSheaf.of_iso
      ((F.rightDerived 1).mapIso (asIso (upperStarGmSheafToGmSheaf X.fromSpecFunctionField))).symm
  have : Epi (hK.rightDerivedδ F 0) := (hK.rightDerivedδ_exact₃ F 0).epi_f (hG.eq_of_tgt _ _)
  have h₀ := (hK.rightDerivedδ_exact₂ F 0).gIsCokernel
  let e₁ : X.genericGm ≅ (F.rightDerived 0).obj (Spec X.functionField).gmSheaf :=
    X.genericGmIso ≪≫ (F.rightDerivedZeroIsoSelf.app _).symm
  have he : (n • 𝟙 X.genericGm) ≫ e₁.hom =
      e₁.hom ≫ (F.rightDerived 0).map ((Spec X.functionField).kummerSequence n).g := by
    change _ = e₁.hom ≫ (F.rightDerived 0).map (n • 𝟙 _)
    simp only [Functor.map_nsmul, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  exact ⟨_, _, ⟨CokernelCofork.isColimitOfπOfIso e₁ he _ h₀⟩⟩

end Generic

end AlgebraicGeometry.Scheme
