/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint
public import WeilConjectures.AlgebraicGeometry.Curve.Divisor
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.AlgebraicGeometry.Sites.DivisorSequence
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Connecting
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.SixFunctors.Finite.Exact

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

/-- A cokernel of `f` is a cokernel of any `f' = f`. -/
noncomputable def isColimitOfπOfEq {X Y Z : C} {f f' : X ⟶ Y} (hf : f = f') {π : Y ⟶ Z}
    (w : f ≫ π = 0) (h : IsColimit (CokernelCofork.ofπ π w)) :
    IsColimit (CokernelCofork.ofπ (f := f') π (hf ▸ w)) := by
  subst hf
  exact h

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

namespace CategoryTheory

/-- The constant functor into a functor category preserves finite limits, which are computed
pointwise. -/
instance Functor.const_preservesFiniteLimits {C A : Type*} [Category* C] [Category* A] :
    PreservesFiniteLimits (Functor.const C : A ⥤ C ⥤ A) :=
  preservesFiniteLimits_of_evaluation _ fun _ ↦
    preservesFiniteLimits_of_natIso (NatIso.ofComponents (fun _ ↦ Iso.refl _) : 𝟭 A ≅ _)

end CategoryTheory

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

/-- **The cokernel of `n` on `η_* 𝔾ₘ` is the cokernel of `n` on the divisors.** Let `X` be an
integral regular locally noetherian scheme on which `n` is invertible. Composing the divisor map
`η_* 𝔾ₘ ⟶ ⨁_{x ∈ X⁽¹⁾} i_{x*} ℤ` with a cokernel of `n` on its target gives a cokernel of `n` on
`η_* 𝔾ₘ`, as `n` is surjective on `𝔾ₘ` by the Kummer sequence. -/
noncomputable def isColimitOfπDivisorSequenceMapComp [IsLocallyNoetherian X] [IsRegular X]
    (c : Cofan fun x : {x : X // Order.coheight x = 1} ↦ X.pointConstantInt x.1)
    (hc : IsColimit c) (n : ℕ) (hn : IsUnit (n : Γ(X, ⊤))) {Z : Sheaf X.smallEtaleTopology
      AddCommGrpCat.{u + 1}} {π : c.pt ⟶ Z} (w : (n • 𝟙 c.pt) ≫ π = 0)
    (h : IsColimit (CokernelCofork.ofπ π w)) :
    IsColimit (CokernelCofork.ofπ (f := n • 𝟙 X.genericGm) (X.divisorSequenceMap c hc ≫ π)
      (by rw [← Category.assoc, show (n • 𝟙 _) ≫ X.divisorSequenceMap c hc =
        X.divisorSequenceMap c hc ≫ (n • 𝟙 _) by simp, Category.assoc, w, comp_zero])) :=
  have : Epi (n • 𝟙 X.gmSheaf) := (X.kummerSequence_shortExact n hn).epi_g
  CokernelCofork.isColimitOfπOfShortExact (X.shortExact_divisorSequence c hc)
    (a := n • 𝟙 _) (b := n • 𝟙 _) (c := n • 𝟙 _) (by simp) (by simp) w h

end Generic

section Point

/-- The reduction map `ℤ ⟶ ℤ/n`. -/
noncomputable def intToZMod (n : ℕ) :
    AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ AddCommGrpCat.of (ULift.{u + 1} (ZMod n)) :=
  AddCommGrpCat.ofHom (AddEquiv.ulift.symm.toAddMonoidHom.comp
    ((Int.castAddHom (ZMod n)).comp AddEquiv.ulift.toAddMonoidHom))

lemma nsmul_comp_intToZMod (n : ℕ) :
    (n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ))) ≫ intToZMod.{u} n = 0 := by
  ext x
  simp [intToZMod]

/-- The short exact sequence `0 ⟶ ℤ ⟶ ℤ ⟶ ℤ/n ⟶ 0` of abelian groups, for `n ≠ 0`. -/
lemma shortExact_intToZMod (n : ℕ) (hn : n ≠ 0) :
    (ShortComplex.mk _ _ (nsmul_comp_intToZMod.{u} n)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.ab_exact_iff]
    intro x hx
    have hx' : ((x.down : ℤ) : ZMod n) = 0 := congrArg ULift.down hx
    obtain ⟨m, hm⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hx'
    exact ⟨ULift.up m, ULift.ext _ _ (by
      change (n • ULift.up m : ULift.{u + 1} ℤ).down = x.down
      simp [hm])⟩
  · rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    have : (n : ℤ) * a.down = n * b.down := by
      simpa [nsmul_eq_mul] using congrArg ULift.down hab
    exact ULift.ext _ _ (mul_left_cancel₀ (by exact_mod_cast hn) this)
  · rw [AddCommGrpCat.epi_iff_surjective]
    intro y
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective y.down
    exact ⟨ULift.up m, ULift.ext _ _ hm⟩

variable (X : Scheme.{u})

/-- The étale sheaf `i_{x*} ℤ/n` on `X`: the pushforward of the constant sheaf `ℤ/n` along
`Spec κ(x) ⟶ X`. -/
noncomputable def pointConstantZMod (x : X) (n : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} (X.fromSpecResidueField x)).obj
    ((constantSheaf _ AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))))

/-- The reduction map `i_{x*} ℤ ⟶ i_{x*} ℤ/n`. -/
noncomputable def pointConstantIntToZMod (x : X) (n : ℕ) :
    X.pointConstantInt x ⟶ X.pointConstantZMod x n :=
  (Etale.lowerStar AddCommGrpCat.{u + 1} (X.fromSpecResidueField x)).map
    ((constantSheaf _ AddCommGrpCat.{u + 1}).map (intToZMod n))

/-- **`i_{x*} ℤ/n` is the cokernel of `n` on `i_{x*} ℤ`** for a closed point `x`: the constant
sheaf functor is exact, and so is `i_{x*}`, the pushforward along a closed immersion. -/
theorem exists_isColimit_pointConstantIntToZMod {x : X} (hx : IsClosed {x}) (n : ℕ)
    (hn : n ≠ 0) :
    ∃ (w : (n • 𝟙 (X.pointConstantInt x)) ≫ X.pointConstantIntToZMod x n = 0),
      Nonempty (IsColimit (CokernelCofork.ofπ _ w)) := by
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  set G := Etale.lowerStar AddCommGrpCat.{u + 1} (X.fromSpecResidueField x)
  set K := constantSheaf (Spec (X.residueField x)).smallEtaleTopology AddCommGrpCat.{u + 1}
  have : PreservesFiniteLimits K :=
    inferInstanceAs (PreservesFiniteLimits (Functor.const _ ⋙ presheafToSheaf _ _))
  have hS₁ := (shortExact_intToZMod.{u} n hn).map_of_exact K
  have := hS₁.mono_f
  have := hS₁.epi_g
  have hS₂ : ((ShortComplex.mk _ _ (nsmul_comp_intToZMod.{u} n)).map K |>.map G).Exact :=
    hS₁.exact.map_of_mono_of_preservesKernel G hS₁.mono_f inferInstance
  have : Epi (((ShortComplex.mk _ _ (nsmul_comp_intToZMod.{u} n)).map K |>.map G).g) :=
    G.map_epi _
  have hf : G.map (K.map (n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) =
      n • 𝟙 (X.pointConstantInt x) := by
    rw [Functor.map_nsmul, Functor.map_nsmul, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id]
    rfl
  exact ⟨_, ⟨CokernelCofork.isColimitOfπOfEq hf _ hS₂.gIsCokernel⟩⟩

end Point

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.IsCurve

open Scheme

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsCurve f]
  [SmoothOfRelativeDimension 1 f]

include f

omit [IsCurve f] in
/-- A closed point of a smooth curve has coheight one. -/
lemma coheight_eq_one_of_isClosed {x : C} (hx : IsClosed {x}) : Order.coheight x = 1 := by
  have h := ringKrullDim_stalk_eq_one_of_smoothOfRelativeDimension_one f hx
  rw [ringKrullDim_stalk_eq_coheight] at h
  exact_mod_cast h

/-- A point of coheight one of a smooth curve is closed: otherwise it specializes to a closed
point, which would have coheight at least two. -/
lemma isClosed_of_coheight_eq_one {x : C} (hx : Order.coheight x = 1) : IsClosed {x} := by
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  by_contra hnc
  obtain ⟨y, hy, hyc⟩ :=
    isClosed_closure.exists_closed_singleton (S := closure {x}) ⟨x, subset_closure rfl⟩
  have hne : y ≠ x := fun h ↦ hnc (h ▸ hyc)
  have h := Order.coheight_add_one_le
    (lt_of_specializes_of_ne C (specializes_iff_mem_closure.2 hy) hne)
  rw [hx, coheight_eq_one_of_isClosed f hyc] at h
  exact absurd h (by decide)

variable [IsIntegral C]

/-- **The generic Kummer residue sheaf, with its valuation description.** Let `C` be a smooth
integral curve over a field `k`, let `n` be invertible in `k` and let `η : Spec k(C) ⟶ C` be the
generic point. Given colimit cofans `c₀` of the sheaves `i_{x*} ℤ` over the points of coheight
one and `c` of the sheaves `i_{x*} ℤ/n` over the closed points of `C` (these are the same
points), there are

* a cokernel `δ : η_* 𝔾ₘ ⟶ R¹η_* μₙ` of `n` on `η_* 𝔾ₘ` (the Kummer connecting morphism),
* the reduction `r : ⨁_x i_{x*} ℤ ⟶ ⨁_x i_{x*} ℤ/n`, and
* an isomorphism `e : R¹η_* μₙ ≅ ⨁_x i_{x*} ℤ/n`

such that `δ ≫ e = div ≫ r`: the isomorphism is induced by the valuations at the closed points,
via the divisor map `div` (`AlgebraicGeometry.Scheme.divisorSequenceMap`). -/
theorem exists_iso_rightDerived_one_rootsOfUnitySheaf [IsLocallyNoetherian C] [IsRegular C]
    (n : ℕ) (hn : (n : k) ≠ 0)
    (c₀ : Cofan fun x : {x : C // Order.coheight x = 1} ↦ C.pointConstantInt x.1)
    (hc₀ : IsColimit c₀) (c : Cofan fun x : {x : C // IsClosed {x}} ↦ C.pointConstantZMod x.1 n)
    (hc : IsColimit c) :
    ∃ (δ : C.genericGm ⟶ (C.genericLowerStar.rightDerived 1).obj
        ((Spec C.functionField).rootsOfUnitySheaf n)) (w : (n • 𝟙 C.genericGm) ≫ δ = 0)
      (r : c₀.pt ⟶ c.pt) (e : (C.genericLowerStar.rightDerived 1).obj
        ((Spec C.functionField).rootsOfUnitySheaf n) ≅ c.pt),
      Nonempty (IsColimit (CokernelCofork.ofπ δ w)) ∧
      (∀ (x : C) (h₁ : Order.coheight x = 1) (h₂ : IsClosed {x}),
        c₀.inj ⟨x, h₁⟩ ≫ r = C.pointConstantIntToZMod x n ≫ c.inj ⟨x, h₂⟩) ∧
      δ ≫ e.hom = C.divisorSequenceMap c₀ hc₀ ≫ r := by
  have : CompactSpace C := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : IsNoetherian C := ⟨⟩
  have hnC : IsUnit (n : Γ(C, ⊤)) := by
    simpa using hn.isUnit.map ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  obtain ⟨x₀⟩ := (inferInstance : Nonempty C)
  have : Nonempty (⊤ : C.Opens) := ⟨⟨x₀, trivial⟩⟩
  have hnK : IsUnit (n : C.functionField) := by
    simpa using hnC.map (C.germToFunctionField ⊤).hom
  have hn₀ : n ≠ 0 := by
    rintro rfl
    exact hn Nat.cast_zero
  obtain ⟨δ, w, ⟨hδ⟩⟩ := C.exists_isColimit_rightDerived_one_rootsOfUnitySheaf n hnK
  let c' : Cofan fun x : {x : C // Order.coheight x = 1} ↦ C.pointConstantZMod x.1 n :=
    Cofan.mk c.pt fun x ↦ c.inj ⟨x.1, isClosed_of_coheight_eq_one f x.2⟩
  have hc' : IsColimit c' := Cofan.IsColimit.mk c'
    (fun t ↦ Cofan.IsColimit.desc hc fun x ↦ t.inj ⟨x.1, coheight_eq_one_of_isClosed f x.2⟩)
    (fun t x ↦ Cofan.IsColimit.fac hc _ _)
    (fun t m hm ↦ Cofan.IsColimit.hom_ext hc _ _ fun x ↦ by
      rw [Cofan.IsColimit.fac]
      exact hm ⟨x.1, coheight_eq_one_of_isClosed f x.2⟩)
  have hq (x : {x : C // Order.coheight x = 1}) :=
    C.exists_isColimit_pointConstantIntToZMod (isClosed_of_coheight_eq_one f x.2) n hn₀
  choose wq hq using hq
  have hred := CokernelCofork.isColimitOfπNsmulOfCofan (C := Sheaf C.smallEtaleTopology
    AddCommGrpCat.{u + 1}) (P := fun x : {x : C // Order.coheight x = 1} ↦ C.pointConstantInt x.1)
    (P' := fun x : {x : C // Order.coheight x = 1} ↦ C.pointConstantZMod x.1 n) n
    (fun x ↦ C.pointConstantIntToZMod x.1 n) wq (fun x ↦ (hq x).some) hc₀ hc'
  have hdiv := C.isColimitOfπDivisorSequenceMapComp c₀ hc₀ n hnC _ hred
  refine ⟨δ, w, Cofan.IsColimit.desc hc₀ fun i ↦ C.pointConstantIntToZMod i.1 n ≫ c'.inj i,
    hδ.coconePointUniqueUpToIso hdiv, ⟨hδ⟩, fun x h₁ h₂ ↦ ?_, ?_⟩
  · exact Cofan.IsColimit.fac hc₀ _ _
  · exact hδ.comp_coconePointUniqueUpToIso_hom hdiv WalkingParallelPair.one

/-- **The generic Kummer residue sheaf.** Let `C` be a smooth integral curve over a field `k`
(in the blueprint `k` is algebraically closed), let `n` be invertible in `k`, let `μₙ` be the
sheaf of `n`-th roots of unity on `Spec k(C)` and `η : Spec k(C) ⟶ C` the generic point. Then

`R¹η_* μₙ ≅ ⨁_{x ∈ C closed} i_{x*} ℤ/n`,

where `R¹η_*` is the first right derived functor of `η_*` and the direct sum is the vertex of any
colimit cofan. The isomorphism is induced by the valuations at the closed points, see
`AlgebraicGeometry.IsCurve.exists_iso_rightDerived_one_rootsOfUnitySheaf`.
(blueprint: `lem-sc-generic-kummer-residues`) -/
theorem nonempty_rightDerived_one_rootsOfUnitySheaf_iso (n : ℕ) (hn : (n : k) ≠ 0)
    (c : Cofan fun x : {x : C // IsClosed {x}} ↦ C.pointConstantZMod x.1 n) (hc : IsColimit c) :
    Nonempty ((C.genericLowerStar.rightDerived 1).obj
      ((Spec C.functionField).rootsOfUnitySheaf n) ≅ c.pt) := by
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{u, u} (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsRegular C := IsRegular.of_smooth f
  let P := fun x : {x : C // Order.coheight x = 1} ↦ C.pointConstantInt x.1
  obtain ⟨-, -, -, e, -⟩ := exists_iso_rightDerived_one_rootsOfUnitySheaf f n hn
    (colimit.cocone (Discrete.functor P)) (colimit.isColimit _) c hc
  exact ⟨e⟩

end AlgebraicGeometry.IsCurve
