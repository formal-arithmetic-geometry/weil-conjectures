/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.ConstantFieldRestriction
import WeilConjectures.WeilSheaf.StalkUpperStar
import WeilConjectures.DeligneLaumon.ConstantFieldTransportStructure

/-! # Local return comparison for source constant-field restriction

Source: `thm-zl-real-mixed-by-curves`, paragraphs 1--3.
(blueprint: lem-zl-source-constant-field-restriction-stalk).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.WeilSheaf
open ProEtale

private theorem residueCard_eq_natCard {k : Type u} [Field k] [Finite k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) (z : Y.finitePoints) :
    f.residueCard z.1 = Nat.card (Y.residueField z.1) := by
  let := (f.residueFieldAlgebraMap z.1).toAlgebra
  have : Finite (Y.residueField z.1) := z.2
  exact (Module.natCard_eq_pow_finrank (K := k) (V := Y.residueField z.1)).symm

private theorem intertwines_powers {B : Type*} [Category B] {U V : B}
    (θ : U ≅ V) (f : Aut U) (g : Aut V) (r : ℕ)
    (h : θ.hom ≫ g.hom = (f ^ r).hom ≫ θ.hom) (m : ℕ) :
    θ.hom ≫ (g ^ m).hom = (f ^ (r * m)).hom ≫ θ.hom := by
  induction m with
  | zero =>
    simp only [pow_zero, Nat.mul_zero]
    change θ.hom ≫ 𝟙 V = 𝟙 U ≫ θ.hom
    simp
  | succ m ih =>
    rw [← g.pow_hom_comp_pow_hom m 1, pow_one, ← Category.assoc, h,
      Category.assoc, ih, ← Category.assoc, f.pow_hom_comp_pow_hom, Nat.mul_succ]

private theorem intertwines_inverse {B : Type*} [Category B] {U V : B}
    (θ : U ≅ V) (f : U ⟶ U) (g : V ⟶ V) (h : θ.hom ≫ g = f ≫ θ.hom) :
    g ≫ θ.inv = θ.inv ≫ f := by
  rw [← cancel_epi θ.hom, ← Category.assoc, h, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

private theorem transport_square_comm
    {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    {Y₀ Y₁ P₀ P₁ : Scheme.{u}} (j : Y₁ ⟶ Y₀) (g₀ : Y₀ ⟶ Y₀)
    (g₁ : Y₁ ⟶ Y₁) (hc : g₁ ≫ j = j ≫ g₀)
    {M : Sheaf (Scheme.ProEt.topology Y₀) A}
    {N : Sheaf (Scheme.ProEt.topology Y₁) A}
    (ψ₀ : (g₀)^*[A].obj M ⟶ M) (ψ₁ : (g₁)^*[A].obj N ⟶ N)
    (α : (j)^*[A].obj M ⟶ N)
    (hα : (upperStarComp A g₁ j).hom.app M ≫ (g₁)^*[A].map α ≫ ψ₁ =
      (upperStarCongr A hc).hom.app M ≫ (upperStarComp A j g₀).hom.app M ≫
        (j)^*[A].map ψ₀ ≫ α)
    {t₀ : P₀ ⟶ Y₀} {t₁ : P₁ ⟶ Y₁} {ε : P₁ ⟶ P₀}
    {τ₀ : P₀ ⟶ P₀} {τ₁ : P₁ ⟶ P₁}
    (h₀ : τ₀ ≫ t₀ = t₀ ≫ g₀) (h₁ : τ₁ ≫ t₁ = t₁ ≫ g₁)
    (ht : ε ≫ t₀ = t₁ ≫ j) (hε : τ₁ ≫ ε = ε ≫ τ₀) :
    globalSectionsTransport A h₀ ψ₀ ≫ globalSectionsTransport A ht α =
      globalSectionsTransport A ht α ≫ globalSectionsTransport A h₁ ψ₁ := by
  have hl : (ε ≫ τ₀) ≫ t₀ = t₁ ≫ (j ≫ g₀) := by
    rw [Category.assoc, h₀, ← Category.assoc, ht, Category.assoc]
  have hr : (τ₁ ≫ ε) ≫ t₀ = t₁ ≫ (g₁ ≫ j) := by
    rw [Category.assoc, ht, ← Category.assoc, h₁, Category.assoc]
  rw [globalSectionsTransport_comp A h₀ ht hl,
    globalSectionsTransport_comp A ht h₁ hr,
    globalSectionsTransport_congr A hr hc _ _ hα,
    globalSectionsTransport_congr_left A _ hε]

private theorem stalkEquiv_of_transportSquare
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X Y : Scheme.{u}} [X.Over (Spec (.of k₀))] [Y.Over (Spec (.of k₁))]
    (F : WeilSheaf k₀ l X) (G : WeilSheaf k₁ l Y)
    (j : (Y ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    (n m : ℕ)
    (hc : ((Y ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom ≫ j =
      j ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ n).hom)
    (α : (j)^*[WeilCoefficients.{u} l].obj F.obj.carrier.X ≅ G.obj.carrier.X)
    (hα : (upperStarComp _ _ _).hom.app F.obj.carrier.X ≫
      (((Y ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom)^*[_].map α.hom ≫
        G.frobeniusPowStr m =
      (upperStarCongr _ hc).hom.app F.obj.carrier.X ≫
        (upperStarComp _ _ _).hom.app F.obj.carrier.X ≫
          (j)^*[_].map (F.frobeniusPowStr n) ≫ α.hom)
    (ε : Spec (.of (AlgebraicClosure k₁)) ≅ Spec (.of (AlgebraicClosure k₀)))
    (s₀ : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    (s₁ : Spec (.of (AlgebraicClosure k₁)) ⟶ (Y ↘ Spec (.of k₁)).geometricFiber)
    (hs₀ : s₀ ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ n).hom =
      (specGeometricFrobenius k₀ ^ n).hom ≫ s₀)
    (hs₁ : s₁ ≫ ((Y ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₁ ^ m).hom ≫ s₁)
    (ht : ε.hom ≫ s₀ = s₁ ≫ j)
    (hε : (specGeometricFrobenius k₁ ^ m).hom ≫ ε.hom =
      ε.hom ≫ (specGeometricFrobenius k₀ ^ n).hom) :
    Nonempty ((F.stalkAt s₀ n hs₀).Equiv (G.stalkAt s₁ m hs₁)) := by
  let T := globalSectionsTransport (WeilCoefficients.{u} l) ht α.hom
  have : IsIso T := by
    dsimp only [T]
    rw [globalSectionsTransport_eq_of_iso _ ε ht]
    infer_instance
  let E := WeilCoefficients.linearEquivOfIso (asIso T)
  have hcomm := transport_square_comm j
    (((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ n).hom)
    (((Y ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom) hc
    (F.frobeniusPowStr n) (G.frobeniusPowStr m) α.hom hα hs₀.symm hs₁.symm ht hε
  refine ⟨FrobeniusModule.Equiv.ofComp E ?_⟩
  rw [frobeniusEnd_stalkAt, frobeniusEnd_stalkAt]
  change ((WeilCoefficients.toModuleCat l).map T).hom ∘ₗ _ =
    _ ∘ₗ ((WeilCoefficients.toModuleCat l).map T).hom
  simpa only [Functor.map_comp, ModuleCat.hom_comp] using
    congrArg (fun f ↦ ((WeilCoefficients.toModuleCat l).map f).hom) hcomm

private theorem exists_card_power_of_ringHom
    {K L : Type u} [Field K] [Finite K] [Field L] [Finite L] (i : K →+* L) :
    ∃ e : ℕ, 0 < e ∧ Nat.card L = Nat.card K ^ e := by
  let := i.toAlgebra
  have : Module.Finite K L := Module.Finite.of_finite
  exact ⟨Module.finrank K L, Module.finrank_pos, Module.natCard_eq_pow_finrank⟩

private theorem exists_pointDegree
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    {X C : Scheme.{u}} [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
    (c : C ⟶ X) (r : ℕ) (hr : Nat.card k₁ = Nat.card k₀ ^ r) (z : C.finitePoints) :
    ∃ (x : X.finitePoints) (e : ℕ), c z.1 = x.1 ∧ 0 < e ∧
      (C ↘ Spec (.of k₁)).residueCard z.1 = (X ↘ Spec (.of k₀)).residueCard x.1 ^ e ∧
      r * (C ↘ Spec (.of k₁)).degreeOver z.1 = e * (X ↘ Spec (.of k₀)).degreeOver x.1 := by
  let x : X.finitePoints := ⟨c z.1, Scheme.Hom.map_mem_finitePoints c z.2⟩
  have : Finite (C.residueField z.1) := z.2
  have : Finite (X.residueField x.1) := x.2
  obtain ⟨e, he, hcard⟩ := exists_card_power_of_ringHom
    (K := X.residueField x.1) (L := C.residueField z.1) (c.residueFieldMap z.1).hom
  have hq : (C ↘ Spec (.of k₁)).residueCard z.1 =
      (X ↘ Spec (.of k₀)).residueCard x.1 ^ e := by
    rw [residueCard_eq_natCard _ z, residueCard_eq_natCard _ x, hcard]
  have hdegree : r * (C ↘ Spec (.of k₁)).degreeOver z.1 =
      e * (X ↘ Spec (.of k₀)).degreeOver x.1 := by
    apply Nat.pow_right_injective (a := Nat.card k₀) Finite.one_lt_card
    simpa only [Scheme.Hom.residueCard, hr, ← pow_mul, Nat.mul_comm e] using hq
  exact ⟨x, e, rfl, he, hq, hdegree⟩

private theorem compatibleLift_image
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    {X C : Scheme.{u}} [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
    (c : C ⟶ X)
    (θ : (X ↘ Spec (.of k₀)).geometricFiber ≅ (C ↘ Spec (.of k₁)).geometricFiber)
    (ε : Spec (.of (AlgebraicClosure k₁)) ≅ Spec (.of (AlgebraicClosure k₀)))
    (hproj : θ.inv ≫ (X ↘ Spec (.of k₀)).geometricFiberProj =
      (C ↘ Spec (.of k₁)).geometricFiberProj ≫ c) (z : C.finitePoints) :
    ((ε.inv ≫ (C ↘ Spec (.of k₁)).geometricFiberPointOfFinitePoint z ≫ θ.inv) ≫
      (X ↘ Spec (.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) = c z.1 := by
  rw [Category.assoc, Category.assoc, hproj,
    ← Category.assoc ((C ↘ Spec (.of k₁)).geometricFiberPointOfFinitePoint z),
    ← Category.assoc ε.inv]
  change c (((ε.inv ≫ (C ↘ Spec (.of k₁)).geometricFiberPointOfFinitePoint z) ≫
    (C ↘ Spec (.of k₁)).geometricFiberProj)
      (IsLocalRing.closedPoint (AlgebraicClosure k₀))) = c z.1
  rw [Category.assoc, Scheme.Hom.comp_apply]
  have hpoint : ε.inv (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      IsLocalRing.closedPoint (AlgebraicClosure k₁) := Subsingleton.elim _ _
  rw [hpoint, Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base]

private theorem powEquiv_of_comp {K : Type*} [Field K]
    {M N : FrobeniusModule K} (e : ℕ) (E : M.carrier ≃ₗ[K] N.carrier)
    (h : E.toLinearMap ∘ₗ M.frobeniusEnd ^ e = N.frobeniusEnd ∘ₗ E.toLinearMap) :
    Nonempty ((M.powFrobenius e).Equiv N) := by
  refine ⟨FrobeniusModule.Equiv.ofComp (M := M.powFrobenius e) E ?_⟩
  rw [FrobeniusModule.powFrobenius_frobeniusEnd]
  exact h

private theorem id_intertwines {K : Type*} [Field K] (V : ModuleCat K)
    (f g : Module.End K V) (h : f = g) :
    (LinearEquiv.refl K V).toLinearMap ∘ₗ f =
      g ∘ₗ (LinearEquiv.refl K V).toLinearMap := by
  simpa only [LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id] using h

private theorem pow_stalk_equiv_stalkAt
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (F : WeilSheaf k l X) (x : X.finitePoints) (e n : ℕ)
    (hn : n = e * (X ↘ Spec (.of k)).degreeOver x.1)
    (hs : (X ↘ Spec (.of k)).geometricFiberPointOfFinitePoint x ≫
      ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ n).hom =
      (specGeometricFrobenius k ^ n).hom ≫
        (X ↘ Spec (.of k)).geometricFiberPointOfFinitePoint x) :
    Nonempty (((F.stalk x).powFrobenius e).Equiv
      (F.stalkAt ((X ↘ Spec (.of k)).geometricFiberPointOfFinitePoint x) n hs)) := by
  subst n
  let sx := (X ↘ Spec (.of k)).geometricFiberPointOfFinitePoint x
  let V := (WeilCoefficients.toModuleCat l).obj (F.stalkObj sx)
  have hsx := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (.of k)) x
  have h : @Eq (Module.End (PadicAlgCl l) V)
      ((F.stalk x).frobeniusEnd ^ e)
      (F.stalkAt sx (e * (X ↘ Spec (.of k)).degreeOver x.1) hs).frobeniusEnd :=
    @Eq.symm (Module.End (PadicAlgCl l) V) _ _
      (F.frobeniusEnd_stalkAt_mul sx
        (Nat.pos_of_ne_zero (Scheme.Hom.degreeOver_ne_zero _ x.2)) hsx e)
  exact powEquiv_of_comp (M := F.stalk x)
    (N := F.stalkAt sx (e * (X ↘ Spec (.of k)).degreeOver x.1) hs)
    e (LinearEquiv.refl (PadicAlgCl l) V) (id_intertwines V _ _ h)

private theorem nonempty_equiv_trans {K : Type*} [Field K]
    {M N P : FrobeniusModule K} (h : Nonempty (M.Equiv N))
    (h' : Nonempty (N.Equiv P)) : Nonempty (M.Equiv P) := by
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := h'
  exact ⟨e.trans e'⟩

private theorem nonempty_equiv_of_eq {K : Type*} [Field K]
    {M N : FrobeniusModule K} (h : M = N) : Nonempty (M.Equiv N) := by
  subst N
  exact ⟨FrobeniusModule.Equiv.refl M⟩

private theorem stalkAt_fixed_eq_stalk
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (F : WeilSheaf k l X) (x : X.finitePoints) :
    F.stalkAt ((X ↘ Spec (.of k)).geometricFiberPointOfFinitePoint x)
      ((X ↘ Spec (.of k)).degreeOver x.1)
      (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
        (X ↘ Spec (.of k)) x) = F.stalk x := by
  unfold stalk
  rfl

private theorem stalkAt_fixed_equiv_stalk
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (F : WeilSheaf k l X) (x : X.finitePoints) :
    Nonempty ((F.stalkAt ((X ↘ Spec (.of k)).geometricFiberPointOfFinitePoint x)
      ((X ↘ Spec (.of k)).degreeOver x.1)
      (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
        (X ↘ Spec (.of k)) x)).Equiv (F.stalk x)) :=
  nonempty_equiv_of_eq (stalkAt_fixed_eq_stalk F x)

private theorem stalkAt_equiv_stalk_of_eq
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (F : WeilSheaf k l X) (x : X.finitePoints)
    (s : Spec (.of (AlgebraicClosure k)) ⟶ (X ↘ Spec (.of k)).geometricFiber)
    (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k ^ m).hom ≫ s)
    (hpoint : s = (X ↘ Spec (.of k)).geometricFiberPointOfFinitePoint x)
    (hindex : m = (X ↘ Spec (.of k)).degreeOver x.1) :
    Nonempty ((F.stalkAt s m hs).Equiv (F.stalk x)) := by
  subst s
  subst m
  exact stalkAt_fixed_equiv_stalk F x

private theorem periodic_composite {B : Type*} [Category B] {P₀ P₁ U V : B}
    (ε : P₁ ≅ P₀) (θ : U ≅ V) (s : P₁ ⟶ V)
    (τ₀ : P₀ ⟶ P₀) (τ₁ : P₁ ⟶ P₁) (g₀ : U ⟶ U) (g₁ : V ⟶ V)
    (hj : g₁ ≫ θ.inv = θ.inv ≫ g₀)
    (hσ : ε.inv ≫ τ₁ = τ₀ ≫ ε.inv) (hs : s ≫ g₁ = τ₁ ≫ s) :
    (ε.inv ≫ s ≫ θ.inv) ≫ g₀ = τ₀ ≫ (ε.inv ≫ s ≫ θ.inv) := by
  rw [Category.assoc, Category.assoc, ← hj, ← Category.assoc s, hs]
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ s ≫ θ.inv) hσ

private theorem periodic_congr_index {B : Type*} [Category B] {P U : B}
    (s : P ⟶ U) (g : Aut U) (σ : Aut P) {a b : ℕ} (hab : a = b)
    (hs : s ≫ (g ^ a).hom = (σ ^ a).hom ≫ s) :
    s ≫ (g ^ b).hom = (σ ^ b).hom ≫ s := by
  subst b
  exact hs

private theorem mem_transport {T : Type*} (S : Set T) {a b : T}
    (hab : a = b) (hb : b ∈ S) : a ∈ S := by
  subst b
  exact hb

private theorem pow_stalk_equiv_of_image
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k ≠ l)] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (F : WeilSheaf k l X) (x : X.finitePoints) (e n : ℕ)
    (hn : n = e * (X ↘ Spec (.of k)).degreeOver x.1)
    (s : Spec (.of (AlgebraicClosure k)) ⟶ (X ↘ Spec (.of k)).geometricFiber)
    (hs : s ≫ ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ n).hom =
      (specGeometricFrobenius k ^ n).hom ≫ s)
    (hbase : (s ≫ (X ↘ Spec (.of k)).geometricFiberProj).base
      (IsLocalRing.closedPoint (AlgebraicClosure k)) = x.1) :
    Nonempty (((F.stalk x).powFrobenius e).Equiv (F.stalkAt s n hs)) := by
  let sx := (X ↘ Spec (.of k)).geometricFiberPointOfFinitePoint x
  have hsx := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (.of k)) x
  have hsx' : sx ≫ ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ n).hom =
      (specGeometricFrobenius k ^ n).hom ≫ sx :=
    periodic_congr_index sx (X ↘ Spec (.of k)).geometricGaloisFrobenius
      (specGeometricFrobenius k) hn.symm
      (comp_geometricGaloisFrobenius_pow_mul sx hsx e)
  have hsximage :=
    Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base
      (X ↘ Spec (.of k)) x
  have hfinite : (sx ≫ (X ↘ Spec (.of k)).geometricFiberProj).base
      (IsLocalRing.closedPoint (AlgebraicClosure k)) ∈ X.finitePoints :=
    mem_transport X.finitePoints hsximage x.2
  have hE₀ : Nonempty ((F.stalkAt sx n hsx').Equiv (F.stalkAt s n hs)) :=
    F.nonempty_equiv_stalkAt sx s (hsximage.trans hbase.symm) hfinite n hsx' hs
  have hpow : Nonempty (((F.stalk x).powFrobenius e).Equiv (F.stalkAt sx n hsx')) :=
    pow_stalk_equiv_stalkAt (k := k) (l := l) (X := X) F x e n hn hsx'
  exact nonempty_equiv_trans (K := PadicAlgCl l)
    (M := (F.stalk x).powFrobenius e) (N := F.stalkAt sx n hsx')
    (P := F.stalkAt s n hs) hpow hE₀

private theorem stalkPowerEquiv_of_carrierSquare
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X C : Scheme.{u}} [X.Over (Spec (.of k₀))]
    [C.Over (Spec (.of k₁))] {c : C ⟶ X}
    (r : ℕ)
    (θ : (X ↘ Spec (.of k₀)).geometricFiber ≅
      (C ↘ Spec (.of k₁)).geometricFiber)
    (hθ : θ.hom ≫ (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom =
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θ.hom)
    (ε : Spec (.of (AlgebraicClosure k₁)) ≅ Spec (.of (AlgebraicClosure k₀)))
    (hσbase : ε.inv ≫ (specGeometricFrobenius k₁).hom =
      (specGeometricFrobenius k₀ ^ r).hom ≫ ε.inv)
    (hproj : θ.inv ≫ (X ↘ Spec (.of k₀)).geometricFiberProj =
      (C ↘ Spec (.of k₁)).geometricFiberProj ≫ c)
    (F : WeilSheaf k₀ l X) (G : WeilSheaf k₁ l C)
    (α : (θ.inv)^*[WeilCoefficients.{u} l].obj F.obj.carrier.X ≅ G.obj.carrier.X)
    (hcarrier : ∀ (m : ℕ)
      (hj : ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom ≫ θ.inv =
        θ.inv ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (r * m)).hom),
      (upperStarComp (WeilCoefficients.{u} l)
        ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom
        θ.inv).hom.app F.obj.carrier.X ≫
        (((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom)^*[WeilCoefficients.{u} l].map
          α.hom ≫ G.frobeniusPowStr m =
      (upperStarCongr (WeilCoefficients.{u} l) hj).hom.app F.obj.carrier.X ≫
        (upperStarComp (WeilCoefficients.{u} l) θ.inv
          ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (r * m)).hom).hom.app F.obj.carrier.X ≫
          (θ.inv)^*[WeilCoefficients.{u} l].map
            (F.frobeniusPowStr (r * m)) ≫ α.hom)
    (z : C.finitePoints) (x : X.finitePoints) (e : ℕ) (hx : c z.1 = x.1)
    (hdegree : r * (C ↘ Spec (.of k₁)).degreeOver z.1 =
      e * (X ↘ Spec (.of k₀)).degreeOver x.1) :
    Nonempty (((F.stalk x).powFrobenius e).Equiv (G.stalk z)) := by
  let m := (C ↘ Spec (.of k₁)).degreeOver z.1
  let s₁ := (C ↘ Spec (.of k₁)).geometricFiberPointOfFinitePoint z
  let s₀ := ε.inv ≫ s₁ ≫ θ.inv
  have hθm : θ.hom ≫ ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom =
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (r * m)).hom ≫ θ.hom :=
    intertwines_powers θ (X ↘ Spec (.of k₀)).geometricGaloisFrobenius
      (C ↘ Spec (.of k₁)).geometricGaloisFrobenius r hθ m
  have hj : ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom ≫ θ.inv =
      θ.inv ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (r * m)).hom :=
    intertwines_inverse θ
      (((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (r * m)).hom)
      (((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom) hθm
  have hσ : ε.inv ≫ (specGeometricFrobenius k₁ ^ m).hom =
      (specGeometricFrobenius k₀ ^ (r * m)).hom ≫ ε.inv := by
    exact intertwines_powers ε.symm (specGeometricFrobenius k₀)
      (specGeometricFrobenius k₁) r hσbase m
  have hs₁ : s₁ ≫ ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₁ ^ m).hom ≫ s₁ :=
    Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow _ z
  have hs₀ : s₀ ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (r * m)).hom =
      (specGeometricFrobenius k₀ ^ (r * m)).hom ≫ s₀ :=
    periodic_composite ε θ s₁
      ((specGeometricFrobenius k₀ ^ (r * m)).hom) ((specGeometricFrobenius k₁ ^ m).hom)
      (((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (r * m)).hom)
      (((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom) hj hσ hs₁
  have ht : ε.hom ≫ s₀ = s₁ ≫ θ.inv := ε.hom_inv_id_assoc (s₁ ≫ θ.inv)
  have hε : (specGeometricFrobenius k₁ ^ m).hom ≫ ε.hom =
      ε.hom ≫ (specGeometricFrobenius k₀ ^ (r * m)).hom := by
    exact intertwines_inverse ε.symm
      ((specGeometricFrobenius k₀ ^ (r * m)).hom) ((specGeometricFrobenius k₁ ^ m).hom) hσ
  have hE : Nonempty ((F.stalkAt s₀ (r * m) hs₀).Equiv (G.stalkAt s₁ m hs₁)) :=
    stalkEquiv_of_transportSquare
      (k₀ := k₀) (k₁ := k₁) (l := l) (X := X) (Y := C) F G θ.inv (r * m) m hj α
    (hcarrier m hj)
    ε s₀ s₁ hs₀ hs₁ ht hε
  have hbase : (s₀ ≫ (X ↘ Spec (.of k₀)).geometricFiberProj).base
      (IsLocalRing.closedPoint (AlgebraicClosure k₀)) = x.1 :=
    (compatibleLift_image c θ ε hproj z).trans hx
  have hpow : Nonempty (((F.stalk x).powFrobenius e).Equiv (F.stalkAt s₀ (r * m) hs₀)) :=
    pow_stalk_equiv_of_image (k := k₀) (l := l) (X := X) F x e (r * m) hdegree s₀ hs₀ hbase
  have hfinal : Nonempty (((F.stalk x).powFrobenius e).Equiv
      (G.stalkAt s₁ m hs₁)) :=
    nonempty_equiv_trans (K := PadicAlgCl l)
      (M := (F.stalk x).powFrobenius e) (N := F.stalkAt s₀ (r * m) hs₀)
      (P := G.stalkAt s₁ m hs₁) hpow hE
  have hfixed : Nonempty ((G.stalkAt s₁ m hs₁).Equiv (G.stalk z)) :=
    stalkAt_equiv_stalk_of_eq (k := k₁) (l := l) (X := C) G z s₁ m hs₁ rfl rfl
  exact nonempty_equiv_trans (K := PadicAlgCl l)
    (M := (F.stalk x).powFrobenius e) (N := G.stalkAt s₁ m hs₁)
    (P := G.stalk z) hfinal hfixed


private theorem pointwisePowerTransport_of_carrierSquare
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X C : Scheme.{u}} [X.Over (Spec (.of k₀))]
    [C.Over (Spec (.of k₁))] {c : C ⟶ X}
    (r : ℕ) (hr : Nat.card k₁ = Nat.card k₀ ^ r)
    (θ : (X ↘ Spec (.of k₀)).geometricFiber ≅
      (C ↘ Spec (.of k₁)).geometricFiber)
    (hθ : θ.hom ≫ (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom =
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θ.hom)
    (ε : Spec (.of (AlgebraicClosure k₁)) ≅ Spec (.of (AlgebraicClosure k₀)))
    (hσbase : ε.inv ≫ (specGeometricFrobenius k₁).hom =
      (specGeometricFrobenius k₀ ^ r).hom ≫ ε.inv)
    (hproj : θ.inv ≫ (X ↘ Spec (.of k₀)).geometricFiberProj =
      (C ↘ Spec (.of k₁)).geometricFiberProj ≫ c)
    (R : WeilSheaf k₀ l X ⥤ WeilSheaf k₁ l C)
    (carrierIso : ∀ F : WeilSheaf k₀ l X,
      (θ.inv)^*[WeilCoefficients.{u} l].obj
        F.obj.carrier.X ≅ (R.obj F).obj.carrier.X)
    (hcarrier : ∀ (F : WeilSheaf k₀ l X) (m : ℕ)
      (hj : ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom ≫ θ.inv =
        θ.inv ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (r * m)).hom),
      (upperStarComp (WeilCoefficients.{u} l)
        ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom
        θ.inv).hom.app F.obj.carrier.X ≫
        (((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom)^*[WeilCoefficients.{u} l].map
          (carrierIso F).hom ≫ (R.obj F).frobeniusPowStr m =
      (upperStarCongr (WeilCoefficients.{u} l) hj).hom.app F.obj.carrier.X ≫
        (upperStarComp (WeilCoefficients.{u} l) θ.inv
          ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (r * m)).hom).hom.app F.obj.carrier.X ≫
          (θ.inv)^*[WeilCoefficients.{u} l].map
            (F.frobeniusPowStr (r * m)) ≫ (carrierIso F).hom) :
    HasPointwisePowerTransport (k₀ := k₀) (k₁ := k₁) (l := l) (X := X) (Y := C) R c := by
  intro z
  obtain ⟨x, e, hx, he, hq, hdegree⟩ := exists_pointDegree c r hr z
  refine ⟨x, e, hx, he, hq, ?_⟩
  intro F
  exact stalkPowerEquiv_of_carrierSquare
    (k₀ := k₀) (k₁ := k₁) (l := l) (X := X) (C := C) (c := c)
    r θ hθ ε hσbase hproj F (R.obj F) (carrierIso F) (hcarrier F)
    z x e hx hdegree

/-- The actual source transport across a cartesian constant-field square has
the residue-degree local return formula for every constructible sheaf.

Source: blueprint `thm-zl-real-mixed-by-curves`, paragraphs 1--3, and the local
iterated point transports of `def-weil-local-frobenius-trace`.
(blueprint: lem-zl-source-constant-field-restriction-stalk).

Proof: For a finite point z of C take its finite image x=c(z), and set
e=[kappa(z):kappa(x)]>0. Finite-field cardinalities give q_z=q_x^e and
r*degreeOver(z)=e*degreeOver(x). Let theta be the geometric-fiber isomorphism,
epsilon the spectrum isomorphism of algebraic closures, and s_1 the fixed lift
of z. Set s_0=epsilon.inv followed by s_1 and theta.inv. The Frobenius power
identities make s_0 periodic with return index r*degreeOver(z), and the projection
identity puts its image at x. Apply globalSectionsTransport to the canonical
carrier comparison along theta.inv. This map is invertible since epsilon and
the carrier comparison are isomorphisms. The structure-map square of
frobeniusPowStr_constantFieldRestriction and composition of global-sections
transports show that it intertwines the return maps. Finally change from s_0
to the fixed lift of x using nonempty_equiv_stalkAt, and use
frobeniusEnd_stalkAt_mul together with the degree identity to identify the old
return map with the e-th power. No lissity or semisimplicity is needed. -/
theorem hasPointwisePowerTransport_constantFieldRestrictionOfSquare
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    [Algebra k₀ k₁] [Algebra.IsAlgebraic k₀ k₁]
    {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X C : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [C.Over (Spec (CommRingCat.of k₁))] {c : C ⟶ X}
    (hc : IsPullback c (C ↘ Spec (CommRingCat.of k₁)) (X ↘ Spec (CommRingCat.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))))
    (r : ℕ) (hr : Nat.card k₁ = Nat.card k₀ ^ r) :
    HasPointwisePowerTransport (constantFieldRestrictionOfSquare (l := l) hc r hr) c := by
  let θ := Scheme.Hom.geometricFiberBaseChangeIso hc
  let hθ := Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius hc r hr
  let ε : Spec (.of (AlgebraicClosure k₁)) ≅ Spec (.of (AlgebraicClosure k₀)) :=
    (Scheme.Spec.mapIso (algebraicClosureAlgEquiv k₀ k₁).toRingEquiv.toCommRingCatIso.op).symm
  exact pointwisePowerTransport_of_carrierSquare
    (k₀ := k₀) (k₁ := k₁) (l := l) (X := X) (C := C) (c := c) r hr θ hθ ε
    (Scheme.Hom.spec_algebraicClosureAlgEquiv_comp_specGeometricFrobenius r hr)
    (Scheme.Hom.geometricFiberBaseChangeInv_comp_geometricFiberProj hc)
    (constantFieldRestrictionOfSquare (l := l) hc r hr)
    (constantFieldRestrictionCarrierIso
      (k₀ := k₀) (k₁ := k₁) (l := l) (X := X) (Y := C) θ r hθ)
    (fun F m hj ↦ frobeniusPowStr_constantFieldRestriction
      (k₀ := k₀) (k₁ := k₁) (l := l) (X := X) (Y := C) θ r hθ F m hj)

end AlgebraicGeometry.WeilSheaf
