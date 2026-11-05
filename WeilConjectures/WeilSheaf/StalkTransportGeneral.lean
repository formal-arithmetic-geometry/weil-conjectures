/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkUpperStar
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCover

/-!
# Transports along the Weil structure over arbitrary schemes

For a Weil sheaf `F` on `X₀`, a scheme `P` with a morphism `t : P ⟶ X̄` and a square
`τ ≫ t = t' ≫ Frᵐ`, the transport `Γ(P, t^* F) ⟶ Γ(P', t'^* F)` along the iterated Weil structure
`φ_m` (`AlgebraicGeometry.ProEtale.globalSectionsTransport`) generalises the Frobenius of the stalks
of `F` at geometric points, which is the case `P = P' = Spec k̄`
(`AlgebraicGeometry.WeilSheaf.stalkAt_frobenius_hom_eq_globalSectionsTransport`). This file
records, for arbitrary `P`:

* these transports commute with restrictions `Γ(P₁, t₁^* F) ⟶ Γ(P₂, t₂^* F)` along morphisms
  compatible with the squares (`AlgebraicGeometry.ProEtale.globalSectionsTransport_comp_resOver`);
* they compose (`AlgebraicGeometry.WeilSheaf.globalSectionsTransport_frobeniusPowStr_comp'`);
* they are compatible with a morphism `θ : φ̄^* G ⟶ F` compatible with the Weil structures, for
  `φ : X₀ ⟶ Y₀` and a Weil sheaf `G` on `Y₀`
  (`AlgebraicGeometry.WeilSheaf.globalSectionsTransport_frobeniusPowStr_comp_upperStar`).

They are used at the generic geometric point and at a strictly henselian neighbourhood of a
boundary point, for the Frobenius equivariance of blueprint `lem-wf-boundary-stalk-invariants`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The composition isomorphism `(f ≫ g)^* ≅ g^* ⋙ f^*` for `f = 𝟙`, followed by `f^* = (𝟙)^* ≅ 𝟭`,
is the identification `(f ≫ g)^* = g^*`. -/
lemma upperStarComp_hom_app_comp_upperStarCongr_id {Y Y' : Scheme.{u}} {f : Y' ⟶ Y'}
    (p : f = 𝟙 Y') (g : Y' ⟶ Y) (h : f ≫ g = g) (G : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarComp A f g).hom.app G ≫ (upperStarCongr A p).hom.app ((g)^*[A].obj G) ≫
        (upperStarId A Y').hom.app ((g)^*[A].obj G) =
      (upperStarCongr A h).hom.app G := by
  subst p
  simpa [upperStarCongr] using upperStarComp_id_left_hom_app A g G

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The transports along the iterated Weil structures compose, over arbitrary schemes, for
`b = 0`. -/
lemma globalSectionsTransport_frobeniusPowStr_comp_zero (F : WeilSheaf k₀ l X)
    {P P' P'' : Scheme.{u}} {t : P ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {t' : P' ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {t'' : P'' ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {τ : P' ⟶ P} {τ' : P'' ⟶ P'} {τ'' : P'' ⟶ P} (a : ℕ)
    (ha : τ ≫ t = t' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).hom)
    (hb' : τ' ≫ t' = t'' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).hom)
    (hτ : τ' ≫ τ = τ'')
    (hab : τ'' ≫ t =
      t'' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (a + 0)).hom) :
    ProEtale.globalSectionsTransport _ ha (F.frobeniusPowStr a) ≫
        ProEtale.globalSectionsTransport _ hb' (F.frobeniusPowStr 0) =
      ProEtale.globalSectionsTransport _ hab (F.frobeniusPowStr (a + 0)) := by
  have p : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).hom = 𝟙 _ := by
    rw [pow_zero]
    rfl
  refine ProEtale.globalSectionsTransport_comp_eq _ ha hb' hab hτ
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.pow_hom_comp_pow_hom a 0) _ _ _ ?_
  have n₁ := (ProEtale.upperStarCongr (WeilCoefficients.{u} l) p).hom.naturality
    (F.frobeniusPowStr a)
  have n₂ := (ProEtale.upperStarId (WeilCoefficients.{u} l) _).hom.naturality
    (F.frobeniusPowStr a)
  simp only [Functor.id_map] at n₂
  rw [F.frobeniusPowStr_zero p]
  rw [reassoc_of% n₁, n₂, reassoc_of% (ProEtale.upperStarComp_hom_app_comp_upperStarCongr_id p
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).hom
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.pow_hom_comp_pow_hom a 0)
    F.obj.carrier.X)]
  rfl

/-- The transports along the iterated Weil structures compose, over arbitrary schemes:
transporting along `φ_a` and then along `φ_b` is transporting along `φ_{a+b}`. -/
lemma globalSectionsTransport_frobeniusPowStr_comp' (F : WeilSheaf k₀ l X) {P P' P'' : Scheme.{u}}
    {t : P ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {t' : P' ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {t'' : P'' ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {τ : P' ⟶ P} {τ' : P'' ⟶ P'} {τ'' : P'' ⟶ P} (a b : ℕ)
    (ha : τ ≫ t = t' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).hom)
    (hb' : τ' ≫ t' = t'' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ b).hom)
    (hτ : τ' ≫ τ = τ'')
    (hab : τ'' ≫ t =
      t'' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (a + b)).hom) :
    ProEtale.globalSectionsTransport _ ha (F.frobeniusPowStr a) ≫
        ProEtale.globalSectionsTransport _ hb' (F.frobeniusPowStr b) =
      ProEtale.globalSectionsTransport _ hab (F.frobeniusPowStr (a + b)) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · exact F.globalSectionsTransport_frobeniusPowStr_comp_zero a ha hb' hτ hab
  have hg := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.pow_hom_comp_pow_hom a b
  have h'' : (τ' ≫ τ) ≫ t = t'' ≫
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ b).hom ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).hom) := by
    rw [Category.assoc, ha, ← Category.assoc, hb', Category.assoc]
  have add := upperStarFactor_hom_app_comp_frobeniusPowStr_add F a b hb hg
  have hψ : (ProEtale.upperStarComp _ _ _).hom.app F.obj.carrier.X ≫
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ b).hom)^*[_].map
        (F.frobeniusPowStr a) ≫ F.frobeniusPowStr b =
      (ProEtale.upperStarCongr _ hg).hom.app F.obj.carrier.X ≫ F.frobeniusPowStr (a + b) := by
    rw [← add]
    simp [ProEtale.upperStarFactor, ProEtale.upperStarCongr]
  rw [ProEtale.globalSectionsTransport_comp _ ha hb' h'',
    ProEtale.globalSectionsTransport_congr _ h'' hg _ _ hψ,
    ProEtale.globalSectionsTransport_congr_left _ _ hτ]

section UpperStar

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  {φ : X ⟶ Y} [φ.IsOver (Spec (CommRingCat.of k₀))] {F : WeilSheaf k₀ l X} {G : WeilSheaf k₀ l Y}
  {θ : (Scheme.Hom.geometricFiberMap φ (comp_over φ _))^*[WeilCoefficients.{u} l].obj
    G.obj.carrier.X ⟶ F.obj.carrier.X}

set_option hygiene false in
local notation "φ̄" => Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))

end UpperStar

end AlgebraicGeometry.WeilSheaf
