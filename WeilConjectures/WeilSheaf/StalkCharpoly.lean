/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkFrobenius

/-!
# The characteristic polynomial of the local Frobenius
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {P P' Y Y' : Scheme.{u}}

lemma upperStarCompIso_eq {τ : P' ⟶ P} {t : P ⟶ Y} {t' : P' ⟶ Y'} {g : Y' ⟶ Y}
    (h : τ ≫ t = t' ≫ g) :
    upperStarCompIso A h =
      (upperStarComp A τ t).symm ≪≫ upperStarCongr A h ≪≫ upperStarComp A t' g :=
  rfl

lemma symm_trans_hom_app_eq {τ : P' ⟶ P} {t : P ⟶ Y} {t' : P' ⟶ Y'} {g : Y' ⟶ Y}
    (h : τ ≫ t = t' ≫ g) (F : Sheaf (Scheme.ProEt.topology Y) A) :
    ((upperStarComp A τ t).symm ≪≫ upperStarCongr A h ≪≫ upperStarComp A t' g).hom.app F =
      (upperStarComp A τ t).inv.app F ≫ (upperStarCongr A h ≪≫ upperStarComp A t' g).hom.app F :=
  rfl

lemma congr_trans_hom_app_eq {τ : P' ⟶ P} {t : P ⟶ Y} {t' : P' ⟶ Y'} {g : Y' ⟶ Y}
    (h : τ ≫ t = t' ≫ g) (F : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarCongr A h ≪≫ upperStarComp A t' g).hom.app F =
      (upperStarCongr A h).hom.app F ≫ (upperStarComp A t' g).hom.app F :=
  rfl

/-- The components of the isomorphism `upperStarCompIso` of a commutative square. -/
lemma upperStarCompIso_hom_app {τ : P' ⟶ P} {t : P ⟶ Y} {t' : P' ⟶ Y'} {g : Y' ⟶ Y}
    (h : τ ≫ t = t' ≫ g) (F : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarCompIso A h).hom.app F = (upperStarComp A τ t).inv.app F ≫
      (upperStarCongr A h).hom.app F ≫ (upperStarComp A t' g).hom.app F :=
  (congrArg (fun e ↦ e.hom.app F) (upperStarCompIso_eq A h)).trans <|
    (symm_trans_hom_app_eq A h F).trans
      (congrArg ((upperStarComp A τ t).inv.app F ≫ ·) (congr_trans_hom_app_eq A h F))

/-- The sections of the isomorphism `upperStarCongr` are an `eqToHom`. -/
lemma Γ_map_upperStarCongr_hom_app {Z W : Scheme.{u}} {g g' : Z ⟶ W} (h : g = g')
    (F : Sheaf (Scheme.ProEt.topology W) A) :
    (Sheaf.Γ _ A).map ((upperStarCongr A h).hom.app F) = eqToHom (by rw [h]) := by
  subst h
  simp [upperStarCongr]

/-- The transport along a square `e ≫ t = t' ≫ g` whose top side is an isomorphism `e`. -/
lemma globalSectionsTransport_eq_of_iso (e : P' ≅ P) {t : P ⟶ Y} {t' : P' ⟶ Y'} {g : Y' ⟶ Y}
    (h : e.hom ≫ t = t' ≫ g) {F : Sheaf (Scheme.ProEt.topology Y) A}
    {F' : Sheaf (Scheme.ProEt.topology Y') A} (ψ : (upperStar A g).obj F ⟶ F') :
    globalSectionsTransport A h ψ =
      (globalSectionsUpperStarIso A e).inv.app ((upperStar A t).obj F) ≫
        (Sheaf.Γ _ A).map ((upperStarCompIso A h).hom.app F ≫ (upperStar A t').map ψ) := by
  have h' := globalSectionsToUpperStar_app_comp_globalSectionsUpperStarIso A e ((upperStar A t).obj F)
  replace h' : (globalSectionsToUpperStar A e.hom).app ((upperStar A t).obj F) =
      (globalSectionsUpperStarIso A e).inv.app ((upperStar A t).obj F) :=
    (Iso.comp_hom_eq_id ((globalSectionsUpperStarIso A e).app _)).1 h'
  rw [globalSectionsTransport, h']

/-- The transport along a square `e ≫ t = t' ≫ g` with `e` an isomorphism and `ψ` an
isomorphism, written as a composite of isomorphisms. -/
lemma globalSectionsTransport_eq_hom (e : P' ≅ P) {t : P ⟶ Y} {t' : P' ⟶ Y'} {g : Y' ⟶ Y}
    (h : e.hom ≫ t = t' ≫ g) {F : Sheaf (Scheme.ProEt.topology Y) A}
    {F' : Sheaf (Scheme.ProEt.topology Y') A} (ψ : (upperStar A g).obj F ≅ F') :
    (((Sheaf.Γ _ A).mapIso ((upperStarComp A e.hom t).app F) ≪≫
        (globalSectionsUpperStarIso A e).app ((upperStar A t).obj F)).symm ≪≫
      eqToIso (congrArg (fun u ↦ (Sheaf.Γ _ A).obj ((upperStar A u).obj F)) h) ≪≫
      (Sheaf.Γ _ A).mapIso ((upperStarComp A t' g).app F ≪≫ (upperStar A t').mapIso ψ)).hom =
      globalSectionsTransport A h ψ.hom := by
  rw [globalSectionsTransport_eq_of_iso, upperStarCompIso_hom_app]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Iso.app_hom, Iso.app_inv, eqToIso.hom, Functor.map_comp, Category.assoc,
    Γ_map_upperStarCongr_hom_app]

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

variable (F : WeilSheaf k₀ l X)
  (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)

/-- The Frobenius of the stalk at `s` relative to `𝔽_{qᵐ}` is the transport of global sections
along the square `σᵐ ≫ s = s ≫ Frᵐ` and the iterated Weil structure. -/
lemma stalkAt_frobenius_hom_eq_globalSectionsTransport (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ s) :
    ((F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫ eqToIso (congrArg F.stalkObj hs.symm) ≪≫
        F.stalkObjFrobeniusPowIso m s).hom =
      ProEtale.globalSectionsTransport _ hs.symm (F.frobeniusPowStr m) := by
  exact ProEtale.globalSectionsTransport_eq_hom (WeilCoefficients.{u} l)
    (specGeometricFrobenius k₀ ^ m) hs.symm
    ((ProEtale.upperStarIsoLowerStarInv _ _).app F.obj.carrier.X ≪≫
      (ProEtale.AdicSheaf.forget _).mapIso (F.frobeniusPowIso m))

end AlgebraicGeometry.WeilSheaf

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

variable (F : WeilSheaf k₀ l X)
  (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)

/-- The transports along the iterated Weil structures compose: for `b ≥ 1`, transporting along
`φ_a` and then along `φ_b` is transporting along `φ_{a+b}`. -/
lemma globalSectionsTransport_frobeniusPowStr_comp {t t' t'' : Spec (.of (AlgebraicClosure k₀)) ⟶
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} {τ τ' τ'' : Spec (.of (AlgebraicClosure k₀)) ⟶
      Spec (.of (AlgebraicClosure k₀))} (a b : ℕ) (hb : 1 ≤ b)
    (ha : τ ≫ t = t' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).hom)
    (hb' : τ' ≫ t' = t'' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ b).hom)
    (hτ : τ' ≫ τ = τ'')
    (hab : τ'' ≫ t = t'' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (a + b)).hom) :
    ProEtale.globalSectionsTransport _ ha (F.frobeniusPowStr a) ≫
        ProEtale.globalSectionsTransport _ hb' (F.frobeniusPowStr b) =
      ProEtale.globalSectionsTransport _ hab (F.frobeniusPowStr (a + b)) := by
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

lemma globalSectionsTransport_frobeniusPowStr_congr {t t' : Spec (.of (AlgebraicClosure k₀)) ⟶
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} {τ τ' : Spec (.of (AlgebraicClosure k₀)) ⟶
      Spec (.of (AlgebraicClosure k₀))} {n n' : ℕ} (hn : n = n') (hτ : τ = τ')
    (h : τ ≫ t = t' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).hom)
    (h' : τ' ≫ t = t' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n').hom) :
    ProEtale.globalSectionsTransport _ h (F.frobeniusPowStr n) =
      ProEtale.globalSectionsTransport _ h' (F.frobeniusPowStr n') := by
  subst hn hτ
  rfl

instance isIso_frobeniusPowStr (m : ℕ) : IsIso (F.frobeniusPowStr m) := by
  unfold frobeniusPowStr
  exact inferInstanceAs (IsIso (((ProEtale.upperStarIsoLowerStarInv _ _).app _ ≪≫
    (ProEtale.AdicSheaf.forget _).mapIso (F.frobeniusPowIso m)).hom))

/-- The Frobenius transports at two geometric points `s` and `s'` related by a square
`g ≫ s = s' ≫ Frʲ`, with `g` commuting with `σᵐ`, are intertwined by the transport along that
square. -/
lemma globalSectionsTransport_frobeniusPowStr_comm {s s' : Spec (.of (AlgebraicClosure k₀)) ⟶
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} {g σ : Spec (.of (AlgebraicClosure k₀)) ⟶
      Spec (.of (AlgebraicClosure k₀))} (j m : ℕ) (hj : 1 ≤ j) (hm : 1 ≤ m)
    (hg : g ≫ s = s' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ j).hom)
    (hs : σ ≫ s = s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom)
    (hs' : σ ≫ s' = s' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom)
    (hcomm : g ≫ σ = σ ≫ g) :
    ProEtale.globalSectionsTransport _ hs (F.frobeniusPowStr m) ≫
        ProEtale.globalSectionsTransport _ hg (F.frobeniusPowStr j) =
      ProEtale.globalSectionsTransport _ hg (F.frobeniusPowStr j) ≫
        ProEtale.globalSectionsTransport _ hs' (F.frobeniusPowStr m) := by
  have h₁ : (g ≫ σ) ≫ s = s' ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + j)).hom := by
    rw [Category.assoc, hs, ← Category.assoc, hg, Category.assoc,
      CategoryTheory.Aut.pow_hom_comp_pow_hom]
  have h₂ : (σ ≫ g) ≫ s = s' ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (j + m)).hom := by
    rw [Category.assoc, hg, ← Category.assoc, hs', Category.assoc,
      CategoryTheory.Aut.pow_hom_comp_pow_hom]
  rw [globalSectionsTransport_frobeniusPowStr_comp F m j hj hs hg rfl h₁,
    globalSectionsTransport_frobeniusPowStr_comp F j m hm hg hs' rfl h₂]
  exact globalSectionsTransport_frobeniusPowStr_congr F (Nat.add_comm m j) hcomm h₁ h₂

/-- The transport along a square `g ≫ s = s' ≫ Frʲ` with `g` an isomorphism is an
isomorphism. -/
lemma isIso_globalSectionsTransport_frobeniusPowStr {s s' : Spec (.of (AlgebraicClosure k₀)) ⟶
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} {g : Spec (.of (AlgebraicClosure k₀)) ≅
      Spec (.of (AlgebraicClosure k₀))} (j : ℕ)
    (hg : g.hom ≫ s = s' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ j).hom) :
    IsIso (ProEtale.globalSectionsTransport _ hg (F.frobeniusPowStr j)) := by
  rw [ProEtale.globalSectionsTransport_eq_of_iso _ g hg]
  infer_instance

end AlgebraicGeometry.WeilSheaf
