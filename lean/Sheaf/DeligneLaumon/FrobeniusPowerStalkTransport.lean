/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.DeligneLaumon.FrobeniusPowerCommutation
public import Sheaf.DeligneLaumon.FrobeniusPowerDeckPoints
public import WeilConjectures.WeilSheaf.Stalk
import WeilConjectures.WeilSheaf.StalkUpperStar
import Sheaf.DeligneLaumon.FrobeniusPowerTranslateStructure

/-! # Stalk transport for an equivariant power-translate

Source: `sk-i-dl-general-real`, geometric orbit argument, stalk transport.
(blueprint: lem-zl-frobenius-power-stalk-transport).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Endofunctor
namespace AlgebraicGeometry.WeilSheaf
open ProEtale


private theorem commute_power_hom {D : Type*} [Category D] {Y : D}
    (f : Aut Y) (b : Y ⟶ Y) (hc : f.hom ≫ b = b ≫ f.hom) (m : ℕ) :
    (f ^ m).hom ≫ b = b ≫ (f ^ m).hom := by
  induction m with
  | zero => change 𝟙 Y ≫ b = b ≫ 𝟙 Y; simp
  | succ m ih =>
    rw [← f.pow_hom_comp_pow_hom m 1, pow_one, Category.assoc, ih,
      ← Category.assoc, hc, Category.assoc]

private theorem conjugate_power_commutes {D : Type*} [Category D] {Y Z : D}
    (θ : Y ≅ Z) (g : Aut Y) (f : Aut Z) (r j : ℕ)
    (hθ : θ.hom ≫ f.hom = (g ^ r).hom ≫ θ.hom) :
    f.hom ≫ (θ.symm ≪≫ (g ^ j) ≪≫ θ).hom =
      (θ.symm ≪≫ (g ^ j) ≪≫ θ).hom ≫ f.hom := by
  rw [← cancel_epi θ.hom, ← Category.assoc θ.hom f.hom, hθ]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [hθ, ← Category.assoc, ← Category.assoc, g.pow_hom_comp_pow_hom,
    g.pow_hom_comp_pow_hom, Nat.add_comm r j]

section GeneralTransport

variable {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
  [Fact (ringChar k ≠ l)] {Y : Scheme.{u}} [Y.Over (Spec (.of k))]
  (A B : WeilSheaf k l Y)
  (b : (Y ↘ Spec (.of k)).geometricFiber ⟶ (Y ↘ Spec (.of k)).geometricFiber)
  (hc : (Y ↘ Spec (.of k)).geometricGaloisFrobenius.hom ≫ b =
    b ≫ (Y ↘ Spec (.of k)).geometricGaloisFrobenius.hom)
  (α : (b)^*[WeilCoefficients.{u} l].obj A.obj.carrier.X ≅ B.obj.carrier.X)

include hc α

-- The structure maps in this hypothesis come from proof-only imports.
-- Bind it on the private helpers, rather than as a public section variable.
private theorem translate_transport_one_comm
    (hα : (upperStarComp (WeilCoefficients.{u} l)
      (Y ↘ Spec (.of k)).geometricGaloisFrobenius.hom b).hom.app A.obj.carrier.X ≫
      ((Y ↘ Spec (.of k)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l].map
        α.hom ≫ WeilSheaf.frobeniusStr B =
    (upperStarCongr (WeilCoefficients.{u} l) hc).hom.app A.obj.carrier.X ≫
      (upperStarComp (WeilCoefficients.{u} l) b
        (Y ↘ Spec (.of k)).geometricGaloisFrobenius.hom).hom.app A.obj.carrier.X ≫
        (b)^*[WeilCoefficients.{u} l].map (WeilSheaf.frobeniusStr A) ≫ α.hom)
    {t t' : Spec (.of (AlgebraicClosure k)) ⟶ (Y ↘ Spec (.of k)).geometricFiber}
    {τ : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of (AlgebraicClosure k))}
    (hX : τ ≫ t = t' ≫ ((Y ↘ Spec (.of k)).geometricGaloisFrobenius ^ 1).hom)
    (hY : τ ≫ (t ≫ b) = (t' ≫ b) ≫
      ((Y ↘ Spec (.of k)).geometricGaloisFrobenius ^ 1).hom) :
    globalSectionsTransport _ hY (A.frobeniusPowStr 1) ≫
        globalSectionsTransport _ (τ := (Iso.refl _).hom)
          (Category.id_comp (t' ≫ b)) α.hom =
      globalSectionsTransport _ (τ := (Iso.refl _).hom)
        (Category.id_comp (t ≫ b)) α.hom ≫
        globalSectionsTransport _ hX (B.frobeniusPowStr 1) := by
  have p := congrArg Iso.hom (pow_one (Y ↘ Spec (.of k)).geometricGaloisFrobenius)
  rw [globalSectionsTransport_congr _ hX p _ _ (B.frobeniusPowStr_one p),
    globalSectionsTransport_congr _ hY p _ _ (A.frobeniusPowStr_one p)]
  exact globalSectionsTransport_comm_of_upperStar _ b _ _ hc
    A.frobeniusStr B.frobeniusStr α.hom hα _ _

private theorem translate_transport_comm
    (hα : (upperStarComp (WeilCoefficients.{u} l)
      (Y ↘ Spec (.of k)).geometricGaloisFrobenius.hom b).hom.app A.obj.carrier.X ≫
      ((Y ↘ Spec (.of k)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l].map
        α.hom ≫ WeilSheaf.frobeniusStr B =
    (upperStarCongr (WeilCoefficients.{u} l) hc).hom.app A.obj.carrier.X ≫
      (upperStarComp (WeilCoefficients.{u} l) b
        (Y ↘ Spec (.of k)).geometricGaloisFrobenius.hom).hom.app A.obj.carrier.X ≫
        (b)^*[WeilCoefficients.{u} l].map (WeilSheaf.frobeniusStr A) ≫ α.hom)
    (m : ℕ) (hm : 1 ≤ m)
    {t t' : Spec (.of (AlgebraicClosure k)) ⟶ (Y ↘ Spec (.of k)).geometricFiber}
    {τ : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of (AlgebraicClosure k))}
    (hX : τ ≫ t = t' ≫ ((Y ↘ Spec (.of k)).geometricGaloisFrobenius ^ m).hom)
    (hY : τ ≫ (t ≫ b) = (t' ≫ b) ≫
      ((Y ↘ Spec (.of k)).geometricGaloisFrobenius ^ m).hom) :
    globalSectionsTransport _ hY (A.frobeniusPowStr m) ≫
        globalSectionsTransport _ (τ := (Iso.refl _).hom)
          (Category.id_comp (t' ≫ b)) α.hom =
      globalSectionsTransport _ (τ := (Iso.refl _).hom)
        (Category.id_comp (t ≫ b)) α.hom ≫
        globalSectionsTransport _ hX (B.frobeniusPowStr m) := by
  induction m, hm using Nat.le_induction generalizing t t' τ with
  | base => exact translate_transport_one_comm A B b hc α hα hX hY
  | succ m hm ih =>
    let f := (Y ↘ Spec (.of k)).geometricGaloisFrobenius
    have pc := commute_power_hom f b hc m
    have e₁ := f.pow_hom_comp_pow_hom m 1
    have haX : (Iso.refl _).hom ≫ t = (t ≫ (f ^ m).inv) ≫ (f ^ m).hom := by simp
    have hbX : τ ≫ (t ≫ (f ^ m).inv) = t' ≫ (f ^ 1).hom := by
      rw [← cancel_mono (f ^ m).hom, Category.assoc, Category.assoc, Iso.inv_hom_id,
        Category.comp_id, hX, Category.assoc, e₁]
    have haY : (Iso.refl _).hom ≫ (t ≫ b) =
        ((t ≫ (f ^ m).inv) ≫ b) ≫ (f ^ m).hom := by
      rw [Category.assoc, ← pc]
      simp
    have hbY : τ ≫ ((t ≫ (f ^ m).inv) ≫ b) = (t' ≫ b) ≫ (f ^ 1).hom := by
      rw [Category.assoc t', ← commute_power_hom f b hc 1,
        ← Category.assoc t', ← hbX]
      simp
    have hτ : τ ≫ (Iso.refl _).hom = τ := Category.comp_id τ
    rw [← A.globalSectionsTransport_frobeniusPowStr_comp m 1 le_rfl haY hbY hτ hY,
      ← B.globalSectionsTransport_frobeniusPowStr_comp m 1 le_rfl haX hbX hτ hX,
      Category.assoc, translate_transport_one_comm A B b hc α hα hbX hbY,
      ← Category.assoc, ih haX haY, Category.assoc]

private theorem stalk_equiv_of_translate_square
    (hα : (upperStarComp (WeilCoefficients.{u} l)
      (Y ↘ Spec (.of k)).geometricGaloisFrobenius.hom b).hom.app A.obj.carrier.X ≫
      ((Y ↘ Spec (.of k)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l].map
        α.hom ≫ WeilSheaf.frobeniusStr B =
    (upperStarCongr (WeilCoefficients.{u} l) hc).hom.app A.obj.carrier.X ≫
      (upperStarComp (WeilCoefficients.{u} l) b
        (Y ↘ Spec (.of k)).geometricGaloisFrobenius.hom).hom.app A.obj.carrier.X ≫
        (b)^*[WeilCoefficients.{u} l].map (WeilSheaf.frobeniusStr A) ≫ α.hom)
    (s : Spec (.of (AlgebraicClosure k)) ⟶ (Y ↘ Spec (.of k)).geometricFiber)
    (m : ℕ)
    (hs : s ≫ ((Y ↘ Spec (.of k)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k ^ m).hom ≫ s)
    (hs' : (s ≫ b) ≫ ((Y ↘ Spec (.of k)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k ^ m).hom ≫ (s ≫ b)) :
    Nonempty ((B.stalkAt s m hs).Equiv (A.stalkAt (s ≫ b) m hs')) := by
  let T := globalSectionsTransport (WeilCoefficients.{u} l)
    (τ := (Iso.refl _).hom) (Category.id_comp (s ≫ b)) α.hom
  have : IsIso T := by
    dsimp only [T]
    rw [globalSectionsTransport_eq_of_iso _ (Iso.refl _)
      (Category.id_comp (s ≫ b))]
    infer_instance
  let E := WeilCoefficients.linearEquivOfIso (asIso T)
  have hE : (A.stalkAt (s ≫ b) m hs').Equiv (B.stalkAt s m hs) := by
    refine FrobeniusModule.Equiv.ofComp E ?_
    change ((WeilCoefficients.toModuleCat l).map T).hom ∘ₗ _ =
      _ ∘ₗ ((WeilCoefficients.toModuleCat l).map T).hom
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [frobeniusEnd_stalkAt_zero, frobeniusEnd_stalkAt_zero]
      rfl
    · have h := translate_transport_comm A B b hc α hα m hm hs.symm hs'.symm
      rw [frobeniusEnd_stalkAt, frobeniusEnd_stalkAt]
      simpa only [Functor.map_comp, ModuleCat.hom_comp] using
        congrArg (fun f ↦ ((WeilCoefficients.toModuleCat l).map f).hom) h
  exact ⟨hE.symm⟩

end GeneralTransport

/-- An equivariant isomorphism from a translated power-return object gives
an equivalence of local Frobenius modules at a supplied geometric point and its actual translate.
Source: step 3 of `lem-zl-geometric-power-orbit-stalk`, geometric orbit argument
in `sk-i-dl-general-real`.
(blueprint: lem-zl-frobenius-power-stalk-transport).

Proof: Write beta for the conjugated j-th geometric Frobenius on the geometric
fibre of C. Pullback composition through the geometric-fibre comparison carries
e to an isomorphism E : beta^* A -> B of underlying sheaves. The definition of
the commutor compares both orders of the j-th and r-th pullbacks with the same
iterate. Consequently he says that E intertwines the single C-return: pulling
E back by Fr_C and then applying the return of B equals applying the return of
A pulled back by beta and then E, with the pullback-composition comparison
inserted. Induct on m to obtain the same equation for m successive returns;
the induction step composes the single-return square with its Fr_C pullback.
Pull E back to s and take global sections. This gives an invertible coefficient
map u from the fibre of A at s;beta to the fibre of B at s. In the definition of
stalkAt, Frobenius is the inverse scalar-reparametrization comparison, followed
by the point-square comparison, followed by the iterated return. Naturality of
pullback and global sections identifies the first two factors using hs and hs',
which have the same scalar map. The iterated-return equation supplies the third
factor. Thus u F_A = F_B u. Its inverse satisfies u^-1 F_B = F_A u^-1 and is the
required equivalence. No embeddings into an ambient sheaf or existence assertion
about finite points is involved. -/
theorem nonempty_stalk_equiv_of_equivariant_power_translate
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    {k₁ : Type u} [Field k₁] [Finite k₁] [Algebra k₀ k₁]
    [Algebra.IsAlgebraic k₀ k₁] [Fact (ringChar k₁ ≠ l)]
    {C : Scheme.{u}} [C.Over (Spec (CommRingCat.of k₁))] {c : C ⟶ X}
    (hc : IsPullback c (C ↘ Spec (CommRingCat.of k₁)) (X ↘ Spec (CommRingCat.of k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁))))
    (r : ℕ) (hr : Nat.card k₁ = Nat.card k₀ ^ r)
    (P Q : IsoAlgebra (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r))
    (j : ℕ)
    (e : (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X j).obj P.carrier ≅ Q.carrier)
    (he : (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r).map e.hom ≫ Q.str.hom =
      (ProEtaleWeilSheaf.frobeniusPowerCommIso j r).hom.app P.carrier ≫
        (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X j).map P.str.hom ≫ e.hom)
    (A B : WeilSheaf k₁ l C)
    (hA : A.obj = (IsoAlgebra.mapOfNatIso (ProEtaleWeilSheaf.transportCommIso
      (Scheme.Hom.geometricFiberBaseChangeIso hc) r
      (Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius
        hc r hr))).obj P)
    (hB : B.obj = (IsoAlgebra.mapOfNatIso (ProEtaleWeilSheaf.transportCommIso
      (Scheme.Hom.geometricFiberBaseChangeIso hc) r
      (Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius
        hc r hr))).obj Q)
    (s : Spec (.of (AlgebraicClosure k₁)) ⟶ (C ↘ Spec (.of k₁)).geometricFiber)
    (m : ℕ)
    (hs : s ≫ ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₁ ^ m).hom ≫ s)
    (hs' : Scheme.Hom.frobeniusPowerTranslatePoint hc j s ≫
        ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₁ ^ m).hom ≫
        Scheme.Hom.frobeniusPowerTranslatePoint hc j s) :
    Nonempty ((B.stalkAt s m hs).Equiv
      (A.stalkAt (Scheme.Hom.frobeniusPowerTranslatePoint hc j s) m hs')) := by
  let θ := Scheme.Hom.geometricFiberBaseChangeIso hc
  have hθ := Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius
    hc r hr
  have hcomm : (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom ≫
      (frobeniusPowerTranslateAut θ j).hom =
    (frobeniusPowerTranslateAut θ j).hom ≫
      (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom :=
    conjugate_power_commutes θ _ _ r j hθ
  have hα := frobeniusStr_powerTranslate θ r hθ P Q j e he A B hA hB hcomm
  have ht : Scheme.Hom.frobeniusPowerTranslatePoint hc j s =
      s ≫ (frobeniusPowerTranslateAut θ j).hom := by
    simp only [Scheme.Hom.frobeniusPowerTranslatePoint, frobeniusPowerTranslateAut,
      Iso.trans_hom, Iso.symm_hom, θ]
  have hs'' : (s ≫ (frobeniusPowerTranslateAut θ j).hom) ≫
      ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ m).hom =
    (specGeometricFrobenius k₁ ^ m).hom ≫
      (s ≫ (frobeniusPowerTranslateAut θ j).hom) := by
    simpa only [ht] using hs'
  simpa only [ht] using stalk_equiv_of_translate_square A B _ hcomm
    (frobeniusPowerTranslateSheafIso θ r hθ P Q j e A B hA hB) hα s m hs hs''

end AlgebraicGeometry.WeilSheaf
