/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import Sheaf.DeligneLaumon.PoweredGeometricPullback
public import WeilConjectures.WeilSheaf.Stalk
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Exact
import WeilConjectures.WeilSheaf.StalkCharpoly
import WeilConjectures.Evaluation
import Sheaf.DeligneLaumon.PoweredGeometricPullbackIterate
import WeilConjectures.WeilSheaf.BaseChangeField.Geometric

/-! # Frobenius-module transport under a powered geometric pullback -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale
open ProEtale

/-- An intertwining map also intertwines every power. -/
private theorem poweredPullback_comm_pow {A B : Scheme.{u}} (f : Aut A) (g : Aut B)
    (v : A ⟶ B) (h : f.hom ≫ v = v ≫ g.hom) (m : ℕ) :
    (f ^ m).hom ≫ v = v ≫ (g ^ m).hom := by
  induction m with
  | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
  | succ m ih =>
    rw [pow_succ, pow_succ, Aut.Aut_mul_def, Aut.Aut_mul_def, Iso.trans_hom,
      Iso.trans_hom, Category.assoc, ih, ← Category.assoc, h, Category.assoc]

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

/-- At any closed point, the explicitly constructed powered pullback has the original
local Frobenius raised to the residue extension degree. This is a uniform stalk assertion
for arbitrary finite-type schemes; it does not assert curve or diagram descent.

Source: blueprint `thm-zl-real-mixed-by-curves.proof.md`, paragraphs 1--3
(blueprint: lem-zl-clopen-return-stalk).

Proof: The structure square gives an embedding of residue fields at s and x=c(s).
They are finite fields. Its degree e is positive, and the cardinality tower gives qs=qx^e.
Choose the geometric lifts used by the two source stalks. Through tau and u they are two
lifts of x, related by a power of Frobenius, since embeddings of its finite residue field
form one Frobenius orbit. Pullback identifies the underlying fibres. Iterate the normalized
point-transport square around the orbit of s. Put ds=[kappa(s):k1] and dx=[kappa(x):k0].
The cardinality identity says r*ds=e*dx. One circuit on C therefore applies r*ds source
Weil maps, while one circuit at x applies dx. Write Ti for the successive normalized
source point transports. Their ordered product over r*ds steps is the product of e
successive dx-step circuits. The commutation hu identifies each pulled-back step with
its source block of r steps; functoriality identifies every adjacent endpoint, so the
intermediate fibre identifications cancel. Shifting the initial lift to the canonical
lift of x by its partial-orbit transport gives an isomorphism B with
B*F(P(G),s)=F(G,x)^e*B. This gives an actual Frobenius-module equivalence.
This uses no semisimplicity, rank or lissity
assumption, and works for the zero sheaf and when several closed points have the same image.
The construction of e uses the residue-field embedding only, so works for every sheaf. -/
theorem poweredGeometricPullback_stalkEquiv
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X C : Scheme.{u}} [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
    (r : ℕ) (hcard : Nat.card k₁ = Nat.card k₀ ^ r)
    (τ : AlgebraicClosure k₀ ≃+* AlgebraicClosure k₁)
    (c : C ⟶ X)
    (u : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    (hup : u ≫ (X ↘ Spec (.of k₀)).geometricFiberProj =
      (C ↘ Spec (.of k₁)).geometricFiberProj ≫ c)
    (hu : (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom ≫ u =
      u ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom)
    (s : C.finitePoints) :
    ∃ (x : X.finitePoints) (e : ℕ), c s.1 = x.1 ∧ 0 < e ∧
      (C ↘ Spec (.of k₁)).residueCard s.1 =
        (X ↘ Spec (.of k₀)).residueCard x.1 ^ e ∧
      ∀ G : WeilSheaf k₀ l X,
        Nonempty (((G.stalk x).powFrobenius e).Equiv
          (((poweredGeometricPullback u r hu).obj G).stalk s)) := by
  classical
  let f := X ↘ Spec (.of k₀)
  let g := C ↘ Spec (.of k₁)
  have : Finite (C.residueField s.1) := C.mem_finitePoints.mp s.2
  let x : X.finitePoints :=
    ⟨c s.1, Finite.of_injective _ (c.residueFieldMap s.1).hom.injective⟩
  let := (c.residueFieldMap s.1).hom.toAlgebra
  have : Finite (X.residueField x.1) := X.mem_finitePoints.mp x.2
  let e := Module.finrank (X.residueField x.1) (C.residueField s.1)
  have he : 0 < e := Module.finrank_pos
  have hnorm : C.pointNorm s.1 = X.pointNorm x.1 ^ e :=
    Module.natCard_eq_pow_finrank
  have hq : g.residueCard s.1 = f.residueCard x.1 ^ e := by
    rw [Scheme.Hom.residueCard, Scheme.Hom.residueCard,
      ← g.pointNorm_eq_pow_degreeOver s.2, ← f.pointNorm_eq_pow_degreeOver x.2]
    exact hnorm
  have hd : r * g.degreeOver s.1 = f.degreeOver x.1 * e := by
    apply (Nat.pow_right_injective (show 1 < Nat.card k₀ from Finite.one_lt_card))
    simpa only [Scheme.Hom.residueCard, hcard, ← pow_mul] using hq
  refine ⟨x, e, rfl, he, hq, fun G ↦ ?_⟩
  let t := g.geometricFiberPointOfFinitePoint s
  let a := Spec.map (CommRingCat.ofHom τ.symm.toRingHom)
  have ha : IsIso a := (Scheme.Spec.mapIso τ.symm.toCommRingCatIso.op).isIso_hom
  have hs : t ≫ (g.geometricGaloisFrobenius ^ g.degreeOver s.1).hom =
      (specGeometricFrobenius k₁ ^ g.degreeOver s.1).hom ≫ t :=
    g.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow s
  have hσ : a ≫ (specGeometricFrobenius k₁).hom =
      (specGeometricFrobenius k₀ ^ r).hom ≫ a := by
    let := Fintype.ofFinite k₀
    let := Fintype.ofFinite k₁
    dsimp [a]
    rw [specGeometricFrobenius_hom, specGeometricFrobenius_pow_hom,
      ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext z
    exact algEquiv_geometricFrobenius_apply r
      (by simpa only [Nat.card_eq_fintype_card] using hcard) τ.symm z
  have hσm : a ≫ (specGeometricFrobenius k₁ ^ g.degreeOver s.1).hom =
      (specGeometricFrobenius k₀ ^ (r * g.degreeOver s.1)).hom ≫ a := by
    simpa only [← pow_mul] using
      (poweredPullback_comm_pow _ _ a hσ.symm (g.degreeOver s.1)).symm
  have hum : (g.geometricGaloisFrobenius ^ g.degreeOver s.1).hom ≫ u =
      u ≫ (f.geometricGaloisFrobenius ^ (r * g.degreeOver s.1)).hom := by
    simpa only [← pow_mul] using poweredPullback_comm_pow _ _ u hu (g.degreeOver s.1)
  have ht : (a ≫ t ≫ u) ≫
      (f.geometricGaloisFrobenius ^ (r * g.degreeOver s.1)).hom =
      (specGeometricFrobenius k₀ ^ (r * g.degreeOver s.1)).hom ≫ (a ≫ t ≫ u) := by
    rw [Category.assoc, Category.assoc, ← hum, ← Category.assoc t, hs]
    simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ t ≫ u) hσm
  have hbase : ((a ≫ t ≫ u) ≫ f.geometricFiberProj).base
      (IsLocalRing.closedPoint (AlgebraicClosure k₀)) = x.1 := by
    rw [Category.assoc, Category.assoc, hup, ← Category.assoc t,
      ← Category.assoc a]
    have hapt : a (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
        IsLocalRing.closedPoint (AlgebraicClosure k₁) := Subsingleton.elim _ _
    simp only [Scheme.Hom.comp_apply, hapt]
    exact congrArg c.base (g.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base s)
  obtain ⟨E₀⟩ := pow_stalk_equiv_of_image G x e (r * g.degreeOver s.1)
    (hd.trans (Nat.mul_comm _ _)) (a ≫ t ≫ u) ht hbase
  let H := (poweredGeometricPullback u r hu).obj G
  let b := Spec.map (CommRingCat.ofHom τ.toRingHom)
  have hb : IsIso b := (Scheme.Spec.mapIso τ.toCommRingCatIso.op).isIso_hom
  have hba : b ≫ a = 𝟙 _ :=
    (Scheme.Spec.mapIso τ.toCommRingCatIso.op).hom_inv_id
  have hbσ : (specGeometricFrobenius k₁ ^ g.degreeOver s.1).hom ≫ b =
      b ≫ (specGeometricFrobenius k₀ ^ (r * g.degreeOver s.1)).hom := by
    rw [← cancel_mono a, Category.assoc, Category.assoc, ← hσm, ← Category.assoc b,
      hba, Category.id_comp, Category.comp_id]
  have hbpt : b ≫ (a ≫ t ≫ u) = t ≫ u := by
    rw [← Category.assoc, hba, Category.id_comp]
  obtain ⟨E₁⟩ :=
    stalkEquiv_of_transportSquare G H u (r * g.degreeOver s.1) (g.degreeOver s.1) hum
      (poweredPullbackCarrierIso u r hu G)
      (poweredGeometricPullback_frobeniusPowStr (k₀ := k₀) (k₁ := k₁)
        (l := l) (X := X) (C := C) u r hu G (g.degreeOver s.1) hum)
      (Scheme.Spec.mapIso τ.toCommRingCatIso.op) (a ≫ t ≫ u) t ht hs hbpt hbσ
  exact ⟨E₀.trans E₁⟩

end AlgebraicGeometry.WeilSheaf
