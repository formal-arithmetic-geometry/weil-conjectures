/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F7
-/
module

public import Sheaf.DeligneLaumon.PoweredGeometricPullback
public import WeilConjectures.WeilSheaf.Stalk
import Sheaf.DeligneLaumon.PoweredGeometricPullbackIterate
import WeilConjectures.WeilSheaf.StalkCharpoly
import WeilConjectures.WeilSheaf.BaseChangeField.Geometric
import WeilConjectures.Evaluation

/-! # Local Frobenius under a powered geometric pullback -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

/-- An intertwining map also intertwines every power. -/
private theorem poweredPullback_comm_pow {A B : Scheme.{u}} (f : Aut A) (g : Aut B)
    (v : A ⟶ B) (h : f.hom ≫ v = v ≫ g.hom) (m : ℕ) :
    (f ^ m).hom ≫ v = v ≫ (g ^ m).hom := by
  induction m with
  | zero => exact (Category.id_comp _).trans (Category.comp_id _).symm
  | succ m ih =>
    rw [pow_succ, pow_succ, Aut.Aut_mul_def, Aut.Aut_mul_def, Iso.trans_hom,
      Iso.trans_hom, Category.assoc, ih, ← Category.assoc, h, Category.assoc]

private theorem transport_comm_square {l : ℕ} [Fact l.Prime]
    {P Q A B : Scheme.{u}} (v : A ⟶ B) (fA : A ⟶ A) (fB : B ⟶ B)
    (hv : fA ≫ v = v ≫ fB)
    {M : Sheaf (Scheme.ProEt.topology B) (WeilCoefficients.{u} l)}
    {N : Sheaf (Scheme.ProEt.topology A) (WeilCoefficients.{u} l)}
    (ψM : (fB)^*[_].obj M ⟶ M) (ψN : (fA)^*[_].obj N ⟶ N)
    (θ : (v)^*[_].obj M ⟶ N)
    (hθ : (ProEtale.upperStarComp _ fA v).hom.app M ≫ (fA)^*[_].map θ ≫ ψN =
      (ProEtale.upperStarCongr _ hv).hom.app M ≫
        (ProEtale.upperStarComp _ v fB).hom.app M ≫ (v)^*[_].map ψM ≫ θ)
    {t : P ⟶ B} {s : Q ⟶ A} {a : Q ⟶ P} {σ : P ⟶ P} {ρ : Q ⟶ Q}
    (h : a ≫ t = s ≫ v) (ht : σ ≫ t = t ≫ fB) (hs : ρ ≫ s = s ≫ fA)
    (ha : ρ ≫ a = a ≫ σ) :
    ProEtale.globalSectionsTransport _ ht ψM ≫ ProEtale.globalSectionsTransport _ h θ =
      ProEtale.globalSectionsTransport _ h θ ≫ ProEtale.globalSectionsTransport _ hs ψN := by
  have h₁ : (a ≫ σ) ≫ t = s ≫ (v ≫ fB) := by
    rw [Category.assoc, ht, ← Category.assoc, h, Category.assoc]
  have h₂ : (ρ ≫ a) ≫ t = s ≫ (fA ≫ v) := by
    rw [Category.assoc, h, ← Category.assoc, hs, Category.assoc]
  rw [ProEtale.globalSectionsTransport_comp _ ht h h₁,
    ProEtale.globalSectionsTransport_comp _ h hs h₂,
    ProEtale.globalSectionsTransport_congr _ h₂ hv _ _ hθ,
    ProEtale.globalSectionsTransport_congr_left _ _ ha]

private theorem isIso_transport {l : ℕ} [Fact l.Prime]
    {P Q A B : Scheme.{u}} (v : A ⟶ B) (e : Q ≅ P)
    {t : P ⟶ B} {s : Q ⟶ A} (h : e.hom ≫ t = s ≫ v)
    {M : Sheaf (Scheme.ProEt.topology B) (WeilCoefficients.{u} l)}
    {N : Sheaf (Scheme.ProEt.topology A) (WeilCoefficients.{u} l)}
    (θ : (v)^*[_].obj M ≅ N) :
    IsIso (ProEtale.globalSectionsTransport _ h θ.hom) := by
  rw [ProEtale.globalSectionsTransport_eq_of_iso _ e h]
  infer_instance

private theorem linearEquivOfIso_toLinearMap {l : ℕ} [Fact l.Prime]
    {M N : WeilCoefficients.{u} l} (e : M ≅ N) :
    (WeilCoefficients.linearEquivOfIso e).toLinearMap =
      ((WeilCoefficients.toModuleCat l).map e.hom).hom := rfl

/-- Convert a compatible sheaf square to stalk characteristic polynomials, keeping the
sheaf objects abstract while using the transport API. -/
private theorem stalk_charpoly_of_square
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X C : Scheme.{u}} [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
    (G : WeilSheaf k₀ l X) (H : WeilSheaf k₁ l C)
    (v : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    (m n : ℕ)
    (hv : ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ n).hom ≫ v =
      v ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ m).hom)
    (θ : (v)^*[WeilCoefficients.{u} l].obj G.obj.carrier.X ≅ H.obj.carrier.X)
    (hθ : (ProEtale.upperStarComp _
        ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ n).hom v).hom.app G.obj.carrier.X ≫
        (((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ n).hom)^*[_].map θ.hom ≫
          H.frobeniusPowStr n =
      (ProEtale.upperStarCongr _ hv).hom.app G.obj.carrier.X ≫
        (ProEtale.upperStarComp _ v
          ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ m).hom).hom.app G.obj.carrier.X ≫
        (v)^*[_].map (G.frobeniusPowStr m) ≫ θ.hom)
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    (s : Spec (.of (AlgebraicClosure k₁)) ⟶ (C ↘ Spec (.of k₁)).geometricFiber)
    (e : Spec (.of (AlgebraicClosure k₁)) ≅ Spec (.of (AlgebraicClosure k₀)))
    (h : e.hom ≫ t = s ≫ v)
    (ht : t ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ t)
    (hs : s ≫ ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ n).hom =
      (specGeometricFrobenius k₁ ^ n).hom ≫ s)
    (he : (specGeometricFrobenius k₁ ^ n).hom ≫ e.hom =
      e.hom ≫ (specGeometricFrobenius k₀ ^ m).hom) :
    (H.stalkAt s n hs).frobeniusEnd.charpoly =
      (G.stalkAt t m ht).frobeniusEnd.charpoly := by
  let T := ProEtale.globalSectionsTransport _ h θ.hom
  have : IsIso T := isIso_transport (l := l) v e h θ
  have key := transport_comm_square (l := l)
    (M := G.obj.carrier.X) (N := H.obj.carrier.X)
    (t := t) (s := s) (a := e.hom)
    (σ := (specGeometricFrobenius k₀ ^ m).hom)
    (ρ := (specGeometricFrobenius k₁ ^ n).hom) v
    ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius ^ n).hom
    ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ m).hom hv
    (G.frobeniusPowStr m) (H.frobeniusPowStr n) θ.hom hθ h ht.symm hs.symm he
  let E : (G.stalkAt t m ht).Equiv (H.stalkAt s n hs) :=
    .ofComp (WeilCoefficients.linearEquivOfIso (asIso T)) (by
      rw [linearEquivOfIso_toLinearMap, asIso_hom,
        frobeniusEnd_stalkAt, frobeniusEnd_stalkAt]
      simpa only [Functor.map_comp, ModuleCat.hom_comp] using
        congrArg (fun z ↦ ((WeilCoefficients.toModuleCat l).map z).hom) key)
  exact E.charpoly_frobeniusEnd

-- The redundant compatibility hypotheses belong to the unchanged original signature.
set_option linter.unusedVariables false in
/-- At any closed point, the explicitly constructed powered pullback has the original
local Frobenius raised to the residue extension degree. This is a single-object assertion
for arbitrary finite-type schemes; it does not assert curve or diagram descent.

Source: blueprint `thm-zl-real-mixed-by-curves.proof.md`, paragraphs 1--3
(blueprint: lem-zl-powered-geometric-pullback-stalk).

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
B*F(P(G),s)=F(G,x)^e*B. Conjugate linear maps have the same characteristic polynomial.
This uses no semisimplicity, rank or lissity
assumption, and works for the zero sheaf and when several closed points have the same image.
The construction of e uses the residue-field embedding only, so works for every sheaf. -/
theorem poweredGeometricPullback_stalk
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    [Algebra k₀ k₁] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X C : Scheme.{u}} [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
    [LocallyOfFiniteType (X ↘ Spec (.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (.of k₁))]
    (r : ℕ) (hr : 0 < r) (hcard : Nat.card k₁ = Nat.card k₀ ^ r)
    (τ : AlgebraicClosure k₀ ≃+* AlgebraicClosure k₁)
    (hτ : ∀ a : k₀, τ (algebraMap k₀ (AlgebraicClosure k₀) a) =
      algebraMap k₁ (AlgebraicClosure k₁) (algebraMap k₀ k₁ a))
    (c : C ⟶ X)
    (hc : c ≫ (X ↘ Spec (.of k₀)) =
      (C ↘ Spec (.of k₁)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k₁)))
    (u : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    (hup : u ≫ (X ↘ Spec (.of k₀)).geometricFiberProj =
      (C ↘ Spec (.of k₁)).geometricFiberProj ≫ c)
    (huτ : u ≫ (X ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure =
      (C ↘ Spec (.of k₁)).geometricFiberToAlgebraicClosure ≫
        Spec.map (CommRingCat.ofHom τ.toRingHom))
    (hu : (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom ≫ u =
      u ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom)
    (s : C.finitePoints) :
    ∃ (x : X.finitePoints) (e : ℕ), c s.1 = x.1 ∧ 0 < e ∧
      (C ↘ Spec (.of k₁)).residueCard s.1 =
        (X ↘ Spec (.of k₀)).residueCard x.1 ^ e ∧
      ∀ G : WeilSheaf k₀ l X,
        (((poweredGeometricPullback u r hu).obj G).stalk s).frobeniusEnd.charpoly =
          ((G.stalk x).frobeniusEnd ^ e).charpoly := by
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
  have hdvd : f.degreeOver x.1 ∣ r * g.degreeOver s.1 := ⟨e, hd⟩
  have hdiv : r * g.degreeOver s.1 / f.degreeOver x.1 = e := by
    rw [hd, Nat.mul_div_cancel_left e (Nat.pos_of_ne_zero (f.degreeOver_ne_zero x.2))]
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
  have hcanon := f.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base x
  have hchar := G.charpoly_frobeniusEnd_stalkAt_of_dvd
    (f.geometricFiberPointOfFinitePoint x) (a ≫ t ≫ u)
    (hcanon.trans hbase.symm) (hcanon.symm ▸ x.2) hdvd
    (f.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow x) ht
  rw [hdiv] at hchar
  suffices hcomp : (((poweredGeometricPullback u r hu).obj G).stalk s).frobeniusEnd.charpoly =
      (G.stalkAt (a ≫ t ≫ u) (r * g.degreeOver s.1) ht).frobeniusEnd.charpoly by
    exact hcomp.trans hchar
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
  simpa only [stalk] using
    stalk_charpoly_of_square G H u (r * g.degreeOver s.1) (g.degreeOver s.1) hum
      (poweredPullbackCarrierIso u r hu G)
      (poweredGeometricPullback_frobeniusPowStr (k₀ := k₀) (k₁ := k₁)
        (l := l) (X := X) (C := C) u r hu G (g.degreeOver s.1) hum)
      (a ≫ t ≫ u) t (Scheme.Spec.mapIso τ.toCommRingCatIso.op) hbpt ht hs hbσ

end AlgebraicGeometry.WeilSheaf
