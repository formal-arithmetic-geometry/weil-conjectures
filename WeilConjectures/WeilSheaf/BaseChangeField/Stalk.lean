/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.BaseChangeField.Restriction
public import WeilConjectures.WeilSheaf.EquivariantPullback
public import WeilConjectures.WeilSheaf.StalkUpperStar

/-!
# Stalks of the restriction of a Weil sheaf to a finite extension of the base field

Let `θ : Ȳ ≅ Ȳ'` identify the geometric fibers of a `k₀`-scheme `Y` and a `k₀'`-scheme `Y'`, with
`θ ≫ Fr' = Frʳ ≫ θ`, and let `(θ_* F̄, θ_* φ_r)` be the transport of a Weil sheaf `F` on `Y`
(`AlgebraicGeometry.WeilSheaf.transport`). The identification `θ⁻¹^* F̄ ≅ θ_* F̄` is compatible
with the iterated Weil structure `φ_r` of `F` and the Weil structure of the transport, so the stalk
of the transport at a geometric point `s'` of `Ȳ'`, with its Frobenius relative to `𝔽_{q'ᵐ}`, is
the stalk of `F` at the corresponding geometric point `s` of `Ȳ`, with its Frobenius relative to
`𝔽_{q^{r m}}`.

For the restriction `F ↦ F_K` to `X_K = X ×_{k₀} K` (`AlgebraicGeometry.WeilSheaf.baseChangeField`)
this shows that restriction preserves punctual purity: a closed point `x'` of `X_K` of degree `e'`
over `K` lies over a closed point `x` of `X` whose degree over `k₀` divides `[K : k₀] e'`, so the
local Frobenius of `F_K` at `x'` has the characteristic polynomial of a power of the local
Frobenius of `F` at `x`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalkAt_of_compatible`: the stalks along a morphism
  `j^* F̄ ⟶ Ḡ` compatible with the Weil structures, with their Frobenius.
- `AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalkAt_transport`: the stalks of the transport.
- `AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.baseChangeField`: the restriction of a
  punctually pure Weil sheaf to `X_K` is punctually pure of the same weight.

## Implementation details

The kernel compares two congruence isomorphisms `(g)_* ≅ (g')_*` along a non-definitional
equation `g = g'` by unfolding them, which does not terminate in reasonable time unless they are
syntactically equal. The comparisons are therefore arranged so that these isomorphisms agree
syntactically, also in their implicit arguments: for instance the identification of `θ⁻¹^*` with
`θ_*` is written through `θ.symm`, and the pushforwards along `θ.hom` and `θ.symm.inv` are
exchanged by explicit lemmas.
-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.ProEtale

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

-- Stated for an arbitrary morphism `w`, so that the kernel never unfolds the identifications
-- `e^* ≅ (e⁻¹)_*` of the composites; the congruence isomorphisms are matched syntactically.
private lemma upperStarIsoLowerStarInv_hom_app_conj_aux {U V : Scheme.{u}} (e : U ≅ V)
    (gU : U ≅ U) (gV : V ≅ V) (hc : gU.hom ≫ e.hom = e.hom ≫ gV.hom)
    (hc' : e.inv ≫ gU.inv = gV.inv ≫ e.inv) (M : Sheaf (Scheme.ProEt.topology V) A)
    {a : U ⟶ V} {ai : V ⟶ U} (w : (a)^*[A].obj M ⟶ (ai)_*[A].obj M)
    (hE : gU.hom ≫ e.hom = a) (hE' : e.hom ≫ gV.hom = a) (hEi : e.inv ≫ gU.inv = ai)
    (hEi' : gV.inv ≫ e.inv = ai)
    (h₁ : w ≫ (lowerStarFactor A hEi).inv.app M = (upperStarFactor A hE).hom.app M ≫
      (gU.hom)^*[A].map ((upperStarIsoLowerStarInv A e).hom.app M) ≫
      (upperStarIsoLowerStarInv A gU).hom.app ((e.inv)_*[A].obj M))
    (h₂ : w ≫ (lowerStarFactor A hEi').inv.app M = (upperStarFactor A hE').hom.app M ≫
      (e.hom)^*[A].map ((upperStarIsoLowerStarInv A gV).hom.app M) ≫
      (upperStarIsoLowerStarInv A e).hom.app ((gV.inv)_*[A].obj M)) :
    (upperStarComp A gU.hom e.hom).hom.app M ≫
        (gU.hom)^*[A].map ((upperStarIsoLowerStarInv A e).hom.app M) ≫
        (upperStarIsoLowerStarInv A gU).hom.app ((e.inv)_*[A].obj M) ≫
        (lowerStarComp A e.inv gU.inv).hom.app M ≫ (lowerStarCongr A hc').hom.app M ≫
        (lowerStarComp A gV.inv e.inv).inv.app M =
      (upperStarCongr A hc).hom.app M ≫ (upperStarComp A e.hom gV.hom).hom.app M ≫
        (e.hom)^*[A].map ((upperStarIsoLowerStarInv A gV).hom.app M) ≫
        (upperStarIsoLowerStarInv A e).hom.app ((gV.inv)_*[A].obj M) := by
  subst hE hEi
  rw [upperStarFactor_rfl, ← lowerStarComp_trans_lowerStarCongr, lowerStarCongr_rfl,
    Iso.trans_refl] at h₁
  rw [upperStarFactor, Iso.trans_hom, NatTrans.comp_app, Category.assoc] at h₂
  have hU {x y : U ⟶ V} (p q : x = y) :
      (upperStarCongr A p).hom.app M = (upperStarCongr A q).hom.app M := by
    obtain rfl : p = q := rfl
    rfl
  have hL {x y : V ⟶ U} (p : x = y) (q : y = x) :
      (lowerStarCongr A p).hom.app M = (lowerStarCongr A q).inv.app M := by
    subst p
    simp [lowerStarCongr]
  rw [hU _ hc] at h₂
  rw [← reassoc_of% h₁, Iso.inv_hom_id_app_assoc, ← h₂, ← lowerStarComp_trans_lowerStarCongr,
    Iso.trans_inv, NatTrans.comp_app]
  exact congrArg (fun f ↦ w ≫ f ≫ (lowerStarComp A gV.inv e.inv).inv.app M) (hL hc' hEi')

/-- The identifications `e^* ≅ (e⁻¹)_*` are compatible with automorphisms `g_U` of `U` and `g_V`
of `V` intertwined by an isomorphism `e : U ≅ V`, `g_U ≫ e = e ≫ g_V`: the two ways of going
from `(g_U ≫ e)^* M` to `g_V⁻¹_* e⁻¹_* M` agree. -/
lemma upperStarIsoLowerStarInv_hom_app_conj {U V : Scheme.{u}} (e : U ≅ V)
    (gU : U ≅ U) (gV : V ≅ V) (hc : gU.hom ≫ e.hom = e.hom ≫ gV.hom)
    (hc' : e.inv ≫ gU.inv = gV.inv ≫ e.inv) (M : Sheaf (Scheme.ProEt.topology V) A) :
    (upperStarComp A gU.hom e.hom).hom.app M ≫
        (gU.hom)^*[A].map ((upperStarIsoLowerStarInv A e).hom.app M) ≫
        (upperStarIsoLowerStarInv A gU).hom.app ((e.inv)_*[A].obj M) ≫
        (lowerStarComp A e.inv gU.inv).hom.app M ≫ (lowerStarCongr A hc').hom.app M ≫
        (lowerStarComp A gV.inv e.inv).inv.app M =
      (upperStarCongr A hc).hom.app M ≫ (upperStarComp A e.hom gV.hom).hom.app M ≫
        (e.hom)^*[A].map ((upperStarIsoLowerStarInv A gV).hom.app M) ≫
        (upperStarIsoLowerStarInv A e).hom.app ((gV.inv)_*[A].obj M) :=
  upperStarIsoLowerStarInv_hom_app_conj_aux A e gU gV hc hc' M _ _
    (hc.symm.trans (Iso.trans_hom gU e).symm) _ (hc'.symm.trans (Iso.trans_inv gU e).symm)
    (upperStarIsoLowerStarInv_hom_app_trans A gU e (gU ≪≫ e) (Iso.trans_hom gU e).symm
      (Iso.trans_inv gU e).symm M)
    (upperStarIsoLowerStarInv_hom_app_trans A e gV (gU ≪≫ e)
      (hc.symm.trans (Iso.trans_hom gU e).symm) (hc'.symm.trans (Iso.trans_inv gU e).symm) M)

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The pushforward along `e.hom` and along `e.symm.inv` agree, after a composition and a
congruence isomorphism. -/
@[reassoc]
lemma lowerStarComp_hom_app_comp_lowerStarCongr_hom_app_symm {U V : Scheme.{u}} (e : V ≅ U)
    (g : U ⟶ U) {c : V ⟶ U} (P : e.hom ≫ g = c) (P' : e.symm.inv ≫ g = c)
    (M : Sheaf (Scheme.ProEt.topology V) A) :
    (lowerStarComp A e.hom g).hom.app M ≫ (lowerStarCongr A P).hom.app M =
      (lowerStarComp A e.symm.inv g).hom.app M ≫ (lowerStarCongr A P').hom.app M := by
  subst P
  rfl

omit [Abelian A] [IsGrothendieckAbelian.{u + 1} A] in
/-- The pushforward along `e.hom` and along `e.symm.inv` agree, after a congruence isomorphism and
a composition. -/
@[reassoc]
lemma lowerStarCongr_hom_app_comp_lowerStarComp_inv_app_symm {U V : Scheme.{u}} (e : V ≅ U)
    (g : V ⟶ V) {c : V ⟶ U} (Q : c = g ≫ e.hom) (Q' : c = g ≫ e.symm.inv)
    (M : Sheaf (Scheme.ProEt.topology V) A) :
    (lowerStarCongr A Q).hom.app M ≫ (lowerStarComp A g e.hom).inv.app M =
      (lowerStarCongr A Q').hom.app M ≫ (lowerStarComp A g e.symm.inv).inv.app M := by
  subst Q
  rfl

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtaleWeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  {k₀' : Type u} [Field k₀'] [Finite k₀']
  {Y' : Scheme.{u}} [Y'.Over (Spec (CommRingCat.of k₀'))]
  (θ : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
    (Y' ↘ Spec (CommRingCat.of k₀')).geometricFiber) (r : ℕ)
  (hθ : θ.hom ≫ (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.hom =
    ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.hom ≫ θ.hom)

/-- The Weil structure `θ_* φ_r` of the transport `(θ_* K, θ_* φ_r)`, on the underlying sheaves:
`(Fr'⁻¹)_* θ_* K ≅ θ_* (Fr⁻ʳ)_* K --θ_* φ_r--> θ_* K`. -/
lemma forget_map_transport_obj_str_hom (K : ProEtaleWeilSheaf k₀ l Y) :
    (AdicSheaf.forget _).map ((transport θ r hθ).obj K).str.hom =
      (lowerStarComp (WeilCoefficients.{u} l) θ.hom
          (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.inv).hom.app K.carrier.X ≫
        (lowerStarCongr _ (hom_comp_geometricGaloisFrobenius_inv θ r hθ)).hom.app K.carrier.X ≫
        (lowerStarComp (WeilCoefficients.{u} l)
          ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.inv
          θ.hom).inv.app K.carrier.X ≫
        (θ.hom)_*[_].map ((AdicSheaf.forget _).map (K.frobeniusPowIso r).hom) := by
  rw [transport_obj_str, transportCommIso]
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, NatTrans.comp_app,
    Mod.forget_map, Mod.comp_hom', adicLowerStarComp_hom_app_hom, adicLowerStarCongr_hom_app_hom,
    adicLowerStarComp_inv_app_hom, adicLowerStar_map_hom, Category.assoc]

end AlgebraicGeometry.ProEtaleWeilSheaf

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

section Compatible

variable {l : ℕ} [Fact l.Prime]
  {k₀ : Type u} [Field k₀] [Finite k₀] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  {L : Type u} [Field L] [Finite L] [Fact (ringChar L ≠ l)]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of L))] {N : ℕ}
  {j : (Y ↘ Spec (CommRingCat.of L)).geometricFiber ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
  {F : WeilSheaf k₀ l X} {G : WeilSheaf L l Y}
  {ψ : (j)^*[WeilCoefficients.{u} l].obj F.obj.carrier.X ⟶ G.obj.carrier.X}

/-- A morphism `ψ : j^* F̄ ⟶ Ḡ` compatible with the iterated Weil structure `φ_N` of `F` and the
Weil structure of `G` intertwines the transports of global sections along `φ_N` and along the
Weil structure of `G`, over squares `Θ ≫ t = t' ≫ j`. -/
lemma globalSectionsTransport_frobeniusPowStr_comp_of_compatible_one
    (hj : j ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
      (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom ≫ j)
    (hψ : (ProEtale.upperStarComp _
        (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom j).hom.app
          F.obj.carrier.X ≫
        ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom)^*[_].map ψ ≫
          G.frobeniusStr =
      (ProEtale.upperStarCongr _ hj.symm).hom.app F.obj.carrier.X ≫
        (ProEtale.upperStarComp _ j
          ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom).hom.app
          F.obj.carrier.X ≫
        (j)^*[_].map (F.frobeniusPowStr N) ≫ ψ)
    {Θ : Spec (.of (AlgebraicClosure L)) ⟶ Spec (.of (AlgebraicClosure k₀))}
    {t₁ t₂ : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {t₁' t₂' : Spec (.of (AlgebraicClosure L)) ⟶ (Y ↘ Spec (CommRingCat.of L)).geometricFiber}
    {τ : Spec (.of (AlgebraicClosure k₀)) ⟶ Spec (.of (AlgebraicClosure k₀))}
    {τ' : Spec (.of (AlgebraicClosure L)) ⟶ Spec (.of (AlgebraicClosure L))}
    (h₁ : Θ ≫ t₁ = t₁' ≫ j) (h₂ : Θ ≫ t₂ = t₂' ≫ j)
    (hX : τ ≫ t₁ = t₂ ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom)
    (hY : τ' ≫ t₁' = t₂' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ 1).asIso.hom)
    (hΘ : τ' ≫ Θ = Θ ≫ τ) :
    ProEtale.globalSectionsTransport _ hX (F.frobeniusPowStr N) ≫
        ProEtale.globalSectionsTransport _ h₂ ψ =
      ProEtale.globalSectionsTransport _ h₁ ψ ≫
        ProEtale.globalSectionsTransport _ hY (G.frobeniusPowStr 1) := by
  have pY := congrArg (fun e ↦ e.asIso.hom)
    (pow_one (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius)
  rw [ProEtale.globalSectionsTransport_congr _ hY pY _ _ (frobeniusPowStr_one _ pY)]
  exact ProEtale.globalSectionsTransport_comm_of_upperStar_of_comp _ j _ _
    hj.symm _ _ _ hψ h₁ h₂ hX _ hΘ

/-- A morphism `ψ : j^* F̄ ⟶ Ḡ` compatible with the iterated Weil structure `φ_N` of `F` and the
Weil structure of `G` intertwines the transports of global sections along the iterated Weil
structures `φ_{N m}` of `F` and `φ_m` of `G`, `m ≥ 1`. -/
lemma globalSectionsTransport_frobeniusPowStr_comp_of_compatible
    (hj : j ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
      (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom ≫ j) (hN : 1 ≤ N)
    (hψ : (ProEtale.upperStarComp _
        (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom j).hom.app
          F.obj.carrier.X ≫
        ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom)^*[_].map ψ ≫
          G.frobeniusStr =
      (ProEtale.upperStarCongr _ hj.symm).hom.app F.obj.carrier.X ≫
        (ProEtale.upperStarComp _ j
          ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom).hom.app
          F.obj.carrier.X ≫
        (j)^*[_].map (F.frobeniusPowStr N) ≫ ψ)
    (m : ℕ) (hm : 1 ≤ m)
    {Θ : Spec (.of (AlgebraicClosure L)) ⟶ Spec (.of (AlgebraicClosure k₀))}
    {t₁ t₂ : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {t₁' t₂' : Spec (.of (AlgebraicClosure L)) ⟶ (Y ↘ Spec (CommRingCat.of L)).geometricFiber}
    {τ : Spec (.of (AlgebraicClosure k₀)) ⟶ Spec (.of (AlgebraicClosure k₀))}
    {τ' : Spec (.of (AlgebraicClosure L)) ⟶ Spec (.of (AlgebraicClosure L))}
    (h₁ : Θ ≫ t₁ = t₁' ≫ j) (h₂ : Θ ≫ t₂ = t₂' ≫ j)
    (hX : τ ≫ t₁ =
      t₂ ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m)).asIso.hom)
    (hY : τ' ≫ t₁' = t₂' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ m).asIso.hom)
    (hΘ : τ' ≫ Θ = Θ ≫ τ) :
    ProEtale.globalSectionsTransport _ hX (F.frobeniusPowStr (N * m)) ≫
        ProEtale.globalSectionsTransport _ h₂ ψ =
      ProEtale.globalSectionsTransport _ h₁ ψ ≫
        ProEtale.globalSectionsTransport _ hY (G.frobeniusPowStr m) := by
  induction m, hm using Nat.le_induction generalizing t₁ t₂ t₁' t₂' τ τ' with
  | base =>
    have hX' : τ ≫ t₁ =
        t₂ ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom := by
      rw [hX, Nat.mul_one]
    rw [globalSectionsTransport_frobeniusPowStr_congr F (Nat.mul_one N) rfl hX hX']
    exact globalSectionsTransport_frobeniusPowStr_comp_of_compatible_one hj hψ h₁ h₂ hX' hY hΘ
  | succ m hm ih =>
    have pc' : j ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m)).asIso.inv =
        ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ m).asIso.inv ≫ j := by
      rw [← cancel_mono
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m)).asIso.hom,
        Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        comp_geometricGaloisFrobenius_pow_mul_eq j hj m, Iso.inv_hom_id_assoc]
    have haX : (Iso.refl _).hom ≫ t₁ =
        (t₁ ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m)).asIso.inv) ≫
          ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m)).asIso.hom := by
      simp
    have hbX : τ ≫
        (t₁ ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m)).asIso.inv) =
        t₂ ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom := by
      rw [← cancel_mono
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m)).asIso.hom,
        Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, hX, Category.assoc,
        Aut.pow_hom_comp_pow_hom, Nat.mul_succ]
    have haY : (Iso.refl _).hom ≫ t₁' =
        (t₁' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ m).asIso.inv) ≫
          ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ m).asIso.hom := by
      simp
    have hbY : τ' ≫ (t₁' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ m).asIso.inv) =
        t₂' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ 1).asIso.hom := by
      rw [← cancel_mono ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ m).asIso.hom,
        Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, hY, Category.assoc,
        Aut.pow_hom_comp_pow_hom]
    have hmid : Θ ≫
        (t₁ ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m)).asIso.inv) =
        (t₁' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ m).asIso.inv) ≫ j := by
      rw [← Category.assoc, h₁, Category.assoc, pc', Category.assoc]
    have hΘ₀ : (Iso.refl _).hom ≫ Θ = Θ ≫ (Iso.refl _).hom := by simp
    have hX'' : τ ≫ t₁ =
        t₂ ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * m + N)).asIso.hom := by
      rw [hX, Nat.mul_succ]
    rw [globalSectionsTransport_frobeniusPowStr_congr F (Nat.mul_succ N m) rfl hX hX'',
      ← F.globalSectionsTransport_frobeniusPowStr_comp (N * m) N hN haX hbX (Category.comp_id τ)
        hX'',
      ← G.globalSectionsTransport_frobeniusPowStr_comp m 1 le_rfl haY hbY (Category.comp_id τ') hY,
      Category.assoc,
      globalSectionsTransport_frobeniusPowStr_comp_of_compatible_one hj hψ hmid h₂ hbX hbY hΘ,
      ← Category.assoc, ih h₁ hmid haX haY hΘ₀, Category.assoc]

/-- **Stalks along a compatible morphism.** Let `ψ : j^* F̄ ⟶ Ḡ` be an isomorphism compatible with
the iterated Weil structure `φ_N` of a Weil sheaf `F` on `X` over `k₀` and the Weil structure of a
Weil sheaf `G` on `Y` over `L`, and let `Θ : Spec k̄_L ≅ Spec k̄₀` carry the `n`-th power of the
geometric Frobenius of `k̄_L` to the `N n`-th power of that of `k̄₀`. Then the stalk of `F` at a
geometric point `s` with its Frobenius relative to `𝔽_{q^{N n}}` is the stalk of `G` at a geometric
point `s'` with `Θ ≫ s = s' ≫ j`, with its Frobenius relative to `L_n`. -/
theorem nonempty_equiv_stalkAt_of_compatible
    (hj : j ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
      (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom ≫ j) (hN : 1 ≤ N)
    (hψ : (ProEtale.upperStarComp _
        (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom j).hom.app
          F.obj.carrier.X ≫
        ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom)^*[_].map ψ ≫
          G.frobeniusStr =
      (ProEtale.upperStarCongr _ hj.symm).hom.app F.obj.carrier.X ≫
        (ProEtale.upperStarComp _ j
          ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom).hom.app
          F.obj.carrier.X ≫
        (j)^*[_].map (F.frobeniusPowStr N) ≫ ψ) [IsIso ψ]
    (Θ : Spec (.of (AlgebraicClosure L)) ≅ Spec (.of (AlgebraicClosure k₀)))
    {s' : Spec (.of (AlgebraicClosure L)) ⟶ (Y ↘ Spec (CommRingCat.of L)).geometricFiber}
    {s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hsq : Θ.hom ≫ s = s' ≫ j) {n : ℕ}
    (hΘ : (specGeometricFrobenius L ^ n).asIso.hom ≫ Θ.hom =
      Θ.hom ≫ (specGeometricFrobenius k₀ ^ (N * n)).asIso.hom)
    (hs' : s' ≫ ((Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius ^ n).asIso.hom =
      (specGeometricFrobenius L ^ n).asIso.hom ≫ s')
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (N * n)).asIso.hom =
      (specGeometricFrobenius k₀ ^ (N * n)).asIso.hom ≫ s) :
    Nonempty ((F.stalkAt s (N * n) hs).Equiv (G.stalkAt s' n hs')) := by
  have : IsIso (ProEtale.globalSectionsTransport _ hsq ψ) :=
    ProEtale.isIso_globalSectionsTransport _ _ hsq _
  refine ⟨.ofComp (WeilCoefficients.linearEquivOfIso
    (asIso (ProEtale.globalSectionsTransport _ hsq ψ))) ?_⟩
  rw [WeilCoefficients.linearEquivOfIso_toLinearMap, asIso_hom, frobeniusEnd_stalkAt,
    frobeniusEnd_stalkAt, ← WeilCoefficients.toModuleCat_map_comp_hom,
    ← WeilCoefficients.toModuleCat_map_comp_hom]
  refine congrArg (fun f ↦ ((WeilCoefficients.toModuleCat l).map f).hom) ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h₀ : (specGeometricFrobenius k₀ ^ 0).asIso.hom ≫ s =
        s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.hom := by
      rw [pow_zero, pow_zero]
      rfl
    rw [globalSectionsTransport_frobeniusPowStr_congr F (Nat.mul_zero N)
      (by rw [Nat.mul_zero]) hs.symm h₀, globalSectionsTransport_frobeniusPowStr_zero F
      (by rw [pow_zero]; rfl), globalSectionsTransport_frobeniusPowStr_zero _
      (by rw [pow_zero]; rfl), Category.id_comp, Category.comp_id]
  · exact globalSectionsTransport_frobeniusPowStr_comp_of_compatible hj hN hψ n hn hsq hsq hs.symm
      hs'.symm hΘ

end Compatible

section Transport

open ProEtale

variable {l : ℕ} [Fact l.Prime]
  {k₀ : Type u} [Field k₀] [Finite k₀] [Fact (ringChar k₀ ≠ l)]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  {k₀' : Type u} [Field k₀'] [Finite k₀'] [Fact (ringChar k₀' ≠ l)]
  {Y' : Scheme.{u}} [Y'.Over (Spec (CommRingCat.of k₀'))]
  {θ : (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
    (Y' ↘ Spec (CommRingCat.of k₀')).geometricFiber} {r : ℕ}

/-- An identification `θ : Ȳ ≅ Ȳ'` of geometric fibers with `θ ≫ Fr' = Frʳ ≫ θ` satisfies
`θ⁻¹ ≫ Frʳ = Fr' ≫ θ⁻¹`. -/
lemma symm_hom_comp_geometricGaloisFrobenius_pow
    (hθ : θ.hom ≫ (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.hom =
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.hom ≫ θ.hom) :
    θ.symm.hom ≫ ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.hom =
      (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.hom ≫ θ.symm.hom := by
  rw [Iso.symm_hom, ← cancel_epi θ.hom, Iso.hom_inv_id_assoc, reassoc_of% hθ, Iso.hom_inv_id,
    Category.comp_id]

/-- The identification `θ⁻¹^* F̄ ≅ θ_* F̄` of the underlying sheaves is compatible with the iterated
Weil structure `φ_r` of `F` and the Weil structure of the transport `(θ_* F̄, θ_* φ_r)`. -/
lemma transport_frobeniusStr_compatible
    (hθ : θ.hom ≫ (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.hom =
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.hom ≫ θ.hom)
    (F : WeilSheaf k₀ l Y) :
    (upperStarComp _ (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.hom
        θ.symm.hom).hom.app F.obj.carrier.X ≫
      ((Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.hom)^*[_].map
        ((ProEtale.upperStarIsoLowerStarInv _ θ.symm).hom.app F.obj.carrier.X) ≫
        ((transport θ r hθ).obj F).frobeniusStr =
      (ProEtale.upperStarCongr _ (symm_hom_comp_geometricGaloisFrobenius_pow hθ).symm).hom.app
          F.obj.carrier.X ≫
        (ProEtale.upperStarComp _ θ.symm.hom
          ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.hom).hom.app
          F.obj.carrier.X ≫
        (θ.symm.hom)^*[_].map (F.frobeniusPowStr r) ≫
        (ProEtale.upperStarIsoLowerStarInv _ θ.symm).hom.app F.obj.carrier.X := by
  have hstr : ((transport θ r hθ).obj F).frobeniusStr =
      (ProEtale.upperStarIsoLowerStarInv _
        (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso).hom.app
          ((transport θ r hθ).obj F).obj.carrier.X ≫
        (lowerStarComp (WeilCoefficients.{u} l) θ.hom
          (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.inv).hom.app
          F.obj.carrier.X ≫
        (lowerStarCongr _ (ProEtaleWeilSheaf.hom_comp_geometricGaloisFrobenius_inv θ r hθ)).hom.app
          F.obj.carrier.X ≫
        (lowerStarComp (WeilCoefficients.{u} l)
          ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.inv
          θ.hom).inv.app F.obj.carrier.X ≫
        (θ.hom)_*[_].map ((AdicSheaf.forget _).map (F.obj.frobeniusPowIso r).hom) :=
    congrArg (_ ≫ ·) (ProEtaleWeilSheaf.forget_map_transport_obj_str_hom θ r hθ F.obj)
  have nat : (θ.symm.hom)^*[_].map ((AdicSheaf.forget _).map (F.obj.frobeniusPowIso r).hom) ≫
      (ProEtale.upperStarIsoLowerStarInv (WeilCoefficients.{u} l) θ.symm).hom.app
        F.obj.carrier.X =
      (ProEtale.upperStarIsoLowerStarInv (WeilCoefficients.{u} l) θ.symm).hom.app
        ((((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.inv)_*[_].obj
          F.obj.carrier.X) ≫
        (θ.symm.inv)_*[_].map ((AdicSheaf.forget _).map (F.obj.frobeniusPowIso r).hom) :=
    (ProEtale.upperStarIsoLowerStarInv (WeilCoefficients.{u} l) θ.symm).hom.naturality _
  have hc' : θ.symm.inv ≫ (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.inv =
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.inv ≫ θ.symm.inv :=
    ProEtaleWeilSheaf.hom_comp_geometricGaloisFrobenius_inv θ r hθ
  rw [hstr, frobeniusPowStr, frobeniusPowIso_eq, Functor.map_comp, Category.assoc, nat,
    lowerStarComp_hom_app_comp_lowerStarCongr_hom_app_symm_assoc _ θ _ _
      (ProEtaleWeilSheaf.hom_comp_geometricGaloisFrobenius_inv θ r hθ),
    lowerStarCongr_hom_app_comp_lowerStarComp_inv_app_symm_assoc _ θ _ _ hc']
  have key := ProEtale.upperStarIsoLowerStarInv_hom_app_conj _ θ.symm
    (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso
    ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso
    (symm_hom_comp_geometricGaloisFrobenius_pow hθ).symm hc' F.obj.carrier.X =≫
      (θ.symm.inv)_*[_].map ((AdicSheaf.forget _).map (F.obj.frobeniusPowIso r).hom)
  simp only [Category.assoc] at key
  exact key

/-- **Stalks of the transport.** Let `Θ : Spec k̄₀' ≅ Spec k̄₀` carry the `n`-th power of the
geometric Frobenius of `k̄₀'` to the `r n`-th power of that of `k̄₀`. The stalk of a Weil sheaf `F`
at a geometric point `s` of `Ȳ` with its Frobenius relative to `𝔽_{q^{r n}}` is the stalk of the
transport `(θ_* F̄, θ_* φ_r)` at the geometric point `s'` of `Ȳ'` with `Θ ≫ s = s' ≫ θ⁻¹`, with its
Frobenius relative to `𝔽_{q'ⁿ}`. -/
theorem nonempty_equiv_stalkAt_transport
    (hθ : θ.hom ≫ (Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius.asIso.hom =
      ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ r).asIso.hom ≫ θ.hom)
    (hr : 1 ≤ r) (F : WeilSheaf k₀ l Y)
    (Θ : Spec (.of (AlgebraicClosure k₀')) ≅ Spec (.of (AlgebraicClosure k₀)))
    {s' : Spec (.of (AlgebraicClosure k₀')) ⟶ (Y' ↘ Spec (CommRingCat.of k₀')).geometricFiber}
    {s : Spec (.of (AlgebraicClosure k₀)) ⟶ (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (hsq : Θ.hom ≫ s = s' ≫ θ.inv) {n : ℕ}
    (hΘ : (specGeometricFrobenius k₀' ^ n).asIso.hom ≫ Θ.hom =
      Θ.hom ≫ (specGeometricFrobenius k₀ ^ (r * n)).asIso.hom)
    (hs' : s' ≫ ((Y' ↘ Spec (CommRingCat.of k₀')).geometricGaloisFrobenius ^ n).asIso.hom =
      (specGeometricFrobenius k₀' ^ n).asIso.hom ≫ s')
    (hs : s ≫ ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (r * n)).asIso.hom =
      (specGeometricFrobenius k₀ ^ (r * n)).asIso.hom ≫ s) :
    Nonempty ((F.stalkAt s (r * n) hs).Equiv (((transport θ r hθ).obj F).stalkAt s' n hs')) :=
  nonempty_equiv_stalkAt_of_compatible (G := (transport θ r hθ).obj F)
    (ψ := (ProEtale.upperStarIsoLowerStarInv _ θ.symm).hom.app F.obj.carrier.X)
    (symm_hom_comp_geometricGaloisFrobenius_pow hθ) hr
    (transport_frobeniusStr_compatible hθ F) Θ hsq hΘ hs' hs

end Transport

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] (K : Type u) [Field K] [Finite K]
  [Algebra k₀ K] [Fact (ringChar K ≠ l)]

/-- The restriction of a Weil sheaf punctually `ι`-pure of weight `w` to `X_K` is punctually
`ι`-pure of weight `w`. -/
theorem IsPunctuallyPureOfWeight.baseChangeField {ι : PadicAlgCl l →+* ℂ}
    {F : WeilSheaf k₀ l X} {w : ℝ} (h : F.IsPunctuallyPureOfWeight ι w) :
    ((WeilSheaf.baseChangeField K).obj F).IsPunctuallyPureOfWeight ι w := by
  intro x'
  have hθ := Scheme.Hom.geometricFiberBaseChangeIso_hom_comp_geometricGaloisFrobenius
    (isPullback_baseChangeField (k₀ := k₀) X K) (Module.finrank k₀ K) Module.natCard_eq_pow_finrank
  have hr : 1 ≤ Module.finrank k₀ K := Module.finrank_pos
  -- the image `x` of `x'` in `X`, of degree dividing `[K : k₀] e'`
  have hf := (isPullback_baseChangeField (k₀ := k₀) X K).w.symm
  have hx := Scheme.Hom.map_mem_finitePoints
    (pullback.fst (X ↘ Spec (CommRingCat.of k₀)) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    x'.2
  have hdvd := Scheme.Hom.degreeOver_dvd_degreeOver_comp
    (pullback.fst (X ↘ Spec (CommRingCat.of k₀)) (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))))
    (X ↘ Spec (CommRingCat.of k₀)) x'.2
  rw [Scheme.Hom.degreeOver_eq_finrank_mul_degreeOver _ _ hf x'.2] at hdvd
  -- the geometric points
  have hs' := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X.baseChangeField k₀ K ↘ Spec (CommRingCat.of K)) x'
  have hsq : (specAlgHomAlgebraicClosureIso
      (algebraicClosureAlgEquiv k₀ K).symm.toAlgHom).hom ≫
        ((specAlgHomAlgebraicClosureIso (algebraicClosureAlgEquiv k₀ K).symm.toAlgHom).inv ≫
          (X.baseChangeField k₀ K ↘ Spec (CommRingCat.of K)).geometricFiberPointOfFinitePoint x' ≫
          (Scheme.Hom.geometricFiberBaseChangeIso
            (isPullback_baseChangeField (k₀ := k₀) X K)).inv) =
      (X.baseChangeField k₀ K ↘ Spec (CommRingCat.of K)).geometricFiberPointOfFinitePoint x' ≫
        (Scheme.Hom.geometricFiberBaseChangeIso (isPullback_baseChangeField (k₀ := k₀) X K)).inv :=
    Iso.hom_inv_id_assoc _ _
  have hs := comp_geometricGaloisFrobenius_pow_mul_of_comp_eq _
    (symm_hom_comp_geometricGaloisFrobenius_pow hθ) rfl
    (algebraicClosureAlgEquiv k₀ K).symm.toAlgHom hsq.symm hs'
  have hΘ := specGeometricFrobenius_pow_hom_comp_spec_map_algHom
    (algebraicClosureAlgEquiv k₀ K).symm.toAlgHom
    ((X.baseChangeField k₀ K ↘ Spec (CommRingCat.of K)).degreeOver x'.1)
  obtain ⟨e⟩ := nonempty_equiv_stalkAt_transport hθ hr F _ hsq hΘ hs' hs
  have hproj : (Scheme.Hom.geometricFiberBaseChangeIso
      (isPullback_baseChangeField (k₀ := k₀) X K)).inv ≫
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj =
      (X.baseChangeField k₀ K ↘ Spec (CommRingCat.of K)).geometricFiberProj ≫
        pullback.fst (X ↘ Spec (CommRingCat.of k₀))
          (Spec.map (CommRingCat.ofHom (algebraMap k₀ K))) :=
    Scheme.Hom.geometricFiberBaseChangeInv_comp_geometricFiberProj
      (isPullback_baseChangeField (k₀ := k₀) X K)
  have hb₀ := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base
    (X ↘ Spec (CommRingCat.of k₀)) ⟨_, hx⟩
  have hb : ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint ⟨_, hx⟩ ≫
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      (((specAlgHomAlgebraicClosureIso (algebraicClosureAlgEquiv k₀ K).symm.toAlgHom).inv ≫
          (X.baseChangeField k₀ K ↘ Spec (CommRingCat.of K)).geometricFiberPointOfFinitePoint x' ≫
          (Scheme.Hom.geometricFiberBaseChangeIso
            (isPullback_baseChangeField (k₀ := k₀) X K)).inv) ≫
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiberProj).base
        (IsLocalRing.closedPoint (AlgebraicClosure k₀)) := by
    rw [hb₀, Category.assoc, Category.assoc, hproj, ← Category.assoc
      ((X.baseChangeField k₀ K ↘ Spec (CommRingCat.of K)).geometricFiberPointOfFinitePoint x'),
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact congrArg _ ((Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base
      _ x').symm.trans (congrArg _ (Subsingleton.elim _ _)))
  have hc := F.charpoly_frobeniusEnd_stalkAt_of_dvd _ _ hb (hb₀ ▸ hx) hdvd
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow _ ⟨_, hx⟩) hs
  have hpos : 0 < Module.finrank k₀ K *
      (X.baseChangeField k₀ K ↘ Spec (CommRingCat.of K)).degreeOver x'.1 /
        (X ↘ Spec (CommRingCat.of k₀)).degreeOver (⟨_, hx⟩ : X.finitePoints).1 :=
    Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hr (Nat.pos_of_ne_zero
      (Scheme.Hom.degreeOver_ne_zero _ x'.2))) hdvd)
      (Nat.pos_of_ne_zero (Scheme.Hom.degreeOver_ne_zero _ hx))
  have key := (h ⟨_, hx⟩).of_charpoly_eq_pow hpos (e.charpoly_frobeniusEnd.trans hc)
  rw [Scheme.Hom.residueCard, ← pow_mul, Nat.mul_div_cancel' hdvd, pow_mul,
    ← Module.natCard_eq_pow_finrank] at key
  exact key

end AlgebraicGeometry.WeilSheaf
