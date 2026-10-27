/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import Sheaf.DeligneLaumon.PoweredPullbackCarrier
public import WeilConjectures.SixFunctors.ProEtale.Adic.OpenImmersion

/-! # Factorization of a return translate through the original equivariant map

Source: the cyclic Frobenius-orbit argument in `sk-i-dl-general-real`.
(blueprint: lem-zl-clopen-return-translate-factor).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Endofunctor
open scoped AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.WeilSheaf

private def shiftIndex (n : ℤ) : ℕ → ℤ
  | 0 => n
  | m + 1 => shiftIndex n m + 1

private theorem shiftIndex_eq (n : ℤ) (m : ℕ) : shiftIndex n m = n + (m : ℤ) := by
  induction m with
  | zero => simp only [shiftIndex, Int.natCast_zero, add_zero]
  | succ m ih => simp only [shiftIndex, ih, Int.natCast_add, Int.natCast_one, add_assoc]

private noncomputable def freePowShiftIso
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (S : ProEtale.AdicSheaf l (X ↘ Spec (.of k)).geometricFiber) (n : ℤ) :
    ∀ m : ℕ,
      (ProEtaleWeilSheaf.frobeniusPowPullback k l X m).obj
          (IsoAlgebra.Free.obj (frobeniusPullback k l X) S n) ≅
        IsoAlgebra.Free.obj (frobeniusPullback k l X) S (shiftIndex n m)
  | 0 => (ProEtale.adicLowerStarCongr l (by rw [pow_zero]; rfl)).app
      (IsoAlgebra.Free.obj (frobeniusPullback k l X) S n) ≪≫
      (ProEtale.adicLowerStarId l _).app _
  | m + 1 =>
      (ProEtale.adicLowerStarCongr l
        (by rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv])).app
          (IsoAlgebra.Free.obj (frobeniusPullback k l X) S n) ≪≫
        (ProEtale.adicLowerStarComp l
          ((X ↘ Spec (.of k)).geometricGaloisFrobenius ^ m).inv
          (X ↘ Spec (.of k)).geometricGaloisFrobenius.inv).symm.app _ ≪≫
        (frobeniusPullback k l X).mapIso (freePowShiftIso S n m) ≪≫
        IsoAlgebra.Free.objSucc (frobeniusPullback k l X) S (shiftIndex n m)

private theorem map_ι_freePowStr
    {k : Type u} [Field k] [Finite k] {l : ℕ} [Fact l.Prime]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (S : ProEtale.AdicSheaf l (X ↘ Spec (.of k)).geometricFiber) (n : ℤ) (m : ℕ) :
    (ProEtaleWeilSheaf.frobeniusPowPullback k l X m).map
        (Sigma.ι (IsoAlgebra.Free.obj (frobeniusPullback k l X) S) n) ≫
        (ProEtaleWeilSheaf.frobeniusPowIso
          (IsoAlgebra.Free.algebra (frobeniusPullback k l X) S) m).hom =
      (freePowShiftIso S n m).hom ≫
        Sigma.ι (IsoAlgebra.Free.obj (frobeniusPullback k l X) S) (shiftIndex n m) := by
  induction m with
  | zero =>
    simp only [ProEtaleWeilSheaf.frobeniusPowIso, freePowShiftIso,
      Iso.trans_hom, Iso.app_hom]
    erw [NatTrans.naturality_assoc, NatTrans.naturality]
    rfl
  | succ m ih =>
    have hs : (frobeniusPullback k l X).map
          (Sigma.ι (IsoAlgebra.Free.obj (frobeniusPullback k l X) S) (shiftIndex n m)) ≫
          (IsoAlgebra.Free.algebra (frobeniusPullback k l X) S).str.hom =
        (IsoAlgebra.Free.objSucc (frobeniusPullback k l X) S (shiftIndex n m)).hom ≫
          Sigma.ι (IsoAlgebra.Free.obj (frobeniusPullback k l X) S)
            (shiftIndex n (m + 1)) :=
      IsoAlgebra.Free.map_ι_comp_str (frobeniusPullback k l X) S (shiftIndex n m)
    simp only [ProEtaleWeilSheaf.frobeniusPowIso, freePowShiftIso,
      Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
    erw [NatTrans.naturality_assoc, NatTrans.naturality_assoc]
    simp only [Functor.comp_map]
    rw [← Functor.map_comp_assoc, ih, Functor.map_comp, Category.assoc, hs]

-- Check the induction with abstract functors before applying it to sheaves.
private theorem factor_return_of_shift
    {B : Type*} [Category B] (E : B ⥤ B) [E.Full] [E.Faithful]
    {W V G : B} (wstr : E.obj W ≅ W) (vstr : E.obj V ≅ V) (gstr : E.obj G ≅ G)
    (i : G ⟶ V) (j : W ⟶ V)
    (hi : E.map i ≫ vstr.hom = gstr.hom ≫ i)
    (hj : E.map j ≫ vstr.hom = wstr.hom ≫ j)
    (r : ℕ) (N : ℤ → B) (b : ∀ n, N n ⟶ W)
    (nextIdx : ℤ → ℤ) (hnext : ∀ n, nextIdx n = n + (r : ℤ))
    (d : ∀ n, E.obj (N n) ≅ N (nextIdx n))
    (hb : ∀ n, E.map (b n) ≫ wstr.hom = (d n).hom ≫ b (nextIdx n))
    (hz : ∃ a : N 0 ⟶ G, b 0 ≫ j = a ≫ i) :
    ∀ m : ℤ, ∃ a : N ((r : ℤ) * m) ⟶ G, b ((r : ℤ) * m) ≫ j = a ≫ i := by
  let T (n : ℤ) : Prop := ∃ a : N n ⟶ G, b n ≫ j = a ≫ i
  have hstep (n : ℤ) : T n ↔ T (nextIdx n) := by
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨(d n).inv ≫ E.map a ≫ gstr.hom, ?_⟩
      apply (cancel_epi (d n).hom).1
      simp only [Iso.hom_inv_id_assoc, Category.assoc]
      calc
        (d n).hom ≫ b (nextIdx n) ≫ j = E.map (b n) ≫ wstr.hom ≫ j := by
          simpa only [Category.assoc] using congrArg (fun t ↦ t ≫ j) (hb n).symm
        _ = E.map (b n ≫ j) ≫ vstr.hom := by
          rw [E.map_comp, Category.assoc, hj]
        _ = E.map (a ≫ i) ≫ vstr.hom := by rw [ha]
        _ = E.map a ≫ gstr.hom ≫ i := by
          rw [E.map_comp, Category.assoc, hi]
    · rintro ⟨a, ha⟩
      refine ⟨E.preimage ((d n).hom ≫ a ≫ gstr.inv), ?_⟩
      apply E.map_injective
      apply (cancel_mono vstr.hom).1
      rw [E.map_comp, E.map_comp, Functor.map_preimage]
      simp only [Category.assoc, hj, hi, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, hb, Category.assoc, ha]
  have hstep' (n : ℤ) : T n ↔ T (n + (r : ℤ)) := by
    simpa only [hnext] using hstep n
  intro m
  change T ((r : ℤ) * m)
  induction m using Int.induction_on with
  | zero => simpa only [mul_zero] using hz
  | succ n ih =>
    simpa only [Int.natCast_add, Int.natCast_one, mul_add, mul_one] using
      (hstep' ((r : ℤ) * n)).mp ih
  | pred n ih =>
    apply (hstep' ((r : ℤ) * (-(n : ℤ) - 1))).mpr
    simpa only [mul_sub, mul_one, sub_add_cancel] using ih

private theorem factor_free_return
    {A B : Type*} [Category A] [Category B]
    (F : A ⥤ A) [F.IsEquivalence] [HasColimitsOfShape (Discrete ℤ) A]
    (H : A ⥤ A) (E : B ⥤ B) [E.IsEquivalence]
    (L : B ⥤ A) (P : A ⥤ B) (adj : L ⊣ P)
    (φ : ∀ K : IsoAlgebra F, H.obj K.carrier ≅ K.carrier)
    (hφ : ∀ {K K' : IsoAlgebra F} (f : K ⟶ K'),
      H.map f.hom.f ≫ (φ K').hom = (φ K).hom ≫ f.hom.f)
    (e : P ⋙ E ≅ H ⋙ P) (r : ℕ)
    (nextIdx : ℤ → ℤ) (hnext : ∀ n, nextIdx n = n + (r : ℤ))
    (ds : ∀ (S : A) (n : ℤ), H.obj (IsoAlgebra.Free.obj F S n) ≅
      IsoAlgebra.Free.obj F S (nextIdx n))
    (hds : ∀ (S : A) (n : ℤ), H.map (Sigma.ι (IsoAlgebra.Free.obj F S) n) ≫
      (φ (IsoAlgebra.Free.algebra F S)).hom =
        (ds S n).hom ≫ Sigma.ι (IsoAlgebra.Free.obj F S) (nextIdx n))
    (V : IsoAlgebra F) (G : IsoAlgebra E) [IsIso (adj.unit.app G.carrier)]
    (s : G.carrier ⟶ P.obj V.carrier)
    (hi : E.map s ≫ (e.app V.carrier ≪≫ P.mapIso (φ V)).hom = G.str.hom ≫ s)
    (m : ℤ) :
    ∃ a : P.obj (IsoAlgebra.Free.obj F (L.obj G.carrier) ((r : ℤ) * m)) ⟶ G.carrier,
      P.map (IsoAlgebra.Free.hom V ((adj.homEquiv G.carrier V.carrier).symm s)
        ((r : ℤ) * m)) = a ≫ s := by
  let S := L.obj G.carrier
  let W := IsoAlgebra.Free.algebra F S
  let t := (adj.homEquiv G.carrier V.carrier).symm s
  let f : W ⟶ V := IsoAlgebra.Free.desc V t
  let j := P.map f.hom.f
  let wstr : E.obj (P.obj W.carrier) ≅ P.obj W.carrier := e.app _ ≪≫ P.mapIso (φ W)
  let vstr : E.obj (P.obj V.carrier) ≅ P.obj V.carrier := e.app _ ≪≫ P.mapIso (φ V)
  let d (n : ℤ) : E.obj (P.obj (IsoAlgebra.Free.obj F S n)) ≅
      P.obj (IsoAlgebra.Free.obj F S (nextIdx n)) := e.app _ ≪≫ P.mapIso (ds S n)
  let b (n : ℤ) := P.map (Sigma.ι (IsoAlgebra.Free.obj F S) n)
  have hj : E.map j ≫ vstr.hom = wstr.hom ≫ j := by
    have hnat : E.map (P.map f.hom.f) ≫ e.hom.app V.carrier =
        (e.app W.carrier).hom ≫ P.map (H.map f.hom.f) := e.hom.naturality f.hom.f
    simp only [wstr, vstr, j, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, Category.assoc]
    rw [reassoc_of% hnat, ← P.map_comp, hφ, P.map_comp]
    rfl
  have hshift (n : ℤ) : E.map (b n) ≫ wstr.hom =
      (d n).hom ≫ b (nextIdx n) := by
    change E.map (P.map _) ≫ e.hom.app W.carrier ≫ P.map (φ W).hom = _
    have hnat : E.map (P.map (Sigma.ι (IsoAlgebra.Free.obj F S) n)) ≫
          e.hom.app W.carrier =
        (e.app _).hom ≫ P.map (H.map (Sigma.ι (IsoAlgebra.Free.obj F S) n)) :=
      e.hom.naturality (Sigma.ι (IsoAlgebra.Free.obj F S) n)
    rw [reassoc_of% hnat, ← P.map_comp, hds, P.map_comp]
    simp only [d, b, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  have hz : ∃ a : P.obj (IsoAlgebra.Free.obj F S 0) ⟶ G.carrier,
      b 0 ≫ j = a ≫ s := by
    refine ⟨inv (adj.unit.app G.carrier), ?_⟩
    apply (cancel_epi (adj.unit.app G.carrier)).1
    simp only [IsIso.hom_inv_id_assoc]
    change adj.unit.app G.carrier ≫ P.map
      (Sigma.ι (IsoAlgebra.Free.obj F S) 0) ≫ P.map f.hom.f = s
    rw [← P.map_comp, IsoAlgebra.Free.ι_desc_hom_f]
    exact (adj.homEquiv G.carrier V.carrier).apply_symm_apply s
  obtain ⟨a, ha⟩ := factor_return_of_shift E wstr vstr G.str
    s j hi hj r (fun n ↦ P.obj (IsoAlgebra.Free.obj F S n)) b
    nextIdx hnext d hshift hz m
  refine ⟨a, ?_⟩
  change P.map (IsoAlgebra.Free.hom V t ((r : ℤ) * m)) = a ≫ s
  rw [← ha]
  change P.map (IsoAlgebra.Free.hom V t ((r : ℤ) * m)) =
    P.map (Sigma.ι (IsoAlgebra.Free.obj F S) ((r : ℤ) * m)) ≫ P.map f.hom.f
  rw [← P.map_comp]
  congr 1
  exact (Sigma.ι_desc _ _).symm

private theorem factor_free_return_lift
    {A B : Type*} [Category A] [Category B]
    (F : A ⥤ A) [F.IsEquivalence] [HasColimitsOfShape (Discrete ℤ) A]
    (H : A ⥤ A) (E : B ⥤ B) [E.IsEquivalence]
    (L : B ⥤ A) (P : A ⥤ B) (adj : L ⊣ P)
    (φ : ∀ K : IsoAlgebra F, H.obj K.carrier ≅ K.carrier)
    (hφ : ∀ {K K' : IsoAlgebra F} (f : K ⟶ K'),
      H.map f.hom.f ≫ (φ K').hom = (φ K).hom ≫ f.hom.f)
    (e : P ⋙ E ≅ H ⋙ P) (r : ℕ)
    (nextIdx : ℤ → ℤ) (hnext : ∀ n, nextIdx n = n + (r : ℤ))
    (ds : ∀ (S : A) (n : ℤ), H.obj (IsoAlgebra.Free.obj F S n) ≅
      IsoAlgebra.Free.obj F S (nextIdx n))
    (hds : ∀ (S : A) (n : ℤ), H.map (Sigma.ι (IsoAlgebra.Free.obj F S) n) ≫
      (φ (IsoAlgebra.Free.algebra F S)).hom =
        (ds S n).hom ≫ Sigma.ι (IsoAlgebra.Free.obj F S) (nextIdx n))
    (V : IsoAlgebra F) (G : IsoAlgebra E) [IsIso (adj.unit.app G.carrier)]
    (i : G ⟶ (IsoAlgebra.liftOfStr H φ hφ ⋙ IsoAlgebra.mapOfNatIso e).obj V)
    (m : ℤ) :
    ∃ a : P.obj (IsoAlgebra.Free.obj F (L.obj G.carrier) ((r : ℤ) * m)) ⟶ G.carrier,
      P.map (IsoAlgebra.Free.hom V
        ((adj.homEquiv G.carrier V.carrier).symm i.hom.f) ((r : ℤ) * m)) =
        a ≫ i.hom.f := by
  have hi : E.map i.hom.f ≫ (e.app V.carrier ≪≫ P.mapIso (φ V)).hom =
      G.str.hom ≫ i.hom.f := by
    have h := i.hom.h
    change E.map i.hom.f ≫
      ((IsoAlgebra.liftOfStr H φ hφ ⋙ IsoAlgebra.mapOfNatIso e).obj V).str.hom =
        G.str.hom ≫ i.hom.f at h
    rw [IsoAlgebra.liftOfStr_comp_mapOfNatIso_obj_str] at h
    exact h
  exact factor_free_return F H E L P adj φ hφ e r nextIdx hnext ds hds
    V G i.hom.f hi m

-- Keep the functor and its carrier comparison as arguments of one proposition.
-- Specialize this proposition before evaluating it at a concrete algebra map.
private def ReturnFactors
    {A B : Type*} [Category A] [Category B]
    (F : A ⥤ A) [F.IsEquivalence] [HasColimitsOfShape (Discrete ℤ) A]
    (E : B ⥤ B) (L : B ⥤ A) (P : A ⥤ B) (adj : L ⊣ P) (r : ℕ)
    (Q : IsoAlgebra F ⥤ IsoAlgebra E)
    (κ : Q ⋙ IsoAlgebra.forget E ≅ IsoAlgebra.forget F ⋙ P) : Prop :=
  ∀ (V : IsoAlgebra F) (G : IsoAlgebra E) [IsIso (adj.unit.app G.carrier)]
    (i : G ⟶ Q.obj V) (m : ℤ),
    ∃ a : P.obj (IsoAlgebra.Free.obj F (L.obj G.carrier) ((r : ℤ) * m)) ⟶ G.carrier,
      P.map (IsoAlgebra.Free.hom V
        ((adj.homEquiv G.carrier V.carrier).symm (i.hom.f ≫ κ.hom.app V))
          ((r : ℤ) * m)) = a ≫ i.hom.f ≫ κ.hom.app V

private theorem factor_free_return_lift_property
    {A B : Type*} [Category A] [Category B]
    (F : A ⥤ A) [F.IsEquivalence] [HasColimitsOfShape (Discrete ℤ) A]
    (H : A ⥤ A) (E : B ⥤ B) [E.IsEquivalence]
    (L : B ⥤ A) (P : A ⥤ B) (adj : L ⊣ P)
    (φ : ∀ K : IsoAlgebra F, H.obj K.carrier ≅ K.carrier)
    (hφ : ∀ {K K' : IsoAlgebra F} (f : K ⟶ K'),
      H.map f.hom.f ≫ (φ K').hom = (φ K).hom ≫ f.hom.f)
    (e : P ⋙ E ≅ H ⋙ P) (r : ℕ)
    (nextIdx : ℤ → ℤ) (hnext : ∀ n, nextIdx n = n + (r : ℤ))
    (ds : ∀ (S : A) (n : ℤ), H.obj (IsoAlgebra.Free.obj F S n) ≅
      IsoAlgebra.Free.obj F S (nextIdx n))
    (hds : ∀ (S : A) (n : ℤ), H.map (Sigma.ι (IsoAlgebra.Free.obj F S) n) ≫
      (φ (IsoAlgebra.Free.algebra F S)).hom =
        (ds S n).hom ≫ Sigma.ι (IsoAlgebra.Free.obj F S) (nextIdx n))
 :
    ReturnFactors F E L P adj r
      (IsoAlgebra.liftOfStr H φ hφ ⋙ IsoAlgebra.mapOfNatIso e) (Iso.refl _) := by
  unfold ReturnFactors
  intro V G hunit i m
  simpa only [Iso.refl_hom, NatTrans.id_app, Functor.comp_obj,
    IsoAlgebra.forget_obj, IsoAlgebra.mapOfNatIso_obj_carrier,
    IsoAlgebra.liftOfStr_obj_carrier, Category.comp_id] using
    factor_free_return_lift F H E L P adj φ hφ e r nextIdx hnext ds hds V G i m

private theorem return_factor_property
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X C : Scheme.{u}} [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
    (v : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    [IsOpenImmersion v] (r : ℕ)
    (hv : (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom ≫ v =
      v ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom)
 :
    ReturnFactors (frobeniusPullback k₀ l X) (frobeniusPullback k₁ l C)
      (v)_!ᵃ[l] (v)^*ᵃ[l] (ProEtale.adicOpenImmersionLowerShriekAdjunction l v) r
      (poweredGeometricPullbackAll v r hv) (poweredPullbackAllCarrierIso v r hv) := by
  unfold poweredPullbackAllCarrierIso poweredGeometricPullbackAll
    ProEtaleWeilSheaf.powFunctor
  exact factor_free_return_lift_property
    (frobeniusPullback k₀ l X) (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r)
    (frobeniusPullback k₁ l C) (v)_!ᵃ[l] (v)^*ᵃ[l]
    (ProEtale.adicOpenImmersionLowerShriekAdjunction l v)
    (fun K ↦ ProEtaleWeilSheaf.frobeniusPowIso K r)
    (fun f ↦ ProEtaleWeilSheaf.frobeniusPowIso_hom_naturality f r)
    (poweredGeometricPullbackCommIso (l := l) v r hv) r
    (fun n ↦ shiftIndex n r) (fun n ↦ shiftIndex_eq n r)
    (fun S n ↦ freePowShiftIso S n r) (fun S n ↦ map_ι_freePowStr S n r)

/-- An integral return translate of the adjoint map factors through the original map.
Source: `sk-i-dl-general-real`, geometric-socle/Frobenius orbit step, as used in
`lem-zl-clopen-return-saturation-epi`, proof step 2.

Proof: inverse image along `v` commutes with the `r`th Frobenius pullback by `hv`.
Iterate this comparison for positive returns, and its inverse for negative
returns. Under these comparisons the `rm`th free map is the `m`th Frobenius
translate of the original adjoint map followed by the iterated ambient Weil
structure. The adjunction unit identifies restriction of extension by zero
with `G.carrier`. Naturality of the iterated comparison, the adjunction
triangle, and equivariance of `i` identify the restricted map with a map to
`G.carrier` followed by the carrier of `i`. The map to `G.carrier` is obtained
from the corresponding iterate of its invertible Weil structure. For `m = 0`
it is the inverse adjunction unit. No monicity of `i`, or assumption on the
other sheets, is needed.
(blueprint: lem-zl-clopen-return-translate-factor). -/
theorem clopen_return_freeHom_factor
    {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
    {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
    {X C : Scheme.{u}} [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]
    (v : (C ↘ Spec (.of k₁)).geometricFiber ⟶ (X ↘ Spec (.of k₀)).geometricFiber)
    [IsOpenImmersion v] (r : ℕ)
    (hv : (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom ≫ v =
      v ≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom)
    (V : ProEtaleWeilSheaf k₀ l X) (G : ProEtaleWeilSheaf k₁ l C)
    (i : G ⟶ (poweredGeometricPullbackAll v r hv).obj V) (m : ℤ) :
    ∃ a : (v)^*ᵃ[l].obj
        (IsoAlgebra.Free.obj (frobeniusPullback k₀ l X) ((v)_!ᵃ[l].obj G.carrier)
          ((r : ℤ) * m)) ⟶ G.carrier,
      (v)^*ᵃ[l].map
          (IsoAlgebra.Free.hom V
            (((ProEtale.adicOpenImmersionLowerShriekAdjunction l v).homEquiv
              G.carrier V.carrier).symm
                (i.hom.f ≫ (poweredPullbackAllCarrierIso v r hv).hom.app V))
            ((r : ℤ) * m)) =
        a ≫ i.hom.f ≫ (poweredPullbackAllCarrierIso v r hv).hom.app V := by
  exact return_factor_property v r hv V G i m

end AlgebraicGeometry.WeilSheaf
