/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.TraceFormulaCoefficientConventions.TraceFormulaFrobeniusOperators
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtalePullbackStalkCoherence
public import WeilConjectures.AlgebraicGeometry.Picard.CondensedFrobeniusOperators.TraceFormulaSchemeGaloisComparison

/-!
# Coherence of fixed-point Frobenius stalk transport

Source: latest blueprint, `lem-trf-frobenius-degree-formula.proof.md`, Step 1,
iteration at one lift (blueprint: lem-trf-fixed-point-transport-coherence).
The stalk convention is point sections after derived pullback. The equality is an
identity of natural isomorphisms on strict Weil complexes, so it includes naturality
in every morphism of strict Weil complexes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralReductionSiteEssentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilConjectures.CondensedFrobeniusOperators

open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

private theorem fixed_compositor_generic
    {B : Type*} [Category B] {D₀ : B → Type*} [∀ X, Category (D₀ X)]
    (P : ∀ {X Y : B}, (X ⟶ Y) → D₀ Y ⥤ D₀ X)
    (c : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {T X : B} (z : T ⟶ X) (f g h : X ⟶ X) (hfg : f ≫ g = h)
    (hzf : z ≫ f = z) (hzg : z ≫ g = z) (hzh : z ≫ h = z)
    (K : D₀ X)
    (hc : (c (z ≫ f) g).hom.app K ≫ (c z f).hom.app ((P g).obj K) =
      eqToHom (congrArg (fun w ↦ (P w).obj K) (Category.assoc z f g)) ≫
        (c z (f ≫ g)).hom.app K ≫ (P z).map ((c f g).hom.app K)) :
    (eqToIso (congrArg (fun w ↦ P w) hzh)).inv.app K ≫
        (c z h).hom.app K ≫
        (P z).map ((eqToIso (congrArg (fun w ↦ P w) hfg)).inv.app K ≫
          (c f g).hom.app K) =
      (eqToIso (congrArg (fun w ↦ P w) hzg)).inv.app K ≫
        (c z g).hom.app K ≫
        (eqToIso (congrArg (fun w ↦ P w) hzf)).inv.app ((P g).obj K) ≫
        (c z f).hom.app ((P g).obj K) := by
  subst h
  have ht := eqToHom_iso_hom_naturality
    (fun w : T ⟶ X ↦ (c w g).app K) hzf.symm
  simp only [eqToIso.inv, eqToHom_app, eqToHom_refl, NatTrans.id_app,
    Category.id_comp] at *
  simp only [Iso.app_hom] at ht ⊢
  rw [reassoc_of% ht]
  rw [hc]
  simp only [← Category.assoc, eqToHom_trans]


-- Substitute the multiplicative comparison and move it past the point identification.

private theorem comparison_transport_generic
    {C D : Type*} [Category C] [Category D]
    (S : C ⥤ D) (A B H A' B' H' : C ⥤ C)
    (ρa : S ≅ A ⋙ S) (ρb : S ≅ B ⋙ S) (ρh : S ≅ H ⋙ S)
    (κa : A ≅ A') (κb : B ≅ B') (κh : H ≅ H')
    (cP : H ≅ A ⋙ B) (cG : H' ≅ A' ⋙ B') (K : C)
    (hc : ρh.hom.app K ≫ S.map (cP.hom.app K) =
      ρa.hom.app K ≫ ρb.hom.app (A.obj K))
    (hκ : κh.hom.app K = cP.hom.app K ≫ κb.hom.app (A.obj K) ≫
      B'.map (κa.hom.app K) ≫ cG.inv.app K) :
    ρh.hom.app K ≫ S.map (κh.hom.app K) =
      (ρa.hom.app K ≫ S.map (κa.hom.app K)) ≫
        (ρb.hom.app (A'.obj K) ≫ S.map (κb.hom.app (A'.obj K))) ≫
          S.map (cG.inv.app K) := by
  rw [hκ]
  simp only [Functor.map_comp, ← Category.assoc]
  rw [hc]
  have hb := congrArg S.map (κb.hom.naturality (κa.hom.app K))
  simp only [Functor.map_comp] at hb
  simp only [Category.assoc]
  rw [← reassoc_of% hb]
  have hr := ρb.hom.naturality (κa.hom.app K)
  simp only [Functor.comp_map] at hr
  rw [← reassoc_of% hr]

private theorem transport_sections_generic
    {C D E : Type*} [Category C] [Category D] [Category E]
    (S : C ⥤ D) (Q : D ⥤ E) (A B H A' B' H' : C ⥤ C)
    (Ra Rb Rh : C ⥤ D)
    (ea : S ≅ Ra) (eb : S ≅ Rb) (eh : S ≅ Rh)
    (ca : Ra ≅ A ⋙ S) (cb : Rb ≅ B ⋙ S) (ch : Rh ≅ H ⋙ S)
    (κa : A ≅ A') (κb : B ≅ B') (κh : H ≅ H')
    (dG : H' ≅ A' ⋙ B')
    (h : ∀ K, (eh ≪≫ ch).hom.app K ≫ S.map (κh.hom.app K) =
      ((ea ≪≫ ca).hom.app K ≫ S.map (κa.hom.app K)) ≫
        ((eb ≪≫ cb).hom.app (A'.obj K) ≫ S.map (κb.hom.app (A'.obj K))) ≫
          S.map (dG.inv.app K)) :
    (Functor.isoWhiskerRight (eh ≪≫ ch ≪≫ Functor.isoWhiskerRight κh S) Q ≪≫
      Functor.associator H' S Q) =
    (Functor.isoWhiskerRight (ea ≪≫ ca ≪≫ Functor.isoWhiskerRight κa S) Q ≪≫
      Functor.associator A' S Q) ≪≫
      Functor.isoWhiskerLeft A'
        (Functor.isoWhiskerRight (eb ≪≫ cb ≪≫ Functor.isoWhiskerRight κb S) Q ≪≫
          Functor.associator B' S Q) ≪≫
      (Functor.associator A' B' (S ⋙ Q)).symm ≪≫
      Functor.isoWhiskerRight dG.symm (S ⋙ Q) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.comp_map,
    Functor.map_comp, Category.comp_id, Category.id_comp, Category.assoc] using
      congrArg Q.map (h K)

private theorem fixed_compositor_iso_generic
    {B : Type*} [Category B] {D₀ : B → Type*} [∀ X, Category (D₀ X)]
    (P : ∀ {X Y : B}, (X ⟶ Y) → D₀ Y ⥤ D₀ X)
    (c : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {T X : B} (z : T ⟶ X) (f g h : X ⟶ X) (hfg : f ≫ g = h)
    (hzf : z ≫ f = z) (hzg : z ≫ g = z) (hzh : z ≫ h = z)
    (K : D₀ X)
    (hc : (c (z ≫ f) g).hom.app K ≫ (c z f).hom.app ((P g).obj K) =
      eqToHom (congrArg (fun w ↦ (P w).obj K) (Category.assoc z f g)) ≫
        (c z (f ≫ g)).hom.app K ≫ (P z).map ((c f g).hom.app K)) :
    ((eqToIso (congrArg (fun w ↦ P w) hzh)).symm ≪≫ c z h).hom.app K ≫
        (P z).map (((eqToIso (congrArg (fun w ↦ P w) hfg.symm)) ≪≫
          c f g).hom.app K) =
      ((eqToIso (congrArg (fun w ↦ P w) hzg)).symm ≪≫ c z g).hom.app K ≫
        ((eqToIso (congrArg (fun w ↦ P w) hzf)).symm ≪≫ c z f).hom.app
          ((P g).obj K) := by
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom,
    eqToIso.inv, Category.assoc] using
      fixed_compositor_generic P c z f g h hfg hzf hzg hzh K hc

private theorem fixed_compositor_nat_generic
    {B : Type*} [Category B] {D₀ : B → Type*} [∀ X, Category (D₀ X)]
    (P : ∀ {X Y : B}, (X ⟶ Y) → D₀ Y ⥤ D₀ X)
    (c : ∀ {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z), P (f ≫ g) ≅ P g ⋙ P f)
    {T X : B} (z : T ⟶ X) (f g h : X ⟶ X) (hfg : f ≫ g = h)
    (hzf : z ≫ f = z) (hzg : z ≫ g = z) (hzh : z ≫ h = z)
    (hc : ∀ K, (c (z ≫ f) g).hom.app K ≫ (c z f).hom.app ((P g).obj K) =
      eqToHom (congrArg (fun w ↦ (P w).obj K) (Category.assoc z f g)) ≫
        (c z (f ≫ g)).hom.app K ≫ (P z).map ((c f g).hom.app K)) :
    ((eqToIso (congrArg (fun w ↦ P w) hzh)).symm ≪≫ c z h).hom ≫
        Functor.whiskerRight ((eqToIso (congrArg (fun w ↦ P w) hfg.symm)) ≪≫
          c f g).hom (P z) =
      ((eqToIso (congrArg (fun w ↦ P w) hzg)).symm ≪≫ c z g).hom ≫
        Functor.whiskerLeft (P g)
          ((eqToIso (congrArg (fun w ↦ P w) hzf)).symm ≪≫ c z f).hom ≫
        (Functor.associator (P g) (P f) (P z)).inv := by
  ext K
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.comp_id] using
      fixed_compositor_iso_generic P c z f g h hfg hzf hzg hzh K (hc K)

private theorem transport_all_generic
    {C D E : Type*} [Category C] [Category D] [Category E]
    (S : C ⥤ D) (Q : D ⥤ E) (A B H A' B' H' : C ⥤ C)
    (Ra Rb Rh : C ⥤ D)
    (ea : S ≅ Ra) (eb : S ≅ Rb) (eh : S ≅ Rh)
    (ca : Ra ≅ A ⋙ S) (cb : Rb ≅ B ⋙ S) (ch : Rh ≅ H ⋙ S)
    (κa : A ≅ A') (κb : B ≅ B') (κh : H ≅ H')
    (dP : H ≅ A ⋙ B) (dG : H' ≅ A' ⋙ B')
    (hc : (eh ≪≫ ch).hom ≫ Functor.whiskerRight dP.hom S =
      (ea ≪≫ ca).hom ≫ Functor.whiskerLeft A (eb ≪≫ cb).hom ≫
        (Functor.associator A B S).inv)
    (hk : κh.hom = dP.hom ≫ Functor.whiskerLeft A κb.hom ≫
      Functor.whiskerRight κa.hom B' ≫ dG.inv) :
    (Functor.isoWhiskerRight (eh ≪≫ ch ≪≫ Functor.isoWhiskerRight κh S) Q ≪≫
      Functor.associator H' S Q) =
    (Functor.isoWhiskerRight (ea ≪≫ ca ≪≫ Functor.isoWhiskerRight κa S) Q ≪≫
      Functor.associator A' S Q) ≪≫
      Functor.isoWhiskerLeft A'
        (Functor.isoWhiskerRight (eb ≪≫ cb ≪≫ Functor.isoWhiskerRight κb S) Q ≪≫
          Functor.associator B' S Q) ≪≫
      (Functor.associator A' B' (S ⋙ Q)).symm ≪≫
      Functor.isoWhiskerRight dG.symm (S ⋙ Q) := by
  apply transport_sections_generic
  intro K
  apply comparison_transport_generic S A B H A' B' H'
    (ea ≪≫ ca) (eb ≪≫ cb) (eh ≪≫ ch) κa κb κh dP dG K
  · simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Category.comp_id] using NatTrans.congr_app hc K
  · simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] using
      NatTrans.congr_app hk K

/-- Clause (2) of the Frobenius-operator definition at an arbitrary fixed geometric
point, as a natural isomorphism in the underlying coefficient complex. This is the
same construction as `fixedPointReturn`, now before choosing a rational-point
presentation or a Weil structure. The three factors are the fixed-point equality,
the canonical derived pullback compositor, and the specified scheme/Galois comparison;
point sections then give the stalk coefficient complex.

Source: latest blueprint, `def-trf-frobenius-operators.md`, clause (2), and
`lem-trf-frobenius-degree-formula.proof.md`, Step 1
(blueprint: lem-trf-fixed-point-transport-coherence). -/
def fixedPointStalkTransport
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n)
    (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left)
    (m : ℕ) (hm : 1 ≤ m) (hz : z ≫ F.coefficientFreeSchemeFrobeniusIterate Y₀ m = z) :
    L (finiteCoefficient ell E n) z ⋙ Γ (finiteCoefficient ell E n) (Spec (.of F.k)) ≅
      L (finiteCoefficient ell E n)
          ((condensedFrobeniusGeometry F Y₀).h.pow m).hom ⋙
        (L (finiteCoefficient ell E n) z ⋙
          Γ (finiteCoefficient ell E n) (Spec (.of F.k))) :=
  let Λ := finiteCoefficient ell E n
  Functor.isoWhiskerRight
      ((eqToIso (congrArg (L Λ) hz)).symm ≪≫
        leftDerivedUpperStarComp Λ z (F.coefficientFreeSchemeFrobeniusIterate Y₀ m) ≪≫
        Functor.isoWhiskerRight
          (finiteSchemeGaloisComparisonFunctor F Y₀ ell E n hn m hm) (L Λ z))
      (Γ Λ (Spec (.of F.k))) ≪≫
    Functor.associator
      (L Λ ((condensedFrobeniusGeometry F Y₀).h.pow m).hom)
      (L Λ z) (Γ Λ (Spec (.of F.k)))

/-- The transport at `a+b` is transport at `a`, transport at `b` evaluated on the
`a`-fold pulled-back complex, and the canonical Galois pullback compositor. Equality
of natural isomorphisms after the strict-Weil forgetful functor states the equation
for every strict Weil complex and its naturality for every strict Weil morphism.
The second transport uses only the underlying pulled-back complex, as in the
construction of `fixedPointReturn`; it does not require choosing a new Weil map.

Source: latest blueprint, `lem-trf-frobenius-degree-formula.proof.md`, Step 1
(blueprint: lem-trf-fixed-point-transport-coherence).

Proof: write `P_m = L(Phi^m)^*`, `G_m = L(g^m)^*`, and `S = Fib_s Lz^*`.
The fixed-point transport is `tau_m = S(kappa_m) rho_m`. Pullback associativity at
`z, Phi^b, Phi^a`, using the three fixed-point equalities, gives
`rho_(a+b) = S(C_P) rho_b(P_a(-)) rho_a`. The normalized multiplicative comparison
says `kappa_(a+b) C_P = C_G kappa_b(G_a(-)) P_b(kappa_a)`.
Substitute the first equation in `tau_(a+b)`, then the second. Naturality of
`rho_b` at `kappa_a` moves `P_b(kappa_a)` across `rho_b`, leaving
`S(C_G) tau_b(G_a(-)) tau_a`. All factors are natural isomorphisms; precomposing
with the strict-Weil forgetful functor gives exactly the claimed natural identity.
The compositors are the normalized derived pullback comparisons, not chosen maps. -/
theorem fixedPointStalkTransport_add
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (Y₀ : Over (Spec (CommRingCat.of F.k₀))) [IsSeparated Y₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ F.p) (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E]
    (n : ℕ) (hn : 1 ≤ n)
    (z : Spec (.of F.k) ⟶ (F.geometricFiber Y₀).left)
    (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hza : z ≫ F.coefficientFreeSchemeFrobeniusIterate Y₀ a = z)
    (hzb : z ≫ F.coefficientFreeSchemeFrobeniusIterate Y₀ b = z)
    (hzab : z ≫ F.coefficientFreeSchemeFrobeniusIterate Y₀ (a + b) = z) :
    let Λ := finiteCoefficient ell E n
    let G := fun m ↦ ((condensedFrobeniusGeometry F Y₀).h.pow m).hom
    let S := L Λ z ⋙ Γ Λ (Spec (.of F.k))
    let W := FiniteStrictWeilComplex.forget (F := F) (Y₀ := Y₀)
      (ell := ell) (E := E) (n := n) (hn := hn)
    let τ := fun m hm hz ↦ fixedPointStalkTransport F Y₀ ell E n hn z m hm hz
    ∃ hG : G b ≫ G a = G (a + b),
      Functor.isoWhiskerLeft W (τ (a + b) (by omega) hzab) =
        Functor.isoWhiskerLeft W
          (τ a ha hza ≪≫
            Functor.isoWhiskerLeft (L Λ (G a)) (τ b hb hzb) ≪≫
            (Functor.associator (L Λ (G a)) (L Λ (G b)) S).symm ≪≫
            Functor.isoWhiskerRight
              ((leftDerivedUpperStarComp Λ (G b) (G a)).symm ≪≫
                eqToIso (congrArg (L Λ) hG)) S) := by
  let Λ := finiteCoefficient ell E n
  let P := fun j ↦ F.coefficientFreeSchemeFrobeniusIterate Y₀ j
  let G := fun j ↦ ((condensedFrobeniusGeometry F Y₀).h.pow j).hom
  let κ := fun j hj ↦ finiteSchemeGaloisComparisonFunctor F Y₀ ell E n hn j hj
  let family (s : ℕ) : Prop :=
    ∃ hs : 1 ≤ s, ∃ hP : P b ≫ P a = P s, ∃ hG : G b ≫ G a = G s,
      (κ s hs).hom = eqToHom (congrArg (L Λ) hP.symm) ≫
        (leftDerivedUpperStarComp Λ (P b) (P a)).hom ≫
        Functor.whiskerLeft (L Λ (P a)) (κ b hb).hom ≫
        Functor.whiskerRight (κ a ha).hom (L Λ (G b)) ≫
        (leftDerivedUpperStarComp Λ (G b) (G a)).inv ≫
        eqToHom (congrArg (L Λ) hG)
  have h : family (b + a) := by
    obtain ⟨hP, hG, hκ⟩ :=
      finiteSchemeGaloisComparison_add F Y₀ ell _hEll E n hn b a hb ha
    exact ⟨by omega, hP, hG, hκ⟩
  have h' : family (a + b) := Eq.mp (congrArg family (Nat.add_comm b a)) h
  obtain ⟨hab, hP, hG, hκ⟩ := h'
  refine ⟨hG, ?_⟩
  apply congrArg (Functor.isoWhiskerLeft _)
  let ρ := fun j (hz : z ≫ P j = z) ↦
    (eqToIso (congrArg (L Λ) hz)).symm ≪≫ leftDerivedUpperStarComp Λ z (P j)
  let cP := eqToIso (congrArg (L Λ) hP.symm) ≪≫
    leftDerivedUpperStarComp Λ (P b) (P a)
  let cG := eqToIso (congrArg (L Λ) hG.symm) ≪≫
    leftDerivedUpperStarComp Λ (G b) (G a)
  have hc : (ρ (a + b) hzab).hom ≫ Functor.whiskerRight cP.hom (L Λ z) =
      (ρ a hza).hom ≫ Functor.whiskerLeft (L Λ (P a)) (ρ b hzb).hom ≫
        (Functor.associator (L Λ (P a)) (L Λ (P b)) (L Λ z)).inv := by
    exact fixed_compositor_nat_generic (D₀ := D Λ) (fun {_ _} f ↦ L Λ f)
      (fun f g ↦ leftDerivedUpperStarComp Λ f g) z (P b) (P a) (P (a + b))
      hP hzb hza hzab (fun K ↦ leftDerivedUpperStarComp_assoc_app Λ z (P b) (P a) K)
  have hk : (κ (a + b) (by omega)).hom = cP.hom ≫
      Functor.whiskerLeft (L Λ (P a)) (κ b hb).hom ≫
      Functor.whiskerRight (κ a ha).hom (L Λ (G b)) ≫ cG.inv := by
    simp only [cP, cG, Iso.trans_hom, Iso.trans_inv, eqToIso.hom,
      eqToIso.inv, Category.assoc]
    exact hκ
  exact transport_all_generic (L Λ z) (Γ Λ (Spec (.of F.k)))
    (L Λ (P a)) (L Λ (P b)) (L Λ (P (a + b)))
    (L Λ (G a)) (L Λ (G b)) (L Λ (G (a + b)))
    (L Λ (z ≫ P a)) (L Λ (z ≫ P b)) (L Λ (z ≫ P (a + b)))
    (eqToIso (congrArg (L Λ) hza)).symm
    (eqToIso (congrArg (L Λ) hzb)).symm
    (eqToIso (congrArg (L Λ) hzab)).symm
    (leftDerivedUpperStarComp Λ z (P a))
    (leftDerivedUpperStarComp Λ z (P b))
    (leftDerivedUpperStarComp Λ z (P (a + b)))
    (κ a ha) (κ b hb) (κ (a + b) (by omega)) cP cG hc hk

end WeilConjectures.CondensedFrobeniusOperators
