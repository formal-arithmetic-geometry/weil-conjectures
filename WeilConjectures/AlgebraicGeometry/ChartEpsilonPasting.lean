/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeneralChartComparisons
public import WeilConjectures.AlgebraicGeometry.ChartDncVectorFactorData
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
import all WeilConjectures.AlgebraicGeometry.DiagonalEtaleRhoUnitSquare
import WeilConjectures.AlgebraicGeometry.DiagonalEtaleLocalityUnitChange
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackDerivedCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence

/-! # Identity and composition of chart epsilon

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-orientation/
sk-prop-sp-orientation-charts.proof.md, Step 3, and exceptional chart mate coherence,
Step 9 (blueprint: lem-pur-chart-epsilon-pasting).

Both equations use the canonical pro-etale pullback constraints and the published
counit-normalized chart comparison, for every compact-support normalization.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option maxRecDepth 4096

universe u

open CategoryTheory AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting.ChartComparisons

private noncomputable abbrev ordinaryEps (P : PurityFiniteSetting.{u})
    {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :=
  let := P.noetherian aV
  let := P.noetherian (B.proj ≫ aV)
  let := P.noetherian (C.proj ≫ aV)
  let := P.noetherian ((e.hom ≫ B.proj) ≫ aV)
  let := Dnc.compactifiable P B.proj aV
  let := Dnc.compactifiable P C.proj aV
  let := Dnc.compactifiable P (e.hom ≫ B.proj) aV
  (P.diagonalDualizingCongr e.over_eq).symm ≪≫
    (P.diagonalEtaleLocality N e.hom B.proj).symm

private theorem ordinaryEps_eq (P : PurityFiniteSetting.{u})
    {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    let := P.noetherian aV
    let := P.noetherian (B.proj ≫ aV)
    let := P.noetherian (C.proj ≫ aV)
    let := Dnc.compactifiable P B.proj aV
    let := Dnc.compactifiable P C.proj aV
    ordinaryEps P aV e N = (OrientationCounit.unitChange P C.proj).symm ≪≫
      (Etale.sectionStructuralLocalityIso P.Coefficient e.hom B.proj C.proj
        e.over_eq).symm ≪≫
      (Etale.ordinaryFinitePullback P.Coefficient e.hom).mapIso
        (OrientationCounit.unitChange P B.proj) := by
  let := P.noetherian aV
  let := P.noetherian (B.proj ≫ aV)
  let := P.noetherian (C.proj ≫ aV)
  let := P.noetherian ((e.hom ≫ B.proj) ≫ aV)
  let := Dnc.compactifiable P B.proj aV
  let := Dnc.compactifiable P C.proj aV
  let := Dnc.compactifiable P (e.hom ≫ B.proj) aV
  have h := P.diagonalEtaleLocality_unitChange N e.hom B.proj C.proj e.over_eq
  have hi := congrArg Iso.symm h
  simp only [Iso.trans_symm] at hi
  have hh := congrArg (fun z ↦ z ≪≫
    (Etale.ordinaryFinitePullback P.Coefficient e.hom).mapIso
      (OrientationCounit.unitChange P B.proj)) hi
  simpa only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl,
    ← Functor.mapIso_trans, Iso.refl_trans, Functor.mapIso_refl] using hh

private theorem ordinaryEps_comp (P : PurityFiniteSetting.{u})
    {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (C B A : Chart V d) (v : Map C B) (e : Map B A)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    let := Dnc.compactifiable P A.proj aV
    ordinaryEps P aV (v.comp e) N ≪≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        v.hom e.hom).app (P.diagonalOrdinaryDualizing A.proj) =
    ordinaryEps P aV v N ≪≫
      (Etale.ordinaryFinitePullback P.Coefficient v.hom).mapIso (ordinaryEps P aV e N) := by
  let := P.noetherian aV
  let := P.noetherian (A.proj ≫ aV)
  let := P.noetherian (B.proj ≫ aV)
  let := P.noetherian (C.proj ≫ aV)
  let := Dnc.compactifiable P A.proj aV
  let := Dnc.compactifiable P B.proj aV
  let := Dnc.compactifiable P C.proj aV
  dsimp only [Map.comp, Etale.ordinaryFinitePullback]
  have h := locality_comp_field P aV v.hom e.hom A.proj B.proj C.proj
    e.over_eq.symm v.over_eq.symm
  rw [ordinaryEps_eq, ordinaryEps_eq, ordinaryEps_eq]
  have hi := congrArg Iso.symm h
  simp only [Iso.trans_symm] at hi
  apply Iso.ext
  have hn := (Etale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} P.Coefficient) v.hom e.hom).hom.naturality
      (OrientationCounit.unitChange P A.proj).hom
  simp only [Functor.comp_map] at hn
  simp only [Etale.ordinaryFinitePullback, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hn]
  have hh := congrArg Iso.hom hi
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.app_inv,
    Functor.mapIso_inv] at hh
  rw [← reassoc_of% hh]

private theorem omegaComparison_congr (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} {g h : X ⟶ Y}
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (w : g = h) :
    let := Dnc.compactifiable P g aY
    let := Dnc.compactifiable P h aY
    (omegaCongr P aY w).symm ≪≫ P.diagonalDualizingComparison g =
      P.diagonalDualizingComparison h ≪≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.mapIso
          (P.diagonalDualizingCongr w).symm := by
  subst h
  simp only [omegaCongr, diagonalDualizingCongr, eqToIso_refl, Iso.refl_symm,
    Iso.refl_trans, Functor.mapIso_refl, Iso.trans_refl]

private theorem eps_compared (P : PurityFiniteSetting.{u})
    {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e : Map C B)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    let := Dnc.compactifiable P B.proj aV
    let := Dnc.compactifiable P C.proj aV
    eps P aV e N = P.diagonalDualizingComparison C.proj ≪≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) C.X).mapDerivedCategory.mapIso
        (ordinaryEps P aV e N) ≪≫
      (Dnc.pullComparison P e.hom (P.diagonalOrdinaryDualizing B.proj)).symm ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e.hom).leftDerivedFunctor.mapIso
        (P.diagonalDualizingComparison B.proj).symm := by
  let := P.noetherian aV
  let := P.noetherian (B.proj ≫ aV)
  let := P.noetherian (C.proj ≫ aV)
  let := P.noetherian ((e.hom ≫ B.proj) ≫ aV)
  let := Dnc.compactifiable P B.proj aV
  let := Dnc.compactifiable P C.proj aV
  let := Dnc.compactifiable P (e.hom ≫ B.proj) aV
  dsimp only [omega]
  simp only [eps, epsilon, ordinaryEps, Functor.mapIso_trans]
  rw [← Iso.trans_assoc, omegaComparison_congr P aV e.over_eq]
  simp only [Iso.trans_assoc]

private theorem transport_pasting {D : Type*} [Category D]
    {X B C E U V W T : D}
    (a : X ≅ B) (b : X ≅ C) (c : C ≅ E) (d : B ≅ E)
    (p : U ≅ B) (q : V ≅ C) (r : W ≅ E) (s : T ≅ W) (t : U ≅ T) (n : V ≅ W)
    (h₁ : a ≪≫ d = b ≪≫ c) (h₂ : p ≪≫ d = t ≪≫ s ≪≫ r)
    (h₃ : n ≪≫ r = q ≪≫ c) :
    a ≪≫ p.symm ≪≫ t = b ≪≫ q.symm ≪≫ n ≪≫ s.symm := by
  apply Iso.ext
  apply (cancel_mono (s.hom ≫ r.hom)).mp
  have hh₁ := congrArg Iso.hom h₁
  have hh₂ := congrArg Iso.hom h₂
  have hh₃ := congrArg Iso.hom h₃
  simp only [Iso.trans_hom] at hh₁ hh₂ hh₃
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← hh₂, Iso.inv_hom_id_assoc, hh₃, Iso.inv_hom_id_assoc]
  exact hh₁

private theorem eps_comp (P : PurityFiniteSetting.{u})
    {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    (C B A : Chart V d) (v : Map C B) (e : Map B A)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    eps P aV (v.comp e) N ≪≫
      (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        v.hom e.hom).app (omega P A.proj aV) = eps P aV v N ≪≫
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v.hom).leftDerivedFunctor.mapIso
        (eps P aV e N) := by
  let := Dnc.compactifiable P A.proj aV
  let := Dnc.compactifiable P B.proj aV
  let := Dnc.compactifiable P C.proj aV
  dsimp only [omega]
  let νC := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) C.X).mapDerivedCategory
  let νB := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) B.X).mapDerivedCategory
  let L := (ProEtale.upperStar
    (ModuleCat.{u + 1} P.Coefficient) v.hom).leftDerivedFunctor
  let K := P.diagonalOrdinaryDualizing A.proj
  let E := (Etale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} P.Coefficient) v.hom e.hom).app K
  let Q := (ProEtale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} P.Coefficient) v.hom e.hom).app
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) A.X).mapDerivedCategory.obj K)
  have h₁ : νC.mapIso (ordinaryEps P aV (v.comp e) N) ≪≫ νC.mapIso E =
      νC.mapIso (ordinaryEps P aV v N) ≪≫
        νC.mapIso ((Etale.ordinaryFinitePullback P.Coefficient v.hom).mapIso
          (ordinaryEps P aV e N)) := by
    simpa only [Functor.mapIso_trans] using
      congrArg νC.mapIso (ordinaryEps_comp P aV C B A v e N)
  have h₂ : Dnc.pullComparison P (v.hom ≫ e.hom) K ≪≫ νC.mapIso E =
      Q ≪≫ L.mapIso (Dnc.pullComparison P e.hom K) ≪≫
        Dnc.pullComparison P v.hom
          ((Etale.ordinaryFinitePullback P.Coefficient e.hom).obj K) := by
    apply Iso.ext
    exact Dnc.pullComparison_comp P v.hom e.hom K
  have h₃ := Dnc.pullComparison_naturality P v.hom (ordinaryEps P aV e N)
  have hp := transport_pasting _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃
  have hc := (ProEtale.leftDerivedUpperStarComp
    (ModuleCat.{u + 1} P.Coefficient) v.hom e.hom).hom.naturality
      (P.diagonalDualizingComparison A.proj).inv
  rw [eps_compared, eps_compared, eps_compared]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp,
    Functor.comp_map, Map.comp, Category.assoc] at hc ⊢
  have hcan := (L.mapIso (P.diagonalDualizingComparison B.proj)).inv_hom_id
  simp only [L, Functor.mapIso_inv, Functor.mapIso_hom] at hcan
  rw [reassoc_of% hcan]
  rw [hc]
  have hh := congrArg Iso.hom hp
  simp only [νC, L, K, Q, Map.comp, ordinaryEps, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom,
    Functor.map_comp, Category.assoc] at hh
  rw [reassoc_of% hh]


private theorem eps_congr (P : PurityFiniteSetting.{u})
    {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    {C B : Chart V d} (e e' : Map C B) (h : e.hom = e'.hom)
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient) :
    eps P aV e N ≪≫
      (ProEtale.leftDerivedUpperStarCongr (ModuleCat.{u + 1} P.Coefficient) h).app
        (omega P B.proj aV) = eps P aV e' N := by
  dsimp only [omega]
  cases e with
  | mk f hf hw =>
    cases e' with
    | mk f' hf' hw' =>
      dsimp only at h
      subst f'
      apply Iso.ext
      simp only [ProEtale.leftDerivedUpperStarCongr_rfl, Iso.trans_hom, Iso.app_hom,
        Iso.refl_hom, NatTrans.id_app, Category.comp_id]

/-- Identity and composition for the canonical chart epsilon, including pullback constraints.
Source: orientation-charts proof, Step 3; exceptional chart mate coherence, Step 9
(blueprint: lem-pur-chart-epsilon-pasting).

Proof: write the ordinary etale part of eps as ordinaryEps, the inverse equality transport
of the diagonal dualizing object followed by inverse normalized structural locality. Invert
the proved structural locality composition (lem-pur-diagonal-etale-rho-unit-square) and
conjugate it by the coefficient-unit change (lem-pur-diagonal-etale-locality-unit-change);
naturality of the ordinary pullback compositor gives composition for ordinaryEps. Rewrite
chart eps as diagonalDualizingComparison, the site comparison applied to ordinaryEps, the
inverse pullComparison and the pulled inverse diagonalDualizingComparison; equality
induction moves omegaCongr past diagonalDualizingComparison. Composition and naturality of
pullComparison (lem-pur-comparison-pullback-derived-coherence) paste the middle squares,
and naturality of the pro-etale compositor cancels the intermediate comparison: this is the
composition law. For identity, apply it to two identity chart maps, identify their
composite with the identity map by equality transport, and use the left unit law of the
pro-etale pullback compositor, naturality of its identity comparison and cancellation of
the invertible eps. No nonemptiness or positive rank is used: rank zero and empty charts
are included, for every finite coefficient extension, positive level and normalization N.
-/
theorem chart_epsilon_pasting (P : PurityFiniteSetting.{u})
    {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    :
    (∀ (C : Chart V d) (N : Etale.EtaleCompactSupportNormalization P.Coefficient),
      eps P aV (Map.id C) N ≪≫
        (ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) C.X).app
          (omega P C.proj aV) = Iso.refl _) ∧
    (∀ (C B A : Chart V d) (v : Map C B) (e : Map B A)
      (N : Etale.EtaleCompactSupportNormalization P.Coefficient),
      eps P aV (v.comp e) N ≪≫
        (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          v.hom e.hom).app (omega P A.proj aV) = eps P aV v N ≪≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v.hom).leftDerivedFunctor.mapIso
          (eps P aV e N)) := by
  dsimp only [omega]
  refine ⟨?_, eps_comp P aV⟩
  intro C N
  let K := P.diagonalDualizing C.proj
  let F := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) (𝟙 C.X)).leftDerivedFunctor
  let a : K ≅ F.obj K := eps P aV (Map.id C) N
  have hg := eps_congr P aV ((Map.id C).comp (Map.id C)) (Map.id C)
    (Category.id_comp (𝟙 C.X)) N
  have h := eps_comp P aV C C C (Map.id C) (Map.id C) N
  have hh := congrArg Iso.hom h
  have hgh := congrArg Iso.hom hg
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at hh hgh
  have hu := ProEtale.leftDerivedUpperStarComp_id_left_app
    (A := ModuleCat.{u + 1} P.Coefficient) (𝟙 C.X) K
  have ht := congrArg (fun z ↦ z ≫
    (ProEtale.leftDerivedUpperStarId
      (ModuleCat.{u + 1} P.Coefficient) C.X).hom.app (F.obj K)) hh
  dsimp only [Map.id, Map.comp, K, F, omega] at ht hu hgh
  rw [Category.assoc, hu, hgh] at ht
  have he : F.map a.hom ≫ (ProEtale.leftDerivedUpperStarId
      (ModuleCat.{u + 1} P.Coefficient) C.X).hom.app (F.obj K) = 𝟙 _ := by
    apply (cancel_epi a.hom).mp
    simpa only [a, F, K, Map.id, omega, Category.assoc, Category.comp_id] using ht.symm
  have hn := (ProEtale.leftDerivedUpperStarId
    (ModuleCat.{u + 1} P.Coefficient) C.X).hom.naturality a.hom
  simp only [Functor.id_map] at hn
  have hi : (ProEtale.leftDerivedUpperStarId
      (ModuleCat.{u + 1} P.Coefficient) C.X).hom.app K ≫ a.hom = 𝟙 _ :=
    hn.symm.trans he
  apply Iso.ext
  change a.hom ≫ (ProEtale.leftDerivedUpperStarId
    (ModuleCat.{u + 1} P.Coefficient) C.X).hom.app K = 𝟙 K
  apply (cancel_mono a.hom).mp
  rw [Category.assoc, hi, Category.comp_id, Category.id_comp]

end WeilConjectures.PurityFiniteSetting.ChartComparisons
