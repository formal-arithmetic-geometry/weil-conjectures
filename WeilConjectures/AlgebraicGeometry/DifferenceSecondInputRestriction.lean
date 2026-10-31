/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineDifferenceTowerFactorization
public import WeilConjectures.AlgebraicGeometry.DifferenceFirstInputRestriction
import WeilConjectures.AlgebraicGeometry.DualizingSigmaCocycleLocality
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-! # Difference-coordinate second input restriction

Source: composition coherence Step 1
(blueprint: lem-pur-difference-second-input-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.DifferenceCoordinateSection
open WeilConjectures.PurityFiniteSetting.DiagonalPasting
open AlgebraicGeometry.AffineDifferenceTower
open FiniteEtaleNormalization

private theorem normalized_base_change
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y X₀ Y₀ U U₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [U₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (U₀ ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    (h₀ : X₀ ⟶ Y₀) [h₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₀] [LocallyOfFiniteType h₀] [QuasiCompact h₀]
    (dh₀ : ℕ) [SmoothOfRelativeDimension dh₀ h₀]
    (v : Y₀ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (u : X₀ ⟶ X) [u.IsOver (Spec (.of P.field.k))]
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    (e₀ : U₀ ⟶ X₀) [e₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated e₀] [LocallyOfFiniteType e₀] [QuasiCompact e₀]
    [Etale e₀]
    (u₁ : U₀ ⟶ U) [u₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₁] [LocallyOfFiniteType u₁] [QuasiCompact u₁]
    (sqh : IsPullback u h₀ h v) (sqe : IsPullback u₁ e₀ e u)
    (p : U ⟶ Y) [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    (p₀ : U₀ ⟶ Y₀) [IsSeparated p₀] [LocallyOfFiniteType p₀] [QuasiCompact p₀]
    [HasCompactification h] [HasCompactification h₀]
    [HasCompactification p] [HasCompactification p₀]
    (hp : p = e ≫ h) (hp₀ : p₀ = e₀ ≫ h₀)
    (sqp : IsPullback u₁ p₀ p v) :
    Etale.dualizingComplexBaseChangeMap P.Coefficient sqp ≫
        (normalizedE P e₀ h₀ p₀ hp₀ (Y₀ ↘ Spec (.of P.field.k))).hom =
      (pull P u₁).map (normalizedE P e h p hp (Y ↘ Spec (.of P.field.k))).hom ≫
        (DualizingLocality.pullSquare P u₁ e₀ e u sqe.toCommSq).hom.app (omega P h) ≫
        (pull P e₀).map (Etale.dualizingComplexBaseChangeMap P.Coefficient sqh) := by
  subst p
  subst p₀
  have hb := (DualizingLocality.dualizing_sigma_cocycle_locality P).2.2.2.1
    h dh h₀ dh₀ v u e e₀ u₁ sqh sqe
  simp only [normalizedE, Iso.trans_hom, Iso.app_hom, FiniteEtaleNormalization.congr,
    Etale.unboundedEtaleLowerShriekCongr, conjugateIsoEquiv_apply_hom, Iso.refl_hom,
    conjugateEquiv_id, NatTrans.id_app, FiniteEtaleNormalization.beta, baseChange,
    Etale.dualizingComplexBaseChangeMap, exceptional, coefficientUnit, omega,
    Category.assoc] at hb ⊢
  erw [Category.id_comp, Category.id_comp]
  exact hb

private theorem section_pullSquare
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U V Q D B C : Scheme.{u}}
    (f : U ⟶ V) (δ : V ⟶ D) (s : U ⟶ Q) (j : Q ⟶ D)
    (G : Q ⟶ B) (E : D ⟶ C) (v : B ⟶ C) (zU : U ⟶ B) (zV : V ⟶ C)
    (hjs : s ≫ j = f ≫ δ) (hsg : s ≫ G = zU) (hδ : δ ≫ E = zV)
    (hz : zU ≫ v = f ≫ zV) (sq : CommSq j G E v)
    (K : Etale.DerivedCategoryModule P.Coefficient C) :
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f δ).inv.app
        ((pull P E).obj K) ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        s j (f ≫ δ) hjs.symm).hom.app ((pull P E).obj K) ≫
      (pull P s).map ((DualizingLocality.pullSquare P j G E v sq).hom.app K) ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        s G zU hsg.symm).inv.app ((pull P v).obj K) =
    (pull P f).map ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        δ E zV hδ.symm).inv.app K) ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f zV).inv.app K ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        zU v (f ≫ zV) hz.symm).hom.app K := by
  have ht : f ≫ zV = (f ≫ δ) ≫ E := by rw [Category.assoc, hδ]
  have h₁ := Etale.leftDerivedUpperStarComp_hom_app_map_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} P.Coefficient) s j E (f ≫ δ) (G ≫ v) (f ≫ zV)
    hjs.symm sq.w.symm ht K
  have h₂ := Etale.map_leftDerivedUpperStarComp_hom_app_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} P.Coefficient) s G v zU (G ≫ v) (f ≫ zV)
    hsg.symm rfl hz.symm K
  have h₃ := Etale.map_leftDerivedUpperStarComp_inv_app_leftDerivedUpperStarComp_inv_app
    (ModuleCat.{u + 1} P.Coefficient) f δ E (f ≫ δ) zV (f ≫ zV)
    rfl hδ.symm ht K
  simp only [DualizingLocality.pullSquare, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% h₁, h₂]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, ← h₃]
  simp only [Category.assoc]

private theorem restrict_base_change
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {U V Q D B C : Scheme.{u}}
    (f : U ⟶ V) (δ : V ⟶ D) (s : U ⟶ Q) (j : Q ⟶ D)
    (G : Q ⟶ B) (E : D ⟶ C) (v : B ⟶ C) (zU : U ⟶ B) (zV : V ⟶ C)
    (hjs : s ≫ j = f ≫ δ) (hsg : s ≫ G = zU) (hδ : δ ≫ E = zV)
    (hz : zU ≫ v = f ≫ zV) (sq : CommSq j G E v)
    {M : Etale.DerivedCategoryModule P.Coefficient D}
    {M₀ : Etale.DerivedCategoryModule P.Coefficient Q}
    {K : Etale.DerivedCategoryModule P.Coefficient C}
    {K₀ : Etale.DerivedCategoryModule P.Coefficient B}
    (α : M ⟶ (pull P E).obj K) (α₀ : M₀ ⟶ (pull P G).obj K₀)
    (b : (pull P j).obj M ⟶ M₀) (c : (pull P v).obj K ⟶ K₀)
    (hb : b ≫ α₀ = (pull P j).map α ≫
      (DualizingLocality.pullSquare P j G E v sq).hom.app K ≫ (pull P G).map c) :
    (pull P f).map ((pull P δ).map α ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          δ E zV hδ.symm).inv.app K) ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f zV).inv.app K ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        zU v (f ≫ zV) hz.symm).hom.app K ≫ (pull P zU).map c =
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f δ).inv.app M ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        s j (f ≫ δ) hjs.symm).hom.app M ≫
      (pull P s).map b ≫ (pull P s).map α₀ ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        s G zU hsg.symm).inv.app K₀ := by
  have hn₁ := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    s j (f ≫ δ) hjs.symm).hom.naturality α
  have hn₂ := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    f δ).inv.naturality α
  have hn₃ := (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    s G zU hsg.symm).inv.naturality c
  change (pull P (f ≫ δ)).map α ≫ _ =
    _ ≫ (pull P s).map ((pull P j).map α) at hn₁
  change (pull P f).map ((pull P δ).map α) ≫ _ =
    _ ≫ (pull P (f ≫ δ)).map α at hn₂
  change (pull P s).map ((pull P G).map c) ≫ _ =
    _ ≫ (pull P zU).map c at hn₃
  rw [← Functor.map_comp_assoc, hb]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn₁, ← reassoc_of% hn₂, hn₃]
  rw [← reassoc_of% (section_pullSquare P f δ s j G E v zU zV hjs hsg hδ hz sq K)]

set_option linter.unusedVariables false in
/-- The second diagonal input in etale-origin coordinates.
Source: composition coherence Step 1, refined input calculation, Step 5 of
lem-pur-difference-coordinate-section-identifications
(blueprint: lem-pur-difference-second-input-restriction).

Proof: apply normalized source-etale base change to h=P_e^V, etale arrow G_g and
base arrow f. Its base-changed smooth map is P_e and its etale arrow is G, using
the translated Cartesian square G_g j = v G. The equation is beta(p_g,f)
followed by E(G,P_e) equals j-pullback of E(G_g,P_e^V), followed by the square
pullback constraint and G-pullback of beta(P_e^V,f). Pull this equation along s.
Use j s = Delta_g f, G s = z_e and v z_e = z_e^V f. Naturality and associativity
of the canonical pullback compositors identify its source comparison with gammaG
and its target comparison with tau, yielding exactly the equation below. All
maps retain their counit normalization. The same polynomial identities hold for
empty schemes and dimension zero, without replacing an etale map by an identity. -/
theorem difference_second_input_restriction
    (P : WeilConjectures.PurityFiniteSetting.{u}) {U V T : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))] [V.Over (Spec (.of P.field.k))]
    [T.Over (Spec (.of P.field.k))]
    [IsAffine U] [IsAffine V] [IsAffine T]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (V ↘ Spec (.of P.field.k))]
    [QuasiCompact (V ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (f : U ⟶ V) (g : V ⟶ T)
    [f.IsOver (Spec (.of P.field.k))] [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (d e : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension e g]
    (x : U ⟶ A d V) (y : V ⟶ A e T) [Etale x] [Etale y]
    (hx : x ≫ pr d V = f) (hy : y ≫ pr e T = g) :
    (by
      letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
      letI := LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of P.field.k))
      letI := LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of P.field.k))
      letI := LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of P.field.k))
      letI : IsNoetherian U := ⟨⟩
      letI : IsNoetherian V := ⟨⟩
      letI : IsNoetherian T := ⟨⟩
      let fac := factorization (k := P.field.k) f g d e x y hx hy
      let hHJ := fac.1
      let hHa := fac.2.1
      let hGpr := fac.2.2.1
      let hJq := fac.2.2.2.1
      let hGs := fac.2.2.2.2.1
      let hFt := fac.2.2.2.2.2.1
      let fac1 := fac.2.2.2.2.2.2.2.2
      let hFpr := fac1.1
      let hGe := fac1.2.1
      let hGsep := fac1.2.2.1
      let hGlft := fac1.2.2.2.1
      let hGqc := fac1.2.2.2.2.1
      let hHe := fac1.2.2.2.2.2.1
      let hHsep := fac1.2.2.2.2.2.2.1
      let hHlft := fac1.2.2.2.2.2.2.2.1
      let fac2 := fac1.2.2.2.2.2.2.2.2
      let hHqc := fac2.1
      let hJe := fac2.2.1
      let hJsep := fac2.2.2.1
      let hJlft := fac2.2.2.2.1
      let hJqc := fac2.2.2.2.2.1
      let hFe := fac2.2.2.2.2.2.1
      let hFsep := fac2.2.2.2.2.2.2.1
      let hFlft := fac2.2.2.2.2.2.2.2.1
      let fac3 := fac2.2.2.2.2.2.2.2.2
      let hFqc := fac3.1
      let hQa := fac3.2.1
      let hWa := fac3.2.2.1
      let hRa := fac3.2.2.2.1
      let hWfa := fac3.2.2.2.2.1
      let hWga := fac3.2.2.2.2.2.1
      let hAda := fac3.2.2.2.2.2.2.1
      let hAea := fac3.2.2.2.2.2.2.2.1
      let fac4 := fac3.2.2.2.2.2.2.2.2
      let hAdea := fac4.1
      let hAdVa := fac4.2.1
      let hAeTa := fac4.2.2.1
      let hAeVa := fac4.2.2.2.1
      let fac5 := fac4.2.2.2.2.2.2.2.2
      let hRsq := fac5.1
      let hAffsq := fac5.2.1
      let hsq := fac5.2.2.1
      let hPe := fac5.2.2.2.1
      let hPde := fac5.2.2.2.2.1
      let hqQ := fac5.2.2.2.2.2.1
      let hHsq := fac5.2.2.2.2.2.2.1
      let hGsq := fac5.2.2.2.2.2.2.2.1
      let fac6 := fac5.2.2.2.2.2.2.2.2
      let hHfe := fac6.1
      let hGge := fac6.2.1
      let hHfz := fac6.2.2.1
      let hGgz := fac6.2.2.2
      letI := hGe
      letI := hGsep
      letI := hGlft
      letI := hGqc
      letI := hHe
      letI := hHsep
      letI := hHlft
      letI := hHqc
      letI := hJe
      letI := hJsep
      letI := hJlft
      letI := hJqc
      letI := hFe
      letI := hFsep
      letI := hFlft
      letI := hFqc
      letI := hQa
      letI := hWa
      letI := hRa
      letI := hWfa
      letI := hWga
      letI := hAda
      letI := hAea
      letI := hAdea
      letI := hAdVa
      letI := hAeTa
      letI := hAeVa
      letI := hsq
      letI := hPe
      letI := hPde
      letI := hqQ
      letI := hHfe
      letI := hGge
      letI := (geometryProperties d e f g).1
      letI := (geometryProperties d e f g).2.1
      letI := (geometryProperties d e f g).2.2.1
      letI := (geometryProperties d e f g).2.2.2.1
      letI := (geometryProperties d e f g).2.2.2.2
      letI := affineDimension d U
      letI := affineDimension e V
      letI := affineDimension (d + e) U
      let aU := U ↘ Spec (.of P.field.k)
      let aV := V ↘ Spec (.of P.field.k)
      let aT := T ↘ Spec (.of P.field.k)
      let aQ := pullback.fst (f ≫ g) g ≫ aU
      let t := pullback.diagonal (f ≫ g)
      let G := differenceSecond e f g y
      let HH := H f g x
      let JJ := J d f g y
      let FF := differenceTotal d e f g x y
      let qQ := R d f g ↘ Q f g
      let hHfpr : pullback.fst f f = differenceFirst d f x ≫ pr d U :=
        (AffineSpace.homOfVector_over _ _).symm
      let hGgpr : pullback.fst g g = differenceFirst e g y ≫ pr e V :=
        (AffineSpace.homOfVector_over _ _).symm
      let chiG0 := (pull P (pullback.diagonal g)).map
        (normalizedE P (differenceFirst e g y) (pr e V) (pullback.fst g g)
          hGgpr aV).hom ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          (pullback.diagonal g) (differenceFirst e g y) (zero e V) hGgz.symm).inv.app _
      let tau :=
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          f (zero e V)).inv.app _ ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          (zero e U) (AffineSpace.map (Coords e) f) (f ≫ zero e V)
          (AffineSpace.zeroSection_comp_map f).symm).hom.app _ ≫
        (pull P (zero e U)).map
          (WeilConjectures.PurityFiniteSetting.DiagonalPasting.beta P.Coefficient P e
            (AffineSpace.isPullback_map f) (pr e V ≫ aV)).hom
      let chiG := (pull P f).map chiG0 ≫ tau
      let secondRoute := (gammaG P.Coefficient P e f g aT).hom ≫
        (pull P (s f g)).map
          (normalizedE P G (pr e U) (pullback.fst (f ≫ g) g) hGpr.symm aU).hom ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          (s f g) G (zero e U) hGs.symm).inv.app _
      exact chiG = secondRoute
      : Prop) := by
  let := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
  let := LocallyOfFiniteType.isLocallyNoetherian (U ↘ Spec (.of P.field.k))
  let := LocallyOfFiniteType.isLocallyNoetherian (V ↘ Spec (.of P.field.k))
  let := LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of P.field.k))
  let : IsNoetherian U := ⟨⟩
  let : IsNoetherian V := ⟨⟩
  let : IsNoetherian T := ⟨⟩
  let fac := factorization (k := P.field.k) f g d e x y hx hy
  let hHJ := fac.1
  let hHa := fac.2.1
  let hGpr := fac.2.2.1
  let hJq := fac.2.2.2.1
  let hGs := fac.2.2.2.2.1
  let hFt := fac.2.2.2.2.2.1
  let fac1 := fac.2.2.2.2.2.2.2.2
  let hFpr := fac1.1
  let hGe := fac1.2.1
  let hGsep := fac1.2.2.1
  let hGlft := fac1.2.2.2.1
  let hGqc := fac1.2.2.2.2.1
  let hHe := fac1.2.2.2.2.2.1
  let hHsep := fac1.2.2.2.2.2.2.1
  let hHlft := fac1.2.2.2.2.2.2.2.1
  let fac2 := fac1.2.2.2.2.2.2.2.2
  let hHqc := fac2.1
  let hJe := fac2.2.1
  let hJsep := fac2.2.2.1
  let hJlft := fac2.2.2.2.1
  let hJqc := fac2.2.2.2.2.1
  let hFe := fac2.2.2.2.2.2.1
  let hFsep := fac2.2.2.2.2.2.2.1
  let hFlft := fac2.2.2.2.2.2.2.2.1
  let fac3 := fac2.2.2.2.2.2.2.2.2
  let hFqc := fac3.1
  let hQa := fac3.2.1
  let hWa := fac3.2.2.1
  let hRa := fac3.2.2.2.1
  let hWfa := fac3.2.2.2.2.1
  let hWga := fac3.2.2.2.2.2.1
  let hAda := fac3.2.2.2.2.2.2.1
  let hAea := fac3.2.2.2.2.2.2.2.1
  let fac4 := fac3.2.2.2.2.2.2.2.2
  let hAdea := fac4.1
  let hAdVa := fac4.2.1
  let hAeTa := fac4.2.2.1
  let hAeVa := fac4.2.2.2.1
  let fac5 := fac4.2.2.2.2.2.2.2.2
  let hRsq := fac5.1
  let hAffsq := fac5.2.1
  let hsq := fac5.2.2.1
  let hPe := fac5.2.2.2.1
  let hPde := fac5.2.2.2.2.1
  let hqQ := fac5.2.2.2.2.2.1
  let hHsq := fac5.2.2.2.2.2.2.1
  let hGsq := fac5.2.2.2.2.2.2.2.1
  let fac6 := fac5.2.2.2.2.2.2.2.2
  let hHfe := fac6.1
  let hGge := fac6.2.1
  let hHfz := fac6.2.2.1
  let hGgz := fac6.2.2.2
  let := hGe
  let := hGsep
  let := hGlft
  let := hGqc
  let := hHe
  let := hHsep
  let := hHlft
  let := hHqc
  let := hJe
  let := hJsep
  let := hJlft
  let := hJqc
  let := hFe
  let := hFsep
  let := hFlft
  let := hFqc
  let := hQa
  let := hWa
  let := hRa
  let := hWfa
  let := hWga
  let := hAda
  let := hAea
  let := hAdea
  let := hAdVa
  let := hAeTa
  let := hAeVa
  let := hsq
  let := hPe
  let := hPde
  let := hqQ
  let := hHfe
  let := hGge
  let := (geometryProperties d e f g).1
  let := (geometryProperties d e f g).2.1
  let := (geometryProperties d e f g).2.2.1
  let := (geometryProperties d e f g).2.2.2.1
  let := (geometryProperties d e f g).2.2.2.2
  let := affineDimension d U
  let := affineDimension e V
  let := affineDimension (d + e) U
  let aU := U ↘ Spec (.of P.field.k)
  let aV := V ↘ Spec (.of P.field.k)
  let aT := T ↘ Spec (.of P.field.k)
  let aQ := pullback.fst (f ≫ g) g ≫ aU
  let t := pullback.diagonal (f ≫ g)
  let G := differenceSecond e f g y
  let HH := H f g x
  let JJ := J d f g y
  let FF := differenceTotal d e f g x y
  let qQ := R d f g ↘ Q f g
  let hHfpr : pullback.fst f f = differenceFirst d f x ≫ pr d U :=
    (AffineSpace.homOfVector_over _ _).symm
  let hGgpr : pullback.fst g g = differenceFirst e g y ≫ pr e V :=
    (AffineSpace.homOfVector_over _ _).symm
  let chiG0 := (pull P (pullback.diagonal g)).map
    (normalizedE P (differenceFirst e g y) (pr e V) (pullback.fst g g)
      hGgpr aV).hom ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (pullback.diagonal g) (differenceFirst e g y) (zero e V) hGgz.symm).inv.app _
  let tau :=
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      f (zero e V)).inv.app _ ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (zero e U) (AffineSpace.map (Coords e) f) (f ≫ zero e V)
      (AffineSpace.zeroSection_comp_map f).symm).hom.app _ ≫
    (pull P (zero e U)).map
      (WeilConjectures.PurityFiniteSetting.DiagonalPasting.beta P.Coefficient P e
        (AffineSpace.isPullback_map f) (pr e V ≫ aV)).hom
  let chiG := (pull P f).map chiG0 ≫ tau
  let secondRoute := (gammaG P.Coefficient P e f g aT).hom ≫
    (pull P (s f g)).map
      (normalizedE P G (pr e U) (pullback.fst (f ≫ g) g) hGpr.symm aU).hom ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (s f g) G (zero e U) hGs.symm).inv.app _
  change chiG = secondRoute
  let : (A e V).Over (Spec (.of P.field.k)) := ⟨pr e V ≫ aV⟩
  let : (A e U).Over (Spec (.of P.field.k)) := ⟨pr e U ≫ aU⟩
  let : (pullback g g).Over (Spec (.of P.field.k)) := ⟨pullback.fst g g ≫ aV⟩
  let : (Q f g).Over (Spec (.of P.field.k)) := ⟨pullback.fst (f ≫ g) g ≫ aU⟩
  let : LocallyOfFiniteType (A e V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pr e V ≫ aV))
  let : QuasiCompact (A e V ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (pr e V ≫ aV))
  let : LocallyOfFiniteType (A e U ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pr e U ≫ aU))
  let : QuasiCompact (A e U ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (pr e U ≫ aU))
  let : LocallyOfFiniteType (pullback g g ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst g g ≫ aV))
  let : QuasiCompact (pullback g g ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (pullback.fst g g ≫ aV))
  let : LocallyOfFiniteType (Q f g ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst (f ≫ g) g ≫ aU))
  let : QuasiCompact (Q f g ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (pullback.fst (f ≫ g) g ≫ aU))
  let : (pr e V).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : (pr e U).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  let : (AffineSpace.map (Coords e) f).IsOver (Spec (.of P.field.k)) := ⟨by
    change AffineSpace.map (Coords e) f ≫ (pr e V ≫ aV) = pr e U ≫ aU
    rw [← Category.assoc, AffineSpace.map_over, Category.assoc]
    rw [show f ≫ aV = aU from CategoryTheory.comp_over f (Spec (.of P.field.k))]⟩
  let : (differenceFirst e g y).IsOver (Spec (.of P.field.k)) := ⟨by
    change differenceFirst e g y ≫ (pr e V ≫ aV) = pullback.fst g g ≫ aV
    rw [← Category.assoc, ← hGgpr]⟩
  let : G.IsOver (Spec (.of P.field.k)) := ⟨by
    change G ≫ (pr e U ≫ aU) = pullback.fst (f ≫ g) g ≫ aU
    rw [← Category.assoc, hGpr]⟩
  let : (j f g).IsOver (Spec (.of P.field.k)) := ⟨by
    change j f g ≫ (pullback.fst g g ≫ aV) = pullback.fst (f ≫ g) g ≫ aU
    rw [← Category.assoc, (geometry f g).2.1.w, Category.assoc]
    rw [show f ≫ aV = aU from CategoryTheory.comp_over f (Spec (.of P.field.k))]⟩
  let : LocallyOfFiniteType (AffineSpace.map (Coords e) f) :=
    MorphismProperty.of_isPullback (AffineSpace.isPullback_map f).flip inferInstance
  let : QuasiCompact (AffineSpace.map (Coords e) f) :=
    MorphismProperty.of_isPullback (AffineSpace.isPullback_map f).flip inferInstance
  let : IsSeparated (j f g) :=
    MorphismProperty.of_isPullback (geometry f g).2.1.flip inferInstance
  let : LocallyOfFiniteType (j f g) :=
    MorphismProperty.of_isPullback (geometry f g).2.1.flip inferInstance
  let : QuasiCompact (j f g) :=
    MorphismProperty.of_isPullback (geometry f g).2.1.flip inferInstance
  have hb := normalized_base_change P (pr e V) e (pr e U) e f
    (AffineSpace.map (Coords e) f) (differenceFirst e g y) G (j f g)
    (AffineSpace.isPullback_map f) hGsq.flip
    (pullback.fst g g) (pullback.fst (f ≫ g) g) hGgpr hGpr.symm
    (geometry f g).2.1
  have hr := restrict_base_change P f (pullback.diagonal g) (s f g) (j f g)
    G (differenceFirst e g y) (AffineSpace.map (Coords e) f) (zero e U) (zero e V)
    (geometry f g).2.2.2.2.2 hGs hGgz (AffineSpace.zeroSection_comp_map f)
    hGsq.flip.toCommSq
    (normalizedE P (differenceFirst e g y) (pr e V) (pullback.fst g g) hGgpr aV).hom
    (normalizedE P G (pr e U) (pullback.fst (f ≫ g) g) hGpr.symm aU).hom
    (Etale.dualizingComplexBaseChangeMap P.Coefficient (geometry f g).2.1)
    (Etale.dualizingComplexBaseChangeMap P.Coefficient (AffineSpace.isPullback_map f)) hb
  simpa only [chiG, chiG0, tau, secondRoute, gammaG, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Category.assoc,
    WeilConjectures.PurityFiniteSetting.DiagonalPasting.beta, asIso_hom] using hr

end AlgebraicGeometry.ProEtale.DifferenceCoordinateSection
