/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y7
-/
module

public import Sheaf.AlgebraicGeometry.AffineDifferenceTowerFactorization
public import Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization

/-! # Difference-coordinate first input restriction

Source: composition coherence Step 1
(blueprint: lem-pur-difference-first-input-restriction).
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

/-- Insert equality of structure maps into the specified normalized etale comparison.
Source: composition coherence Step 1, the comparisons E for the difference charts
(blueprint: lem-pur-difference-coordinate-section-identifications). -/
def normalizedE (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y B : Scheme.{u}} (v : X ⟶ Y) (h : Y ⟶ B) (h' : X ⟶ B)
    [Etale v] [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [IsSeparated h'] [LocallyOfFiniteType h'] [QuasiCompact h']
    [HasCompactification h] [HasCompactification h']
    (hv : h' = v ≫ h) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] :
    Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) h' ≅
      (pull P v).obj (Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) h) :=
  letI : B.Over (Spec (.of P.field.k)) := ⟨aB⟩
  letI : Y.Over (Spec (.of P.field.k)) := ⟨h ≫ aB⟩
  letI : X.Over (Spec (.of P.field.k)) := ⟨h' ≫ aB⟩
  letI : h.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : h'.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  letI : v.IsOver (Spec (.of P.field.k)) :=
    ⟨(Category.assoc v h aB).symm.trans (congrArg (fun t ↦ t ≫ aB) hv.symm)⟩
  letI : LocallyOfFiniteType (B ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType aB)
  letI : QuasiCompact (B ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aB)
  letI : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (h ≫ aB))
  letI : QuasiCompact (Y ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (h ≫ aB))
  letI : LocallyOfFiniteType (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (LocallyOfFiniteType (h' ≫ aB))
  letI : QuasiCompact (X ↘ Spec (.of P.field.k)) :=
    inferInstanceAs (QuasiCompact (h' ≫ aB))
  (FiniteEtaleNormalization.congr P h' (v ≫ h) hv).app
      (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) B) ≪≫
    sourceEtale P v h


/-- The first diagonal input in etale-origin coordinates.
Source: composition coherence Step 1, refined input calculation, Steps 2--4 of
lem-pur-difference-coordinate-section-identifications
(blueprint: lem-pur-difference-first-input-restriction).

Proof: paste the Cartesian squares for q along G and s. Horizontal compact-support
exchange and mate pasting identify beta(q_Q,s) after l-pullback of beta(q,G) with
beta(q,z_e). Paste the projection square with the zero section; P_e z_e = id makes
beta(q,z_e) inverse to k-pullback of beta(P_d,P_e). These particular maps are
invertible by smooth base change. Restrict along z_d to obtain the displayed delta.
Next apply normalized source-etale base change to (q_Q,H,s). Its base-changed
etale arrow is H_f, since H i = l H_f. Pull along Delta_f, use i Delta_f = t and
H_f Delta_f = z_d, and precompose with the inverse of the specified beta(a,s).
Substitute the projection calculation and use H t = l z_d. Pullback associativity
and naturality put every compositor in exactly the displayed firstRoute order.
The actual translated coordinates prove the scheme equalities; this also covers
empty schemes and either zero block, using P_e z_e = id in that direction. -/
theorem difference_first_input_restriction
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
      let chiF := (pull P (pullback.diagonal f)).map
        (normalizedE P (differenceFirst d f x) (pr d U) (pullback.fst f f)
          hHfpr aU).hom ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          (pullback.diagonal f) (differenceFirst d f x) (zero d U) hHfz.symm).inv.app _
      letI := (affineGeometry d e U).2.2.2.2.2.1
      letI := (affineGeometry d e U).2.2.2.2.2.2.1
      letI := (affineGeometry d e U).2.2.2.2.2.2.2.1
      let delta :=
        (pull P (zero (d + e) U)).map
          (WeilConjectures.PurityFiniteSetting.DiagonalPasting.beta P.Coefficient P d
            hAffsq (pr d U ≫ aU)).inv ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          (zero (d + e) U) (first d e U) (zero d U)
          (affineGeometry d e U).2.1.symm).inv.app _
      let firstRoute := (gammaF P.Coefficient P d f g aT).hom ≫
        (pull P t).map
          ((normalizedE P HH qQ (a f g) hHa.symm aQ).hom ≫
            (pull P HH).map
              (WeilConjectures.PurityFiniteSetting.DiagonalPasting.beta P.Coefficient P d
                hRsq (pr (d + e) U ≫ aU)).inv ≫
            (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
              HH JJ FF hHJ.symm).inv.app _) ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          t FF (zero (d + e) U) hFt.symm).inv.app _ ≫ delta
      exact chiF = firstRoute
      : Prop) := by sorry

end AlgebraicGeometry.ProEtale.DifferenceCoordinateSection
