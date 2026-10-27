/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y7
-/
module

public import Sheaf.AlgebraicGeometry.AffineDifferenceTowerFactorization
public import Sheaf.Paper.DifferenceFirstInputRestriction

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
      : Prop) := by sorry

end AlgebraicGeometry.ProEtale.DifferenceCoordinateSection
