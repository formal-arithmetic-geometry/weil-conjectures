module

public import Sheaf.Paper.DifferenceFirstInputRestriction
public import Sheaf.AlgebraicGeometry.AffineDifferenceTowerFactorization
public import Sheaf.SecSmoothPurity.FiniteEtaleDualizingNormalization
public import Sheaf.Paper.PuritySectionInvariantIntrinsic
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Paper.DifferenceSecondInputRestriction
import Sheaf.Paper.NormalizedEtaleComparisonComposition

/-! # Difference-coordinate identifications of diagonal section invariants

Source: blueprint thm-pur-composition-coherence, proof Step 1, standard-coordinate
input and output identifications, refined in the DAG proof
(blueprint: lem-pur-difference-coordinate-section-identifications).

The equations use the actual translated charts and the counit-normalized E maps.
They are expressed in the canonical etale-origin coordinates of the small pro-etale
constructible finite-Tor categories, with every pullback compositor retained.
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

/-- The three equations of the node, with canonical pullback constraints inserted.
The local bindings install only consequences of the affine-difference factorization.
Source: composition coherence Step 1, difference-chart identifications
(blueprint: lem-pur-difference-coordinate-section-identifications). -/
def Statement (P : WeilConjectures.PurityFiniteSetting.{u}) {U V T : Scheme.{u}}
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
    (hx : x ≫ pr d V = f) (hy : y ≫ pr e T = g) : Prop := by
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
  let secondRoute := (gammaG P.Coefficient P e f g aT).hom ≫
    (pull P (s f g)).map
      (normalizedE P G (pr e U) (pullback.fst (f ≫ g) g) hGpr.symm aU).hom ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (s f g) G (zero e U) hGs.symm).inv.app _
  let outputDirect := (pull P t).map
    (normalizedE P FF (pr (d + e) U) (pullback.fst (f ≫ g) (f ≫ g))
      hFpr.symm aU).hom
  let outputComposite := (pull P t).map
    ((normalizedE P HH (JJ ≫ pr (d + e) U) (pullback.fst (f ≫ g) (f ≫ g))
        (hFpr.symm.trans ((congrArg (fun v ↦ v ≫ pr (d + e) U) hHJ.symm).trans
          (Category.assoc HH JJ (pr (d + e) U)))) aU).hom ≫
      (pull P HH).map (normalizedE P JJ (pr (d + e) U)
        (JJ ≫ pr (d + e) U) rfl aU).hom ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        HH JJ FF hHJ.symm).inv.app _)
  exact SameProEtaleMap P.Coefficient P chiF firstRoute ∧
    SameProEtaleMap P.Coefficient P chiG secondRoute ∧
    SameProEtaleMap P.Coefficient P outputDirect outputComposite

/-- The actual difference-chart identifications agree with diagonal-section base change.
Source: current blueprint thm-pur-composition-coherence, proof Step 1; the seven-step
DAG refinement (blueprint: lem-pur-difference-coordinate-section-identifications).

Proof plan:
1. Apply affine-difference-tower-factorization. Its Cartesian square identifies R with
   affine d-space over Q. Its restriction squares give H i = l H_f and G_g j = v G;
   its coordinate equations give H_f Delta_f = z_d, G s = z_e, F t = z_(d+e),
   i Delta_f = t, and j s = Delta_g f. These are scheme-map identities.
2. Horizontal compact-support exchange pasting (fix-lem-exchanges) and mate pasting
   give beta_(qQ,s) l*beta_(q,G) = beta_(q,z_e). Pasting the projection square with
   z_e and using P_e z_e = id gives beta_(q,z_e) k*beta_(P_d,P_e) = id.
   Cohomological smoothness makes these particular mates invertible. Restricting
   along z_d identifies z_d*beta_(q,z_e) with the specified delta_d.
3. The source-etale base-change equation of dualizing-sigma-cocycle-locality at
   (qQ,H,s) gives E_(H_f,P_d) beta_(a,s) = H_f*beta_(qQ,s) i*E_(H,qQ).
   Pull along Delta_f and precompose with the inverse beta to obtain chi_f as
   gamma_f, then t*E_(H,qQ), then z_d*beta_(qQ,s).
4. Substitute step 2 and use H t = l z_d. Pullback composition gives exactly
   firstRoute, including inverse beta_(q,G) and delta_d in the indicated direction.
5. Apply the same source-etale equation at (P_e^V,G_g,f), pull along s, and use
   j s = Delta_g f, G s = z_e and v z_e = z_e^V f. The restricted projection
   base-change is tau. This gives chi_g = secondRoute with the actual translations.
6. The composite-E clause of etale-cartesian-tower-tensor-comparison gives
   E_(F,P_e q) = H*E_(J,P_e q) E_(H,P_e q J). Pull along t and insert only
   equality of the scheme composites and the canonical pullback compositor.
7. Polynomial translations and the preceding squares allow empty affines and zero
   blocks. For d=0 use P_e z_e = id, never z_e P_e = id. For e=0 retain the
   counit-normalized etale maps. No orientation or Tate trivialization is chosen.
Finally apply the canonical comparison inverse image to the three equations;
these are precisely the original small pro-etale derived-object equalities.
-/
theorem difference_coordinate_section_identifications
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
    Statement P f g d e x y hx hy := by
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
  let chiF := (pull P (pullback.diagonal f)).map
    (normalizedE P (differenceFirst d f x) (pr d U) (pullback.fst f f)
      hHfpr aU).hom ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (pullback.diagonal f) (differenceFirst d f x) (zero d U) hHfz.symm).inv.app _
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
  let := (affineGeometry d e U).2.2.2.2.2.1
  let := (affineGeometry d e U).2.2.2.2.2.2.1
  let := (affineGeometry d e U).2.2.2.2.2.2.2.1
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
  let secondRoute := (gammaG P.Coefficient P e f g aT).hom ≫
    (pull P (s f g)).map
      (normalizedE P G (pr e U) (pullback.fst (f ≫ g) g) hGpr.symm aU).hom ≫
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      (s f g) G (zero e U) hGs.symm).inv.app _
  let outputDirect := (pull P t).map
    (normalizedE P FF (pr (d + e) U) (pullback.fst (f ≫ g) (f ≫ g))
      hFpr.symm aU).hom
  let outputComposite := (pull P t).map
    ((normalizedE P HH (JJ ≫ pr (d + e) U) (pullback.fst (f ≫ g) (f ≫ g))
        (hFpr.symm.trans ((congrArg (fun v ↦ v ≫ pr (d + e) U) hHJ.symm).trans
          (Category.assoc HH JJ (pr (d + e) U)))) aU).hom ≫
      (pull P HH).map (normalizedE P JJ (pr (d + e) U)
        (JJ ≫ pr (d + e) U) rfl aU).hom ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        HH JJ FF hHJ.symm).inv.app _)
  change SameProEtaleMap P.Coefficient P chiF firstRoute ∧
    SameProEtaleMap P.Coefficient P chiG secondRoute ∧
    SameProEtaleMap P.Coefficient P outputDirect outputComposite
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.map)
      (difference_first_input_restriction P f g d e x y hx hy)
  · exact congrArg
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.map)
      (difference_second_input_restriction P f g d e x y hx hy)
  · have he := normalizedE_comp_congr P HH JJ (pr (d + e) U) FF
      (pullback.fst (f ≫ g) (f ≫ g)) (d + e) aU hHJ hFpr
    exact congrArg
      ((ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory.map)
      (congrArg (fun v ↦ (pull P t).map v) he)

end AlgebraicGeometry.ProEtale.DifferenceCoordinateSection
