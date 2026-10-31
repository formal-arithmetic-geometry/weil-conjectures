/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficientFamilyPullback
public import WeilConjectures.AlgebraicGeometry.DiagonalPullbackSquares
import WeilConjectures.AlgebraicGeometry.DiagonalQuotientLinePullbackNormalization
import WeilConjectures.AlgebraicGeometry.DiagonalSupportedPullbackScalarNormalization

/-! # Scalar transport of the diagonal class square

Source: diagonal tower coefficient changes, paragraph (3), scalar base change.
(blueprint: lem-diagonal-quotient-class-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] quotientLine quotientLineMap derivedUpper derivedLower
  derivedScalars modelExchange singlePullback PullEndpoint.shift Endpoint.shift
  scalarPullbackComparison Functor.leftDerivedFunctor Functor.mapDerivedCategory
  spIntegralTwist spIntegralComparison

private theorem scalar_pullback_paste
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (U : A ⥤ B) (V : C ⥤ D) (T : A ⥤ C) (S : B ⥤ D)
    (χ : U ⋙ S ⟶ T ⋙ V)
    {A₀ A₁ : A} {B₀ B₁ : B} {C₀ C₁ : C} {D₀ D₁ : D}
    (δ₀ : A₀ ⟶ A₁) (δ₀' : B₀ ⟶ B₁) (δ : C₀ ⟶ C₁) (δ' : D₀ ⟶ D₁)
    (i : U.obj A₀ ≅ B₀) (j : U.obj A₁ ⟶ B₁)
    (e : T.obj A₀ ≅ C₀) (f : T.obj A₁ ⟶ C₁)
    (e' : S.obj B₀ ≅ D₀) (f' : S.obj B₁ ⟶ D₁)
    (k : V.obj C₀ ≅ D₀) (t : V.obj C₁ ⟶ D₁)
    (hi : U.map δ₀ ≫ j = i.hom ≫ δ₀')
    (he : T.map δ₀ ≫ f = e.hom ≫ δ)
    (he' : S.map δ₀' ≫ f' = e'.hom ≫ δ')
    (hs : χ.app A₀ ≫ V.map e.hom ≫ k.hom = S.map i.hom ≫ e'.hom)
    (hl : χ.app A₁ ≫ V.map f ≫ t = S.map j ≫ f') :
    V.map δ ≫ t = k.hom ≫ δ' := by
  let h := χ.app A₀ ≫ V.map e.hom
  have hh : IsIso (h ≫ k.hom) := by
    change IsIso ((χ.app A₀ ≫ V.map e.hom) ≫ k.hom)
    rw [Category.assoc, hs]
    infer_instance
  have : IsIso h := IsIso.of_isIso_comp_right h k.hom
  apply (cancel_epi h).mp
  change (χ.app A₀ ≫ V.map e.hom) ≫ (V.map δ ≫ t) =
    (χ.app A₀ ≫ V.map e.hom) ≫ (k.hom ≫ δ')
  calc
    (χ.app A₀ ≫ V.map e.hom) ≫ (V.map δ ≫ t) =
        χ.app A₀ ≫ V.map (T.map δ₀) ≫ V.map f ≫ t := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z ↦ χ.app A₀ ≫ V.map z ≫ t) he.symm
    _ = S.map (U.map δ₀) ≫ χ.app A₁ ≫ V.map f ≫ t := by
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (· ≫ V.map f ≫ t) (χ.naturality δ₀).symm
    _ = S.map (U.map δ₀) ≫ S.map j ≫ f' := by rw [hl]
    _ = S.map i.hom ≫ S.map δ₀' ≫ f' := by
      rw [← S.map_comp_assoc, hi, S.map_comp, Category.assoc]
    _ = S.map i.hom ≫ e'.hom ≫ δ' := by rw [he']
    _ = (χ.app A₀ ≫ V.map e.hom) ≫ (k.hom ≫ δ') := by
      simpa only [Category.assoc] using congrArg (· ≫ δ') hs.symm

private theorem diagonal_scalar_paste_generic
    {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
    (a : R ⟶ T) [IsMonHom a] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {L₀ : ∀ X : Scheme.{u}, Modules R X} {L : ∀ X : Scheme.{u}, Modules T X}
    {v : ∀ X : Scheme.{u}, (L₀ X).X ⟶ (L X).X}
    {d₀ : Diagram R Y L₀} {d₀' : Diagram R Y' L₀}
    {d : Diagram T Y L} {d' : Diagram T Y' L}
    {m₀P : (upperStar Ab.{u + 1} (baseP g)).obj (L₀ (ProjectiveLine Y)).X ⟶
      (L₀ (ProjectiveLine Y')).X}
    {m₀W : (upperStar Ab.{u + 1} (baseW g)).obj (L₀ (diagonalSurface Y)).X ⟶
      (L₀ (diagonalSurface Y')).X}
    {mP : (upperStar Ab.{u + 1} (baseP g)).obj (L (ProjectiveLine Y)).X ⟶
      (L (ProjectiveLine Y')).X}
    {mW : (upperStar Ab.{u + 1} (baseW g)).obj (L (diagonalSurface Y)).X ⟶
      (L (diagonalSurface Y')).X}
    (integral : PullbackCompatibility R g L₀ d₀ d₀' m₀P m₀W)
    (scalar : ScalarCompatibility a Y L₀ L v d₀ d)
    (scalar' : ScalarCompatibility a Y' L₀ L v d₀' d')
    (s : SourcePullback T g L mP mW)
    (hline : ScalarPullbackEndpointSquare a (baseW g)
      integral.sourceData.endpoints.lineW scalar.lineW scalar'.lineW s.endpoints.lineW)
    (hsource : (scalarPullbackComparison a (baseW g)).app
        ((DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).obj (source R Y)) ≫
      (derivedUpper T (baseW g)).map scalar.supported.iso.hom ≫
      (singlePullback T (baseW g) (source T Y)).hom ≫
      (DerivedCategory.singleFunctor (Modules T (diagonalSurface Y')) 0).map s.supported.hom =
    (derivedScalars a (diagonalSurface Y')).map
      ((singlePullback R (baseW g) (source R Y)).hom ≫
        (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map
          integral.sourceData.supported.hom) ≫ scalar'.supported.iso.hom) :
    ClassPullbackSquare T g L d d' mP mW s := by
  refine ⟨?_⟩
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using
    scalar_pullback_paste
      (derivedUpper R (baseW g)) (derivedUpper T (baseW g))
      (derivedScalars a (diagonalSurface Y)) (derivedScalars a (diagonalSurface Y'))
      (scalarPullbackComparison a (baseW g)) d₀.delta d₀'.delta d.delta d'.delta
      ((singlePullback R (baseW g) (source R Y)) ≪≫
        (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).mapIso
          integral.sourceData.supported)
      integral.sourceData.endpoints.lineW.shift scalar.supported.iso
      (scalar.lineW.shift a) scalar'.supported.iso (scalar'.lineW.shift a)
      ((singlePullback T (baseW g) (source T Y)) ≪≫
        (DerivedCategory.singleFunctor (Modules T (diagonalSurface Y')) 0).mapIso s.supported)
      s.endpoints.lineW.shift
      (by simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using integral.delta)
      scalar.delta scalar'.delta
      (by simpa only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using hsource)
      hline.comm

/-- The diagonal class square after quotient reduction, with ordinary source
and line maps supplied separately. This asserts no trace equation or exchange
isomorphism.

Source: latest blueprint, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3), naturality of the
class under the coefficient functors; original quotient-base-change proof, step 2.
(blueprint: lem-diagonal-quotient-class-pullback).

Proof: Apply derived quotient extension to integral.delta. The scalar/inverse-image
compositor identifies the two ways to pull back the extended integral line. Its
single-complex and shift normalizations identify this compositor with the supplied
quotient PullEndpoint: precomposition with the pulled-back extendπ gives
QuotientPullMap, and that map is epic. On the supported source the same identity
follows from the coefficient-unit normalization and supported_normalization:
both adjoints are obtained by the same coefficient unit and diagonal counit.
Paste the resulting square with scalar.delta and scalar'.delta. The two
Endpoint.normalization equations fix the derived scalar endpoints uniquely
through the scalar adjunction, so these are the specified endpoints, without any
rescaling. Cancel the supported scalar isomorphism and the scalar/pullback
compositor. The remaining boundary is exactly the displayed quotient class
square. No trace equation or property of a particular Cartier class is used.
This reasoning also applies to n = 0, ramified levels, and the zero quotient. -/
theorem diagonalQuotient_classPullback
    (l : ℕ) [Fact l.Prime] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y] [IsNoetherian Y']
    (E : PadicAlgCl.FiniteIntermediateField l)
    (π : PadicAlgCl.integers l E) (n : ℕ)
    (d₀ : Diagram (Profinite.padicIntegersRingObj.{u} l E.1) Y
      (fun X ↦ spIntegralTwist X l E))
    (d₀' : Diagram (Profinite.padicIntegersRingObj.{u} l E.1) Y'
      (fun X ↦ spIntegralTwist X l E))
    (integral : PullbackCompatibility (Profinite.padicIntegersRingObj.{u} l E.1) g
      (fun X ↦ spIntegralTwist X l E) d₀ d₀'
      (spIntegralComparison (baseP g) l E) (spIntegralComparison (baseW g) l E))
    (d : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y (quotientLine l E π n))
    (d' : Diagram (Profinite.continuousMapRingObj.{u} (completedResidue l E π n))
      Y' (quotientLine l E π n))
    (scalar : ScalarCompatibility (quotientMap l E π n) Y
      (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
      (quotientLineMap l E π n) d₀ d)
    (scalar' : ScalarCompatibility (quotientMap l E π n) Y'
      (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
      (quotientLineMap l E π n) d₀' d')
    (mP : (upperStar Ab.{u + 1} (baseP g)).obj
      (quotientLine l E π n (ProjectiveLine Y)).X ⟶
        (quotientLine l E π n (ProjectiveLine Y')).X)
    (mW : (upperStar Ab.{u + 1} (baseW g)).obj
      (quotientLine l E π n (diagonalSurface Y)).X ⟶
        (quotientLine l E π n (diagonalSurface Y')).X)
    (_hP : QuotientPullMap l E π n (baseP g) mP)
    (_hW : QuotientPullMap l E π n (baseW g) mW)
    (s : SourcePullback
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) g
      (quotientLine l E π n) mP mW) :
    ClassPullbackSquare
      (Profinite.continuousMapRingObj.{u} (completedResidue l E π n)) g
      (quotientLine l E π n) d d' mP mW s := by
  have hline := diagonalQuotient_linePullbackNormalization l E π n (baseW g)
    integral.sourceData.endpoints.lineW scalar.lineW scalar'.lineW mW _hW
    s.endpoints.lineW
  have hsource := diagonalSupported_pullbackScalarNormalization
    (quotientMap l E π n) g (fun X ↦ spIntegralTwist X l E) (quotientLine l E π n)
    (spIntegralComparison (baseP g) l E) (spIntegralComparison (baseW g) l E)
    mP mW integral.sourceData s (scalar.units (ProjectiveLine Y))
    (scalar'.units (ProjectiveLine Y')) scalar.supported scalar'.supported
  exact diagonal_scalar_paste_generic (quotientMap l E π n) g
    integral scalar scalar' s hline hsource

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
