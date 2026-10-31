/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChartDncVectorFactorData
import WeilConjectures.AlgebraicGeometry.ChartDncNaturality
import WeilConjectures.AlgebraicGeometry.ChartIntegrationAdjoints

/-! # Deformation and integration factors under an etale chart

The fixed canonical constructions are reexported from ChartDncVectorFactorData.
The two compatibility equations and frame independence are combined here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.ChartFactors

/-- The inverse of beta_h in every local conormal frame, including every further
invertible linear change of that frame. The left side uses the actual normal-cone
comparison and the exceptional mate for the chosen frame. The right side is the
same fixed affine integration adjoint for every frame automorphism, with canonical
Tate pullback. Thus this is an equation about beta_h itself on N_U, transported by nu*.
Source: chart proof Step 4 (blueprint: lem-pur-chart-dnc-vector-factors). -/
def FrameIndependence (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}}
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) : Prop :=
  letI := P.noetherian (h ≫ aY)
  letI := (chartDiagonalNormalBundle d h).1
  let F := ConormalGradedAlgebra.piece (pullback.diagonal h) 1
  ∀ (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (W : U.Opens)
    (f : VectorBundleZeroSection.Trivialization U d F W)
    (G : Aut (F.restrict W.ι)),
    letI : IsNoetherian W.toScheme := ⟨⟩
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) W.ι).leftDerivedFunctor.map
        ((beta P d h aY N).inv ≫ (normalBundleComparison P d h aY N).hom) ≫
      (Dnc.pullComparison P W.ι _).hom ≫
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} P.Coefficient) W.toScheme).mapDerivedCategory.map
        (Etale.FiniteRingSectionDeformation.bundleFrameSectionMap P.Coefficient
          U d F W (G ≪≫ f)) =
      (Dnc.pullComparison P W.ι (P.diagonalTwistEtale U d)).hom ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) W.toScheme).mapDerivedCategory.map
          ((Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient
            P.diagonalExponent P.diagonalExponent_annihilates t W.ι
            (P.diagonalExponent_isUnit (h ≫ aY)) d).hom ≫
          Etale.FiniteRingSectionDeformation.affineSectionAdjoint P.diagonalExponent
            (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
            P.diagonalExponent_annihilates t D W.toScheme
            (affineTracePullbackInvertible P.diagonalExponent W.ι
              (P.diagonalExponent_isUnit (h ≫ aY))) d
            (Etale.FiniteRingSectionDeformation.standardZero W.toScheme d)
            (Etale.FiniteRingSectionDeformation.standardZero_over W.toScheme d))

/-- The two exact derived-category equations, in the fixed canonical comparisons.
The final clause identifies beta_h in every local conormal frame after every
invertible linear change of frame. Every normalized root-line and compact-support
presentation is quantified; no orientation or endpoint comparison is assumed.
Source: chart proof Steps 3--4 (blueprint: lem-pur-chart-dnc-vector-factors). -/
def Conclusion (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}} [IsAffine Y]
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h) : Prop :=
  let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
  letI : SmoothOfRelativeDimension d p := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) Y
  letI := P.noetherian (h ≫ aY)
  ∀ (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates),
    ((Dnc.existsUnique_dncInvariance P d (pullback.fst h h) (h ≫ aY)
      (pullback.diagonal h) (pullback.diagonal_fst h)).exists.choose).hom ≫
      (normal P d h aY e w).hom =
      (source P d h aY e w N).hom ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor.map
          ((Dnc.existsUnique_dncInvariance P d (pullback.fst p p) (p ≫ aY)
            (pullback.diagonal p) (pullback.diagonal_fst p)).exists.choose).hom ∧
    (beta P d h aY N).hom =
      (normal P d h aY e w).hom ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor.map
          (beta P d p aY N).hom ≫ (tate P d aY e t).hom ∧
    FrameIndependence P d h aY N t

attribute [local irreducible] normalBundleComparison

private theorem frame_independence (P : PurityFiniteSetting.{u}) {U Y : Scheme.{u}}
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (N : Etale.EtaleCompactSupportNormalization P.Coefficient)
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) : FrameIndependence P d h aY N t := by
  let := P.noetherian (h ≫ aY)
  let := (chartDiagonalNormalBundle d h).1
  let F := ConormalGradedAlgebra.piece (pullback.diagonal h) 1
  intro D W f G
  let : IsNoetherian W.toScheme := ⟨⟩
  let m := Etale.FiniteRingSectionDeformation.bundleSectionAdjoint P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
    P.diagonalExponent_annihilates U (P.diagonalExponent_isUnit (h ≫ aY)) d F
  let ν := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) U).mapDerivedCategory
  let νW := (ProEtale.comparisonUpperStar
    (ModuleCat.{u + 1} P.Coefficient) W.toScheme).mapDerivedCategory
  let L := (ProEtale.upperStar
    (ModuleCat.{u + 1} P.Coefficient) W.ι).leftDerivedFunctor
  let η : ν ⋙ L ≅ Etale.ordinaryFinitePullback P.Coefficient W.ι ⋙ νW :=
    Functor.isoWhiskerLeft ν (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory _ W.ι) ≪≫
      ProEtale.mapDerivedCategoryComparisonUpperStarCompUpperStarIso _ W.ι ≪≫
        Functor.isoWhiskerRight
          (Etale.leftDerivedUpperStarIsoMapDerivedCategory _ W.ι).symm νW
  have hn := η.hom.naturality m
  change L.map (ν.map m) ≫ (Dnc.pullComparison P W.ι _).hom =
    (Dnc.pullComparison P W.ι _).hom ≫
      νW.map ((Etale.ordinaryFinitePullback P.Coefficient W.ι).map m) at hn
  simp only [beta, Iso.trans_inv, Functor.mapIso_inv, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  change L.map (ν.map m) ≫ (Dnc.pullComparison P W.ι _).hom ≫ _ = _
  rw [reassoc_of% hn, ← Functor.map_comp]
  exact congrArg (fun k ↦ (Dnc.pullComparison P W.ι _).hom ≫ νW.map k)
    (Etale.FiniteRingSectionDeformation.bundleOrientation_frames P.diagonalExponent
      (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
      P.diagonalExponent_annihilates t D U (P.diagonalExponent_isUnit (h ≫ aY))
      d F W (G ≪≫ f))

/-- The normalized DNC and zero-section integration factors commute with an etale
coordinate chart, including non-affine U, empty U, and relative dimension zero.
Source: blueprint latest, sk-prop-sp-orientation-charts.proof.md, Steps 3--4
(blueprint: lem-pur-chart-dnc-vector-factors).

Proof, following the five DAG steps:
1. lem-pur-chart-cartesian-domain gives O by removing the complementary clopen part
   of U times_A U. Factor its etale map through U times_Y A; the normal map is the
   actual graded pullback of lem-pur-chart-normal-differential, hence normalMap.
2. By lem-pur-section-etale-restriction-coherence and exceptional locality, restriction
   to O followed by locality equals the global sourceLift locality in sourceOrdinary.
   Smooth base change is the other factor. Parts (2)--(3) of
   lem-pur-finite-etale-dualizing-normalization identify this pasted map with the
   canonical exceptional comparison for q, and similarly identify normal with b.
3. Section-etale coherence gives R_ni delta_O = delta_h R_i and
   R_nr delta_O = delta_H R_r. thm-pur-dnc-invariance gives
   B_N delta_H = e*delta_p B. Substitution cancels R_ni and R_i and proves the first
   equality. In the standard Rees chart, x_i=t*u_i, so the zero endpoint is exactly
   [a] -> [e*a], with the same sign. Normalized uniqueness excludes any extra unit.
4. cor-pur-vector-bundle-purity gives E v*gamma_A = gamma_U tau for the integration
   transpose. Invert, pull to zero, and use v z_U = z_A e to obtain the second
   equality. lem-pur-vector-integration-site-comparison identifies these very ordinary
   traces, transposes and inverses with the pro-etale maps. Tate comparison is tate,
   the canonical pullback of det-prop-sfb-cartesian-coefficients-twists.
5. lem-amb-linear-trace-invariance fixes the actual trace under every linear frame
   change. Apply bundleOrientation_frames to the conormal module on each open W
   and to the changed frame G followed by f. Its equation identifies the restricted
   bundleSectionAdjoint with the same affineSectionAdjoint for every G. The inverse
   of beta followed by normalBundleComparison is precisely this section adjoint
   transported by nu*. Natural pullComparison and the canonical Tate pullback give
   the displayed FrameIndependence equation. At rank zero the empty ordered
   integration is the identity adjunction (lem-pur-vector-trace-geometric-descent),
   and normalized DNC is the identity on the standard section invariant. Every map
   on the empty scheme is the unique map between the corresponding zero objects. -/
theorem chart_dnc_vector_factors (P : PurityFiniteSetting.{u}) (_hE : P.extension = ⊥)
    {U Y : Scheme.{u}} [IsAffine Y]
    (d : ℕ) (h : U ⟶ Y) [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [SmoothOfRelativeDimension d h]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (e : U ⟶ AffineSpace (ULift.{u} (Fin d)) Y) [Etale e]
    (w : e ≫ (AffineSpace (ULift.{u} (Fin d)) Y ↘ Y) = h) :
    Conclusion P d h aY e w := by
  let p := AffineSpace (ULift.{u} (Fin d)) Y ↘ Y
  let : SmoothOfRelativeDimension d p := by
    simpa using AffineSpace.smoothOfRelativeDimension_over (ULift.{u} (Fin d)) Y
  let := P.noetherian (h ≫ aY)
  intro N t
  refine ⟨chart_dnc_naturality P d h aY e w N, ?_,
    frame_independence P d h aY N t⟩
  have hi := chart_integration_adjoints P d h aY e w N t
  let L := (ProEtale.upperStar
    (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor
  let b := L.mapIso (beta P d p aY N)
  have hb : b.inv ≫ b.hom = 𝟙 _ := b.inv_hom_id
  change (L.map (beta P d p aY N).inv) ≫ L.map (beta P d p aY N).hom = 𝟙 _ at hb
  apply (cancel_mono (tate P d aY e t).inv).mp
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply (cancel_epi (beta P d h aY N).inv).mp
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hi]
  change (tate P d aY e t).inv =
    ((tate P d aY e t).inv ≫ L.map (beta P d p aY N).inv) ≫
      L.map (beta P d p aY N).hom
  rw [Category.assoc, hb]
  change (tate P d aY e t).inv = (tate P d aY e t).inv ≫ 𝟙 _
  exact (Category.comp_id _).symm

end WeilConjectures.PurityFiniteSetting.ChartFactors
