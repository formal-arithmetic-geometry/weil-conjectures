/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Sheaf.AlgebraicGeometry.VectorBundleZeroSection
public import Sheaf.AlgebraicGeometry.ConormalGradedAlgebra
public import Sheaf.Paper.FiniteSmoothCanonicalInterfaces
public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import Sheaf.AlgebraicGeometry.EtaleReesChart
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.CompactifiableOverField

import WeilConjectures.AlgebraicGeometry.AffineMorphismRelativeSpec
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Sheaf.RingTheory.ReesAssociatedGradedChart
import Sheaf.AlgebraicGeometry.RelativeSpecBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Compactification.NagataCompactification

/-! # Noetherian geometry of the extended-Rees deformation of a smooth section

Source: main-20261015, sec-smooth-purity/sk-thm-dnc/sk-thm-dnc.proof.md,
Local construction; Stacks Tags 01LX, 01T6, 0630--0633 and Nagata compactification.
(blueprint: lem-trf-section-rees-noetherian-geometry).

The spaces, section and fibre maps are the published extended-Rees constructions.
The zero-fibre comparison is the normalized associated-graded comparison followed
by relative Spec of the canonical symmetric-to-graded morphism. No orientation,
compactification, or regular-sequence hypothesis is supplied as additional input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.SectionReesNoetherianGeometry

/-- The specified comparison from the Rees zero fibre to Spec Sym(I/I²).
It is relative Spec of the canonical symmetric comparison, preceded by the existing
homogeneous-normalized Rees/associated-graded comparison. Its data is a composite
of the existing functors and morphisms, independently of whether it is an isomorphism.
Source: sk-thm-dnc, Local construction; Stacks 0630--0633 and 01LX
(blueprint: lem-trf-section-rees-noetherian-geometry). -/
def coneToBundle {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (s : S ⟶ V)
    [IsClosedImmersion s] [(ConormalGradedAlgebra.piece s 1).IsFiniteLocallyFreeOfRank d] :
    s.ker.normalCone ⟶ VectorBundleZeroSection.scheme S d (ConormalGradedAlgebra.piece s 1) :=
  (Etale.FiniteSmoothPurity.reesConeComparison s).hom ≫
    ((VectorBundleZeroSection.antiEquivalence S).inverse.map
      (ObjectProperty.homMk (ConormalGradedAlgebra.symmetricComparison s) :
        VectorBundleZeroSection.algebraObject S d (ConormalGradedAlgebra.piece s 1) ⟶
          PurityNormalBundle.algebraObject s)).unop.hom.left

/-- Conormal rank, Noetherian geometry, compactifiability, and the three identifications
of pairs, with their actual canonical maps.
Source: sk-thm-dnc, Local construction; Stacks 01LX, 0630--0633, 01T6, 01KU, 01KT.
(blueprint: lem-trf-section-rees-noetherian-geometry).

Proof: Step 1 uses lem-trf-smooth-section-centred-coordinates: centred etale
coordinates generate the ideal by a regular sequence, identify its conormal with
O_S^d, and identify Sym(I/I²) with gr_I by the monomial formula. Steps 2--3 glue the
localized extended-Rees algebras and their augmentations, giving the actual scheme
and section; inverting t gives the punctured product and setting t=1 gives V.
Step 4 applies lem-pur-rees-associated-graded-chart, [b]_m ↦ [b t^(-m)], and the
canonical symmetric comparison. These maps commute with localization, so relative
Spec glues their identifications and preserves augmentation. Steps 5--7 apply
lem-pur-dnc-etale-rees-chart on every centred chart and use the punctured product
off the centre; these opens cover, proving smoothness of relative dimension d.
Step 8 uses the affine map D→A¹_V and separated base change/composition; the section
of this separated map is closed. Step 9 uses quasi-compactness of D→V, finite type
of V/S, smoothness of q and qcqs permanence to obtain finite type of q and Noetherian D.
Step 10 uses polynomial charts of the conormal bundle to obtain Noetherian total
space and a separated finite-type projection. Step 12 applies Nagata to q and π,
whose targets are Noetherian and thus qcqs. The argument includes d=0 and empty S. -/
theorem geometry {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [LocallyOfFiniteType g]
    [QuasiCompact g] (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) :
    ∃ hE : (ConormalGradedAlgebra.piece s 1).IsFiniteLocallyFreeOfRank d,
      ∃ e : s.ker.normalCone ≅
        @VectorBundleZeroSection.scheme S inferInstance d (ConormalGradedAlgebra.piece s 1) hE,
      e.hom = @coneToBundle V S inferInstance d s inferInstance hE ∧
      e.hom ≫ @VectorBundleZeroSection.π S inferInstance d
          (ConormalGradedAlgebra.piece s 1) hE = Scheme.Hom.normalConeProj g s ∧
      s.normalConeZeroSection ≫ e.hom = @VectorBundleZeroSection.zero S inferInstance d
          (ConormalGradedAlgebra.piece s 1) hE ∧
      s.deformationSpaceSection ≫ Scheme.Hom.deformationSpaceProj g s = 𝟙 _ ∧
      IsNoetherian (AffineSpace (ULift.{u} (Fin 1)) S) ∧
      IsNoetherian s.ker.deformationSpace ∧
      SmoothOfRelativeDimension d (Scheme.Hom.deformationSpaceProj g s) ∧
      IsSeparated (Scheme.Hom.deformationSpaceProj g s) ∧
      LocallyOfFiniteType (Scheme.Hom.deformationSpaceProj g s) ∧
      QuasiCompact (Scheme.Hom.deformationSpaceProj g s) ∧
      IsClosedImmersion s.deformationSpaceSection ∧
      HasCompactification (Scheme.Hom.deformationSpaceProj g s) ∧
      IsNoetherian (@VectorBundleZeroSection.scheme S inferInstance d
        (ConormalGradedAlgebra.piece s 1) hE) ∧
      HasCompactification (@VectorBundleZeroSection.π S inferInstance d
        (ConormalGradedAlgebra.piece s 1) hE) ∧
      IsPullback (Scheme.Hom.deformationSpaceOneFibre g s) g
        (Scheme.Hom.deformationSpaceProj g s)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S) ∧
      s ≫ Scheme.Hom.deformationSpaceOneFibre g s =
        AffineSpace.oneSection (ULift.{u} (Fin 1)) S ≫ s.deformationSpaceSection ∧
      IsPullback s.ker.normalConeToDeformationSpace (Scheme.Hom.normalConeProj g s)
        (Scheme.Hom.deformationSpaceProj g s)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S) ∧
      s.normalConeZeroSection ≫ s.ker.normalConeToDeformationSpace =
        AffineSpace.zeroSection (ULift.{u} (Fin 1)) S ≫ s.deformationSpaceSection ∧
      IsPullback (Scheme.Hom.deformationSpaceGeneric g s) (pullback.snd _ _)
        (Scheme.Hom.deformationSpaceProj g s) (Scheme.Hom.puncturedLine S).ι ∧
      (∃ σ : (Scheme.Hom.puncturedLine S).toScheme ⟶
          pullback g ((Scheme.Hom.puncturedLine S).ι ≫
            (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)),
        σ ≫ pullback.fst _ _ = ((Scheme.Hom.puncturedLine S).ι ≫
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)) ≫ s ∧
        σ ≫ pullback.snd _ _ = 𝟙 _ ∧
        σ ≫ Scheme.Hom.deformationSpaceGeneric g s =
          (Scheme.Hom.puncturedLine S).ι ≫ s.deformationSpaceSection) := by
  sorry

/-- On every centred affine etale chart the actual Rees algebra is the canonical
base change of R[t,u₁,...,u_d], with x_j=t*u_j. The tensor factor in the domain of
etaleReesTensorMap is the origin extended-Rees algebra; the displayed equivalence
identifies that factor with precisely this polynomial algebra, including its P-action.
Source: sk-thm-dnc, Local construction, Step 5
(blueprint: lem-trf-section-rees-noetherian-geometry).
Proof: apply lem-pur-dnc-etale-rees-chart with A=Γ(S,W), R=Γ(V,U), and C=A[x].
The hypothesis on the mapped origin ideal is exactly I=(x)B. The canonical tensor
map is bijective by flat etale base change. The polynomial origin-Rees equivalence
sends x_j to t*u_j and fixes R[t]. Thus this is the displayed B tensor_P R[t,u]
identification with its prescribed map, rather than an arbitrary ring isomorphism.
The relative-spectrum construction identifies Spec of this Rees algebra with the
open over U of the deformation; localization gives the same charts on refinements.
The polynomial chart targets and all their opens are Noetherian. The etale chart
maps are affine, hence separated, and finite type by Noetherian quasi-compactness.
Their structural composites and every separated finite-type map from a Noetherian
chart source into a chart-target open therefore admit Nagata compactifications. -/
theorem affine_chart {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [LocallyOfFiniteType g]
    [QuasiCompact g] (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (W : S.affineOpens) (U : V.AffineZariskiSite) (hUW : U.1 ≤ g ⁻¹ᵁ W.1)
    (ψ : MvPolynomial (Fin d) Γ(S, W.1) →+* Γ(V, U.1)) (hψ : ψ.Etale)
    (hC : ψ.comp MvPolynomial.C = (g.appLE W.1 U.1 hUW).hom)
    (hcentre : s ⁻¹ᵁ U.1 = W.1)
    (hI : (Ideal.mvPolynomialOrigin Γ(S, W.1) (Fin d)).map ψ = s.ker.siteIdeal U) :
    IsNoetherian (Spec (.of
      ((Ideal.mvPolynomialOrigin Γ(S, W.1) (Fin d)).map ψ).extendedReesAlgebra)) ∧
    IsNoetherian (Spec (.of (Polynomial Γ(S, W.1)))) ∧
    IsNoetherian (Spec (.of (MvPolynomial (Fin d) (Polynomial Γ(S, W.1))))) ∧
    HasCompactification (Spec.map (CommRingCat.ofHom
      (@etaleReesChartMap Γ(S, W.1) Γ(V, U.1) inferInstance inferInstance d ψ.toAlgebra))) ∧
    HasCompactification (Spec.map (CommRingCat.ofHom
        (@etaleReesChartMap Γ(S, W.1) Γ(V, U.1) inferInstance inferInstance d ψ.toAlgebra)) ≫
      Spec.map (CommRingCat.ofHom (etaleReesBaseMap Γ(S, W.1) d))) ∧
    HasCompactification (Spec.map (CommRingCat.ofHom
        (@etaleReesChartMap Γ(S, W.1) Γ(V, U.1) inferInstance inferInstance d ψ.toAlgebra)) ≫
      Spec.map (CommRingCat.ofHom (etaleReesBaseMap Γ(S, W.1) d)) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(S, W.1) →+* Polynomial Γ(S, W.1))) ≫
      W.2.isoSpec.inv ≫ W.1.ι) ∧
    (∀ O : (Spec (.of (MvPolynomial (Fin d) (Polynomial Γ(S, W.1))))).Opens,
      IsNoetherian O.toScheme ∧ HasCompactification O.ι ∧
      HasCompactification (O.ι ≫
        Spec.map (CommRingCat.ofHom (etaleReesBaseMap Γ(S, W.1) d))) ∧
      HasCompactification (O.ι ≫
        Spec.map (CommRingCat.ofHom (etaleReesBaseMap Γ(S, W.1) d)) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(S, W.1) →+* Polynomial Γ(S, W.1))) ≫
        W.2.isoSpec.inv ≫ W.1.ι) ∧
      ∀ (T : Scheme.{u}), IsNoetherian T → ∀ a : T ⟶ O.toScheme,
        IsSeparated a → LocallyOfFiniteType a → QuasiCompact a →
        HasCompactification a ∧ HasCompactification (a ≫ O.ι) ∧
        HasCompactification (a ≫ O.ι ≫
          Spec.map (CommRingCat.ofHom (etaleReesBaseMap Γ(S, W.1) d))) ∧
        HasCompactification (a ≫ O.ι ≫
          Spec.map (CommRingCat.ofHom (etaleReesBaseMap Γ(S, W.1) d)) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(S, W.1) →+* Polynomial Γ(S, W.1))) ≫
          W.2.isoSpec.inv ≫ W.1.ι)) ∧
    Function.Bijective
      (@etaleReesTensorMap Γ(S, W.1) Γ(V, U.1) inferInstance inferInstance d ψ.toAlgebra) ∧
    (∀ j : Fin d,
      (Ideal.mvPolynomialExtendedReesAlgebraEquiv Γ(S, W.1) (Fin d)).symm
        (algebraMap (MvPolynomial (Fin d) Γ(S, W.1))
          (Ideal.mvPolynomialOrigin Γ(S, W.1) (Fin d)).extendedReesAlgebra
            (MvPolynomial.X j)) = MvPolynomial.C Polynomial.X * MvPolynomial.X j) ∧
    (∃ e : (s.ker.deformationSpaceProj ⁻¹ᵁ U.1).toScheme ≅
        Spec (.of (s.ker.siteIdeal U).extendedReesAlgebra),
      e.hom ≫ Spec.map (CommRingCat.ofHom
          (algebraMap Γ(V, U.1) (s.ker.siteIdeal U).extendedReesAlgebra)) ≫
          U.2.isoSpec.inv ≫ U.1.ι =
        (s.ker.deformationSpaceProj ⁻¹ᵁ U.1).ι ≫ s.ker.deformationSpaceProj) := by
  sorry

/-- Centred Rees-chart opens together with the punctured deformation cover the whole
space. Every chart appearing here has the exact ideal and coefficient map in affine_chart.
Source: sk-thm-dnc, Local construction, Steps 1, 5--7
(blueprint: lem-trf-section-rees-noetherian-geometry).
Proof: lem-trf-smooth-section-centred-coordinates supplies such affine charts around
every point of s(S). Away from that centre I is the unit ideal, so 1/t belongs to the
extended Rees algebra and t is invertible. Hence every point not in the punctured
open lies over the centre and belongs to one of the stated centred-chart opens. -/
theorem chart_cover {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [LocallyOfFiniteType g]
    [QuasiCompact g] (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    (x : s.ker.deformationSpace) :
    x ∈ (Scheme.Hom.deformationSpaceProj g s) ⁻¹ᵁ Scheme.Hom.puncturedLine S ∨
      ∃ (W : S.affineOpens) (U : V.AffineZariskiSite) (hUW : U.1 ≤ g ⁻¹ᵁ W.1)
        (ψ : MvPolynomial (Fin d) Γ(S, W.1) →+* Γ(V, U.1)),
        ψ.Etale ∧ ψ.comp MvPolynomial.C = (g.appLE W.1 U.1 hUW).hom ∧
        s ⁻¹ᵁ U.1 = W.1 ∧
        (Ideal.mvPolynomialOrigin Γ(S, W.1) (Fin d)).map ψ = s.ker.siteIdeal U ∧
        x ∈ s.ker.deformationSpaceProj ⁻¹ᵁ U.1 := by
  sorry

/-- Open restrictions and separated finite-type chart maps into either the bundle or
its deformation, and all their structural composites, have Noetherian ends and admit
compactifications. The Noetherian chart-source assumption is explicit for chart maps.
Source: sk-thm-dnc, Local construction, Steps 9--12; Stacks 01OW, 01OZ, 01T6; Nagata.
(blueprint: lem-trf-section-rees-noetherian-geometry).
Proof: Steps 9--10 of the node make D, A¹_S and the bundle Noetherian and their
structural projections separated finite type. Step 11 restricts to arbitrary opens:
opens of Noetherian schemes are Noetherian and their inclusions are quasi-compact,
separated and locally finite type, hence finite type. A separated finite-type chart
map from a Noetherian source remains separated finite type after composition with
these inclusions and projections (qcqs and separated/finite-type permanence).
Step 12 applies thm-nagata-compactification to each arrow, using its Noetherian,
hence quasi-compact quasi-separated target. No finite-dimensionality is used. -/
theorem chart_compactifications {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [LocallyOfFiniteType g]
    [QuasiCompact g] (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) :
    ∃ hE : (ConormalGradedAlgebra.piece s 1).IsFiniteLocallyFreeOfRank d,
      (∀ U : s.ker.deformationSpace.Opens,
        IsNoetherian U.toScheme ∧ HasCompactification U.ι ∧
        HasCompactification (U.ι ≫ Scheme.Hom.deformationSpaceProj g s) ∧
        HasCompactification (U.ι ≫ Scheme.Hom.deformationSpaceProj g s ≫
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)) ∧
        ∀ (T : Scheme.{u}), IsNoetherian T → ∀ a : T ⟶ U.toScheme,
          IsSeparated a → LocallyOfFiniteType a → QuasiCompact a →
          HasCompactification a ∧ HasCompactification (a ≫ U.ι) ∧
          HasCompactification (a ≫ U.ι ≫ Scheme.Hom.deformationSpaceProj g s) ∧
          HasCompactification (a ≫ U.ι ≫ Scheme.Hom.deformationSpaceProj g s ≫
            (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))) ∧
      (∀ U : (@VectorBundleZeroSection.scheme S inferInstance d
          (ConormalGradedAlgebra.piece s 1) hE).Opens,
        IsNoetherian U.toScheme ∧ HasCompactification U.ι ∧
        HasCompactification (U.ι ≫ @VectorBundleZeroSection.π S inferInstance d
          (ConormalGradedAlgebra.piece s 1) hE) ∧
        ∀ (T : Scheme.{u}), IsNoetherian T → ∀ a : T ⟶ U.toScheme,
          IsSeparated a → LocallyOfFiniteType a → QuasiCompact a →
          HasCompactification a ∧ HasCompactification (a ≫ U.ι) ∧
          HasCompactification (a ≫ U.ι ≫ @VectorBundleZeroSection.π S inferInstance d
            (ConormalGradedAlgebra.piece s 1) hE)) := by
  sorry

end AlgebraicGeometry.SectionReesNoetherianGeometry
