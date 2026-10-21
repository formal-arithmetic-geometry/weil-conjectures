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

import Sheaf.AlgebraicGeometry.SmoothSectionCentredCoordinates
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth

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

private theorem etale_comp {B C D : Type*} [CommRing B] [CommRing C] [CommRing D]
    (f : B →+* C) (g : C →+* D) (hf : f.Etale) (hg : g.Etale) :
    (g.comp f).Etale := by
  algebraize [f, g, g.comp f]
  exact Algebra.Etale.comp B C D

private theorem noetherian_open {Y : Scheme.{u}} [IsNoetherian Y] (U : Y.Opens) :
    IsNoetherian U.toScheme := by
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isInducing.noetherianSpace
  have : CompactSpace U.toScheme := TopologicalSpace.NoetherianSpace.compactSpace _
  exact ⟨⟩

private theorem compactifiable {Y Z : Scheme.{u}} [IsNoetherian Z] (f : Y ⟶ Z)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] : HasCompactification f :=
  (NagataCompactification f).hasCompactification

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem augmentation_inclusion {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    (ConormalGradedAlgebra.presentation i).inclusion 1 ≫
      (commAlgebraSheafModuleFunctor Z.sheaf).map
        (ConormalGradedAlgebra.augmentation i) = 0 := by
  let adj := (Scheme.Modules.exists_tensorPullbackAdjunction i).choose
  apply (adj.homEquiv (ConormalGradedAlgebra.power i 1) _).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext a
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  change (ConormalGradedAlgebra.augmentation i).right.hom.app (op (i ⁻¹ᵁ U.unop))
    (ConormalGradedAlgebra.homogeneousClass i _ _ 1 U.unop a) = 0
  have h := (ConormalGradedAlgebra.presentation i).augmentation.exists.choose_spec
  simpa only [ConormalGradedAlgebra.augmentation, Nat.one_ne_zero, ↓reduceIte] using
    h 1 U.unop a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem augmentation_comparison {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] :
    ConormalGradedAlgebra.symmetricComparison i ≫ PurityNormalBundle.augmentationToBase i =
      VectorBundleZeroSection.augmentationToBase Z (ConormalGradedAlgebra.piece i 1) := by
  apply ExistsUnique.unique (exists_quasiCoherentSymmetricAlgebra_core Z
    (ConormalGradedAlgebra.piece i 1)
    (((VectorBundleZeroSection.antiEquivalence Z).functor.obj
      (op (VectorBundleZeroSection.baseObject Z))).obj) 0)
  · intro U a
    change (PurityNormalBundle.augmentationToBase i).right.hom.app (op U)
      ((ConormalGradedAlgebra.symmetricComparison i).right.hom.app (op U)
        ((SymmetricAlgebraSheaf.inclusion _).val.app (op U) a)) = 0
    dsimp only [ConormalGradedAlgebra.symmetricComparison]
    rw [(ConormalGradedAlgebra.presentation i).symmetricComparison.exists.choose_spec]
    have h := congrArg (fun q ↦ q.val.app (op U) a) (augmentation_inclusion i)
    change (((VectorBundleZeroSection.antiEquivalence Z).functor.obj
      (op (VectorBundleZeroSection.baseObject Z))).obj.hom.hom.app (op U))
        ((ConormalGradedAlgebra.augmentation i).right.hom.app (op U)
          (((ConormalGradedAlgebra.presentation i).inclusion 1).val.app (op U) a)) = 0
    change (ConormalGradedAlgebra.augmentation i).right.hom.app (op U)
      (((ConormalGradedAlgebra.presentation i).inclusion 1).val.app (op U) a) = 0 at h
    rw [h, map_zero]
  · exact (exists_quasiCoherentSymmetricAlgebra_core Z
      (ConormalGradedAlgebra.piece i 1)
      (((VectorBundleZeroSection.antiEquivalence Z).functor.obj
        (op (VectorBundleZeroSection.baseObject Z))).obj) 0).exists.choose_spec

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
  classical
  obtain ⟨_, _, hE, hSym⟩ :=
    SmoothSectionCentredCoordinates.exists_centred_coordinates d g s hs
  let := hE
  let := hSym
  let E := VectorBundleZeroSection.antiEquivalence S
  let A := VectorBundleZeroSection.algebraObject S d (ConormalGradedAlgebra.piece s 1)
  let B := PurityNormalBundle.algebraObject s
  let f : A ≅ B := ObjectProperty.isoMk _
    (asIso (ConormalGradedAlgebra.symmetricComparison s))
  let fOver := (ObjectProperty.ι (fun Y : Over S ↦ IsAffineHom Y.hom)).mapIso
    ((E.inverse.mapIso f).unop)
  let fScheme := (Over.forget S).mapIso fOver
  let e := Etale.FiniteSmoothPurity.reesConeComparison s ≪≫ fScheme
  have he : e.hom = coneToBundle d s := rfl
  have hp : e.hom ≫ VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1) =
      Scheme.Hom.normalConeProj g s := by
    change (Etale.FiniteSmoothPurity.reesConeComparison s).hom ≫
      fScheme.hom ≫ VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1) = _
    rw [show fScheme.hom ≫ VectorBundleZeroSection.π S d
        (ConormalGradedAlgebra.piece s 1) = PurityNormalBundle.projection s from
      Over.w fOver.hom,
      (Etale.FiniteSmoothPurity.reesConeComparison_spec s).1,
      Scheme.Hom.purityNormalProjection_eq s g hs]
  have hz : PurityNormalBundle.zeroSection s ≫ fScheme.hom =
      VectorBundleZeroSection.zero S d (ConormalGradedAlgebra.piece s 1) := by
    have h :
        E.inverse.map f.hom ≫
          E.functor.preimage ((E.counitIso.app B).hom ≫
            ObjectProperty.homMk (PurityNormalBundle.augmentationToBase s)) =
        E.functor.preimage ((E.counitIso.app A).hom ≫
          ObjectProperty.homMk (VectorBundleZeroSection.augmentationToBase S
            (ConormalGradedAlgebra.piece s 1))) := by
      apply E.functor.map_injective
      simp only [Functor.map_comp, Functor.map_preimage]
      have hn := E.counitIso.hom.naturality f.hom
      dsimp only [Functor.comp_map, Functor.id_map] at hn
      erw [← Category.assoc, hn, Category.assoc]
      apply congrArg (fun q ↦ (E.counitIso.app A).hom ≫ q)
      apply ObjectProperty.hom_ext
      exact augmentation_comparison s
    exact congrArg (fun q ↦ q.unop.hom.left) h
  have hz' : s.normalConeZeroSection ≫ e.hom =
      VectorBundleZeroSection.zero S d (ConormalGradedAlgebra.piece s 1) := by
    rw [show e.hom = (Etale.FiniteSmoothPurity.reesConeComparison s).hom ≫
        fScheme.hom from rfl, ← Category.assoc,
      (Etale.FiniteSmoothPurity.reesConeComparison_spec s).2.1, hz]
  have hq := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  have : Smooth (Scheme.Hom.deformationSpaceProj g s) :=
    SmoothOfRelativeDimension.smooth d _
  have : IsLocallyNoetherian (AffineSpace (ULift.{u} (Fin 1)) S) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
  have : CompactSpace (AffineSpace (ULift.{u} (Fin 1)) S) :=
    QuasiCompact.compactSpace_of_compactSpace
      (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
  have hA : IsNoetherian (AffineSpace (ULift.{u} (Fin 1)) S) := ⟨⟩
  have : IsLocallyNoetherian s.ker.deformationSpace :=
    LocallyOfFiniteType.isLocallyNoetherian (Scheme.Hom.deformationSpaceProj g s)
  have : CompactSpace s.ker.deformationSpace :=
    QuasiCompact.compactSpace_of_compactSpace (Scheme.Hom.deformationSpaceProj g s)
  have hD : IsNoetherian s.ker.deformationSpace := ⟨⟩
  have hpb := Scheme.Hom.isPullback_normalConeToDeformationSpace g s
  have : LocallyOfFiniteType (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hpb inferInstance
  have : IsSeparated (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hpb inferInstance
  have : QuasiCompact (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hpb inferInstance
  have hpi : VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1) =
      e.inv ≫ Scheme.Hom.normalConeProj g s := by rw [← hp]; simp
  have : IsSeparated (VectorBundleZeroSection.π S d
      (ConormalGradedAlgebra.piece s 1)) := by rw [hpi]; infer_instance
  have : LocallyOfFiniteType (VectorBundleZeroSection.π S d
      (ConormalGradedAlgebra.piece s 1)) := by rw [hpi]; infer_instance
  have : QuasiCompact (VectorBundleZeroSection.π S d
      (ConormalGradedAlgebra.piece s 1)) := by rw [hpi]; infer_instance
  have : IsLocallyNoetherian (VectorBundleZeroSection.scheme S d
      (ConormalGradedAlgebra.piece s 1)) :=
    LocallyOfFiniteType.isLocallyNoetherian (VectorBundleZeroSection.π S d _)
  have : CompactSpace (VectorBundleZeroSection.scheme S d
      (ConormalGradedAlgebra.piece s 1)) :=
    QuasiCompact.compactSpace_of_compactSpace (VectorBundleZeroSection.π S d _)
  have hN : IsNoetherian (VectorBundleZeroSection.scheme S d
      (ConormalGradedAlgebra.piece s 1)) := ⟨⟩
  have hsect := Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs
  have : IsClosedImmersion (s.deformationSpaceSection ≫
      Scheme.Hom.deformationSpaceProj g s) := hsect ▸ inferInstance
  have hclosed : IsClosedImmersion s.deformationSpaceSection :=
    IsClosedImmersion.of_comp _ (Scheme.Hom.deformationSpaceProj g s)
  refine ⟨hE, e, he, hp, hz', hsect, hA, hD, hq, inferInstance, inferInstance,
    inferInstance, hclosed, inferInstance, hN, inferInstance,
    Scheme.Hom.isPullback_deformationSpaceOneFibre g s,
    Scheme.Hom.comp_deformationSpaceOneFibre hs, hpb,
    Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace (s := s),
    Scheme.Hom.isPullback_deformationSpaceGeneric g s, ?_⟩
  let P := Scheme.Hom.isPullback_deformationSpaceGeneric g s
  have hm : ((Scheme.Hom.puncturedLine S).ι ≫ s.deformationSpaceSection) ≫
      Scheme.Hom.deformationSpaceProj g s =
      (𝟙 (Scheme.Hom.puncturedLine S).toScheme) ≫ (Scheme.Hom.puncturedLine S).ι := by
    rw [Category.assoc, hsect, Category.comp_id, Category.id_comp]
  let σ := P.lift ((Scheme.Hom.puncturedLine S).ι ≫ s.deformationSpaceSection) (𝟙 _) hm
  refine ⟨σ, ?_, P.lift_snd _ _ hm, P.lift_fst _ _ hm⟩
  rw [← Scheme.Hom.deformationSpaceGeneric_toBase g s, ← Category.assoc,
    P.lift_fst, Category.assoc, Scheme.Hom.deformationSpaceSection_toBase]
  simp only [Category.assoc]


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
  have _section := hs
  have _coefficients := hC
  have _centre := hcentre
  have _ideal := hI
  let : Algebra (MvPolynomial (Fin d) Γ(S, W.1)) Γ(V, U.1) := ψ.toAlgebra
  have he : (algebraMap (MvPolynomial (Fin d) Γ(S, W.1)) Γ(V, U.1)).Etale := hψ
  have hchart := etale_rees_chart Γ(S, W.1) Γ(V, U.1) d he
  have : Algebra.Etale (MvPolynomial (Fin d) Γ(S, W.1)) Γ(V, U.1) :=
    RingHom.etale_algebraMap.mp he
  let J := Ideal.mvPolynomialOrigin Γ(S, W.1) (Fin d)
  let E := J.extendedReesAlgebra
  let D := (J.map (algebraMap (MvPolynomial (Fin d) Γ(S, W.1))
    Γ(V, U.1))).extendedReesAlgebra
  have hRees : (algebraMap E D).Etale := by
    have : Algebra.IsPushout (MvPolynomial (Fin d) Γ(S, W.1)) E Γ(V, U.1) D :=
      Algebra.IsPushout.symm inferInstance
    have : Algebra.Etale E D := Algebra.Etale.of_equiv
      (Algebra.IsPushout.equiv (MvPolynomial (Fin d) Γ(S, W.1)) E Γ(V, U.1) D)
    exact RingHom.etale_algebraMap.mpr this
  have hmap : (etaleReesChartMap Γ(S, W.1) Γ(V, U.1) d).Etale := by
    let e := Ideal.mvPolynomialExtendedReesAlgebraEquiv Γ(S, W.1) (Fin d)
    exact etale_comp e.toRingHom (algebraMap E D)
      (RingHom.Etale.of_bijective e.bijective) hRees
  have : Etale (Spec.map (CommRingCat.ofHom
      (etaleReesChartMap Γ(S, W.1) Γ(V, U.1) d))) :=
    HasRingHomProperty.Spec_iff.mpr hmap
  have : IsNoetherianRing Γ(S, W.1) := IsLocallyNoetherian.component_noetherian W
  have hpoly : IsNoetherian (Spec (.of (Polynomial Γ(S, W.1)))) := inferInstance
  have hmv : IsNoetherian
      (Spec (.of (MvPolynomial (Fin d) (Polynomial Γ(S, W.1))))) := inferInstance
  have : IsLocallyNoetherian (Spec (.of D)) :=
    LocallyOfFiniteType.isLocallyNoetherian (Spec.map (CommRingCat.ofHom
      (etaleReesChartMap Γ(S, W.1) Γ(V, U.1) d)))
  have hD : IsNoetherian (Spec (.of D)) := ⟨⟩
  have : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (etaleReesBaseMap Γ(S, W.1) d))) := by
    apply HasRingHomProperty.Spec_iff.mpr
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (Polynomial.C : Γ(S, W.1) →+* Polynomial Γ(S, W.1)))) := by
    apply HasRingHomProperty.Spec_iff.mpr
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  refine ⟨hD, hpoly, hmv, compactifiable _, compactifiable _, compactifiable _, ?_,
    hchart.2.2.1, hchart.2.1, ?_⟩
  · intro O
    have : IsNoetherian O.toScheme := noetherian_open O
    refine ⟨inferInstance, compactifiable _, compactifiable _, compactifiable _, ?_⟩
    intro T hT a ha hl hqc
    exact ⟨compactifiable _, compactifiable _, compactifiable _, compactifiable _⟩
  · let j := colimit.ι
      (Scheme.AffineZariskiSite.relativeGluingData s.ker.coequifibered_toReesPresheaf).functor U
    let e := IsOpenImmersion.isoOfRangeEq
      (s.ker.deformationSpaceProj ⁻¹ᵁ U.1).ι j
      (by
        rw [Scheme.Opens.range_ι]
        exact congrArg (fun O : s.ker.deformationSpace.Opens ↦ (O : Set s.ker.deformationSpace))
          (Scheme.AffineZariskiSite.toBase_preimage s.ker.coequifibered_toReesPresheaf U))
    refine ⟨e, ?_⟩
    change e.hom ≫ Spec.map (s.ker.toReesPresheaf.app (op U)) ≫ U.2.fromSpec = _
    rw [← Scheme.AffineZariskiSite.ι_toBase s.ker.coequifibered_toReesPresheaf U,
      ← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac]


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
  classical
  by_cases hx : x ∈ (Scheme.Hom.deformationSpaceProj g s) ⁻¹ᵁ
      Scheme.Hom.puncturedLine S
  · exact Or.inl hx
  right
  have hx0 : Scheme.Hom.deformationSpaceProj g s x ∈
      Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S).base := by
    change Scheme.Hom.deformationSpaceProj g s x ∉
      (Scheme.Hom.puncturedLine S : Set _) at hx
    rw [Scheme.Hom.coe_puncturedLine] at hx
    exact not_not.mp hx
  obtain ⟨b, hb⟩ := hx0
  obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback
    (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) x b hb.symm
  have hbase : s.ker.normalConeToDeformationSpace ≫ s.ker.deformationSpaceProj =
      Scheme.Hom.purityNormalProjection s ≫ s := by
    rw [Scheme.IdealSheafData.normalConeToDeformationSpace,
      Scheme.IdealSheafData.deformationSpaceProj]
    rw [Scheme.AffineZariskiSite.relativeGluingMap_toBase _ _ _ rfl]
    exact (IsClosedImmersion.lift_fac _ _ _).symm
  have hxy : s (Scheme.Hom.purityNormalProjection s y) = s.ker.deformationSpaceProj x := by
    rw [← Scheme.Hom.comp_apply, ← hbase, Scheme.Hom.comp_apply, hy]
  obtain ⟨⟨A, c, hc⟩, _, _, _⟩ :=
    SmoothSectionCentredCoordinates.exists_centred_coordinates d g s hs
  have hbmem : Scheme.Hom.purityNormalProjection s y ∈ (⨆ a, (c a).T.1) := by
    rw [hc]
    trivial
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp hbmem
  let C := c a
  refine ⟨C.T, ⟨C.U.1, C.U.2⟩, C.mapsInto,
    MvPolynomial.eval₂Hom (g.appLE C.T.1 C.U.1 C.mapsInto).hom C.x,
    C.algebraEtale, ?_, C.sectionPreimage, ?_, ?_⟩
  · ext r
    simp
  · simpa only [Ideal.mvPolynomialOrigin, Scheme.IdealSheafData.siteIdeal] using
      C.sectionIdeal
  · change s.ker.deformationSpaceProj x ∈ C.U.1
    rw [← hxy]
    have : Scheme.Hom.purityNormalProjection s y ∈ s ⁻¹ᵁ C.U.1 := by
      rw [C.sectionPreimage]
      exact ha
    exact this


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
  obtain ⟨hE, e, _, hp, _, _, hA, hD, hq, hsep, hft, hqc, _, _, hN, _, _⟩ :=
    geometry d g s hs
  let := hE
  have : IsSeparated (VectorBundleZeroSection.π S d
      (ConormalGradedAlgebra.piece s 1)) := by
    have : IsAffineHom (VectorBundleZeroSection.π S d
        (ConormalGradedAlgebra.piece s 1)) := (VectorBundleZeroSection.over S d _).property
    infer_instance
  have : LocallyOfFiniteType (Scheme.Hom.normalConeProj g s) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace g s) hft
  have hpi : VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1) =
      e.inv ≫ Scheme.Hom.normalConeProj g s := by rw [← hp]; simp
  have : LocallyOfFiniteType (VectorBundleZeroSection.π S d
      (ConormalGradedAlgebra.piece s 1)) := by rw [hpi]; infer_instance
  refine ⟨hE, ?_, ?_⟩
  · intro U
    have : IsNoetherian U.toScheme := noetherian_open U
    refine ⟨inferInstance, compactifiable _, compactifiable _, compactifiable _, ?_⟩
    intro T hT a ha hl hqc
    exact ⟨compactifiable _, compactifiable _, compactifiable _, compactifiable _⟩
  · intro U
    have : IsNoetherian U.toScheme := noetherian_open U
    refine ⟨inferInstance, compactifiable _, compactifiable _, ?_⟩
    intro T hT a ha hl hqc
    exact ⟨compactifiable _, compactifiable _, compactifiable _⟩


end AlgebraicGeometry.SectionReesNoetherianGeometry
