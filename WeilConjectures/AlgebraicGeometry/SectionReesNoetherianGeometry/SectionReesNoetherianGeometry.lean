/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.ConormalGradedAlgebra.ConormalGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCanonicalInterfaces
public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.RingTheory.ReesAlgebra
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField

import WeilConjectures.AlgebraicGeometry.SmoothSectionCentredCoordinates.SmoothSectionCentredCoordinates
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

end AlgebraicGeometry.SectionReesNoetherianGeometry
