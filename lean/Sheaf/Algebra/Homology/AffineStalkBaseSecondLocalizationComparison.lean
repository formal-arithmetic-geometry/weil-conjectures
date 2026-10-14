/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Base and second-factor localization after taking the affine input stalk

Source: Stacks Project, Tags 0DJ8 and 06Y6.
(blueprint: new-affine-stalk-base-second-localization-comparison). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- Localize only the base and second factor of an already stalk-localized input.
Source: Stacks Project, Tag 0DJ8, base and second-factor part of the localization
identity; Tag 06Y6.
(blueprint: new-affine-stalk-base-second-localization-comparison).

Proof: the maps from R and R' to their spectrum stalks are prime localizations.
Their maps into the A-stalk and D agree by stalk-map naturality and the cartesian
square. The two restriction equations for psi identify its coefficient actions
with those of the actual tensor-to-stalk map. Apply base and second-factor
localization to Q, keeping the A-stalk unchanged. First compare m with a model
over R and R' in the standard universe using
exists_baseDerivedTensor_restricted_ring_comparison with identity ring equivalences.
Its scalar-action clause and tensor induction upgrade the second-ring-linear
isomorphism to Aq tensor_R R'-linearity. Its ordinary comparison clause,
localized_eq and scalar-extension adjunction give the localized square. Now
apply derivedTensor_base_second_localization_models in that standard universe.
These comparisons preserve the A-stalk action by cohomologyIso_smul.
Extend the resulting tensor-algebra-linear isomorphism to D. The augmentations
of the common resolutions yield a commuting localizedComparison square.
The ordinary targets have the same A-stalk-to-D map, so their canonical chain
isomorphism sends d tensor q to d tensor q. For a compatible tau, set sigma to beta inverse
followed by tau. The formula for beta and its inverse identity show that sigma
agrees with the canonical map on 1 tensor germs of M. These generate C1: beta is an isomorphism, and
1 tensor x generate C. ExtendScalars.hom_ext and D-linearity prove equality
of the chain maps. Taking homology gives the equation for every such sigma.
Zero complexes and identity localizations give the same comparison; a zero A'
has no prime p. No first-factor localization is asserted or used here. -/
theorem exists_affineStalkBaseSecondLocalizationComparison
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra (A ⊗[R] R') A']
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R')]
    (φg' : A →+* A') (φf' : R' →+* A')
    (hφg' : (algebraMap (A ⊗[R] R') A').comp
      (algebraMap A (A ⊗[R] R')) = φg')
    (hφf' : (algebraMap (A ⊗[R] R') A').comp
      Algebra.TensorProduct.includeRight.toRingHom = φf')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (i : ℤ)
    (p : PrimeSpectrum A') :
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
      let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
      let f' := Spec.map (CommRingCat.ofHom φf')
      let g := Spec.map (CommRingCat.ofHom (algebraMap R R'))
      let g' := Spec.map (CommRingCat.ofHom φg')
      let D : Type u := (Spec.structureSheaf A').presheaf.stalk p
      let κ := (StructureSheaf.toStalk A' p).hom
      let Aq : Type u := (Spec.structureSheaf A).presheaf.stalk (g' p)
      let κA := (StructureSheaf.toStalk A (g' p)).hom
      let α := (g'.stalkMap p).hom
      letI : Algebra R Aq := (κA.comp (algebraMap R A)).toAlgebra
      (ψ : Aq ⊗[R] R' →+* D) →
      ψ.comp (algebraMap Aq (Aq ⊗[R] R')) = α →
      ψ.comp Algebra.TensorProduct.includeRight.toRingHom = κ.comp φf' →
      letI := ψ.toAlgebra
      let Q := SingleComplexBaseChange.stalkComplex g' p P
      (m : ModuleCat.BaseDerivedTensorCohomologyModel R Aq R' Q D) →
      let C := ((ModuleCat.extendScalars (κ.comp φg')).mapHomologicalComplex (.up ℤ)).obj M
      let φ₁ := ψ.comp (algebraMap Aq (Aq ⊗[R] R'))
      let C₁ := ((ModuleCat.extendScalars φ₁).mapHomologicalComplex (.up ℤ)).obj Q
      (β : C ≅ C₁) →
      (∀ (j : ℤ) (x : M.X j),
        β.hom.f j ((1 : D) ⊗ₜ[A, κ.comp φg'] x) =
          (1 : D) ⊗ₜ[Aq, φ₁]
            (TopCat.Presheaf.germ (P.X j).val.presheaf ⊤ (g' p) trivial
              (tilde.toOpen (R := .of A) (M.X j) ⊤ x))) →
      letI := SingleComplexBaseChange.leftAlgebra f g' p
      letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
      letI := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
      let ρ := (SingleComplexBaseChange.tensorMap f f' g g' sq p).comp
        (algebraMap (SingleComplexBaseChange.A g' p)
          (SingleComplexBaseChange.A g' p ⊗[SingleComplexBaseChange.R f g' p]
            SingleComplexBaseChange.B f' p))
      let l :=
        (SingleComplexBaseChange.cohomologyModel f f' g g' sq p P).localizedComparison i
      ∃ e : (ModuleCat.extendScalars ψ).obj (m.cohomology i) ≅ (Arrow.mk l).left,
        ∀ τ : C ≅ SingleComplexBaseChange.tensorComplex f f' g g' sq p P,
          (∀ (j : ℤ) (x : M.X j),
            τ.hom.f j ((1 : D) ⊗ₜ[A, κ.comp φg'] x) =
              (1 : (Spec (.of A')).presheaf.stalk p) ⊗ₜ[SingleComplexBaseChange.A g' p, ρ]
                (TopCat.Presheaf.germ (P.X j).val.presheaf ⊤ (g' p) trivial
                  (tilde.toOpen (R := .of A) (M.X j) ⊤ x))) →
          m.localizedComparison i ≫ HomologicalComplex.homologyMap
            (β.inv ≫ τ.hom) i = e.hom ≫ l := by sorry

end AlgebraicGeometry
