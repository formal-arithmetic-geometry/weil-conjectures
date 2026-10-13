/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S4
-/
module

public import Sheaf.Algebra.Homology.AffineOrdinaryTensorStalkCoordinates
public import Mathlib.Algebra.Category.ModuleCat.Descent
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat

/-! # AffineScalarLocalizedTensorSquare

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-scalar-localized-tensor-square). -/

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

/-- Algebraic comparison after extension to the fourth stalk ring, before exact
stalk homology coordinates. Source: Stacks Project, Tag 0DJ8, affine displayed
localization identity; Tags 06Y6, 01HV and 01I9.
(blueprint: lem-pc-affine-scalar-localized-tensor-square).

Proof: the cartesian spectrum square identifies A' with A tensor_R R'. Its fourth
stalk D is the localization at p; the other three stalk rings are localizations
at the contracted primes. Identify the stalk complex of tilde M with the
localization of M, sending 1 tensor x to its germ. Compute the global and local
base-derived tensors using K-flat resolutions. First localize the A-factor,
then the base and second factor. Exact localization commutes with cohomology
and tensor associativity identifies both extensions to D. The universal counit
and coefficient-action equations transport the resulting source isomorphism to
the supplied global model and the fixed local model, giving e. The same counit
squares identify the localized comparison with extension of a0 followed by the
inverse exact scalar-extension homology isomorphism. In the target chain
coordinates both coefficient maps send 1 tensor (1 tensor x) to 1 tensor the
germ of x. D-linearity and tensor generation therefore prove their equality for
every tau with this formula. Taking homology gives the displayed square. No
homology of the tilde of the ordinary target, nor a localization of U expressed
as fractions, occurs here. The argument applies to zero complexes and identity
localizations; the zero fourth ring has no primes. -/
theorem exists_affineScalarLocalizedTensorSquare
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
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat M)
    (i : ℤ) (m : ModuleCat.BaseDerivedTensorCohomologyModel R A R' M A') :
    let P := ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)
    let C := ((ModuleCat.extendScalars φg').mapHomologicalComplex (.up ℤ)).obj M
    let U := affineBaseChangeTildeModule R A R' A' M m i
    let a₀ := affineBaseChangeTildeModuleMap R A R' A' M m φg' hφg' i
      (C.homology i) (Iso.refl _)
    (p : PrimeSpectrum A') →
      let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
      let f' := Spec.map (CommRingCat.ofHom φf')
      let g := Spec.map (CommRingCat.ofHom (algebraMap R R'))
      let g' := Spec.map (CommRingCat.ofHom φg')
      letI := SingleComplexBaseChange.leftAlgebra f g' p
      letI := SingleComplexBaseChange.rightAlgebra f f' g g' sq p
      letI := (SingleComplexBaseChange.tensorMap f f' g g' sq p).toAlgebra
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.R f g' p))
      letI := HasDerivedCategory.standard (ModuleCat.{u} (SingleComplexBaseChange.B f' p))
      let D : Type u := (Spec.structureSheaf A').presheaf.stalk p
      let κ := (StructureSheaf.toStalk A' p).hom
      let F := ModuleCat.extendScalars κ
      letI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
        (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat D p.asIdeal.primeCompl))
      let ρ := (SingleComplexBaseChange.tensorMap f f' g g' sq p).comp
        (algebraMap (SingleComplexBaseChange.A g' p)
          (SingleComplexBaseChange.A g' p ⊗[SingleComplexBaseChange.R f g' p]
            SingleComplexBaseChange.B f' p))
      let l :=
        (SingleComplexBaseChange.cohomologyModel f f' g g' sq p P).localizedComparison i
      ∃ e : F.obj U ≅ (Arrow.mk l).left,
        ∀ τ : (F.mapHomologicalComplex (.up ℤ)).obj C ≅
            SingleComplexBaseChange.tensorComplex f f' g g' sq p P,
          (∀ (j : ℤ) (x : M.X j),
            τ.hom.f j ((1 : D) ⊗ₜ[A', κ] ((1 : A') ⊗ₜ[A, φg'] x)) =
              (1 : (Spec (.of A')).presheaf.stalk p) ⊗ₜ[SingleComplexBaseChange.A g' p, ρ]
                (TopCat.Presheaf.germ (P.X j).val.presheaf ⊤ (g' p) trivial
                  (tilde.toOpen (R := .of A) (M.X j) ⊤ x))) →
          F.map a₀ ≫ ((C.sc i).mapHomologyIso F).inv ≫
              HomologicalComplex.homologyMap τ.hom i = e.hom ≫ l := by sorry

end AlgebraicGeometry
