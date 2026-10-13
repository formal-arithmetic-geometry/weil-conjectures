/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.AffineTorAmplitudeCriterion
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.LocalizedModule.Away
import Sheaf.Algebra.Homology.FlatOpcyclesTorCriterion
import Sheaf.AlgebraicGeometry.AffineOpenLocalizedTensorExact
import Mathlib.Algebra.Category.ModuleCat.Images
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import Mathlib.RingTheory.LocalProperties.Projective

/-! # Flatness of the lower truncation image on principal opens

Source: Stacks Project, Derived Categories of Schemes, Tag 08EG, proof paragraph
invoking Cohomology, Lemma cohomology-lemma-last-one-flat
(blueprint: lem-sc-affine-truncation-kernel-flat).
-/

@[expose] public section

set_option autoImplicit false

universe u wX wU

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

open MonoidalCategory in
private theorem image_flat_finitePresentation
    {R : Type u} [CommRing R] (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfree : ∀ i : ℤ, Module.Free R (P.X i) ∧ Module.Finite R (P.X i))
    (a r : ℤ) (hr : r < a)
    (hexact : ∀ N : ModuleCat.{u} R, ∀ i : ℤ, i < a →
      (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P).ExactAt i) :
    Module.Flat R (LinearMap.range (P.d (r - 1) r).hom) ∧
      Module.FinitePresentation R (LinearMap.range (P.d (r - 1) r).hom) := by
  have hflat (i : ℤ) : Module.Flat R (P.X i) := by
    have := (hfree i).1
    infer_instance
  have hop : Module.Flat R (P.opcycles (r - 1)) :=
    Module.Flat.opcycles_of_exactAt P (r - 1) hflat
      (fun N ↦ hexact N ((r - 1) - 1) (by omega))
  have he : P.ExactAt (r - 1) :=
    (hexact (𝟙_ (ModuleCat R)) (r - 1) (by omega)).of_iso
      ((NatIso.mapHomologicalComplex (rightUnitorNatIso (ModuleCat R)) (.up ℤ)).app P ≪≫
        (Functor.mapHomologicalComplexIdIso (ModuleCat R) (.up ℤ)).app P)
  have hp : (ComplexShape.up ℤ).prev (r - 1) = r - 2 := by simp; omega
  have hn : (ComplexShape.up ℤ).next (r - 1) = r := by simp
  have hk : LinearMap.range (P.d (r - 2) (r - 1)).hom =
      LinearMap.ker (P.d (r - 1) r).hom :=
    ((P.exactAt_iff' (r - 2) (r - 1) r hp hn).mp he).moduleCat_range_eq_ker
  let e : P.opcycles (r - 1) ≃ₗ[R] LinearMap.range (P.d (r - 1) r).hom :=
    (P.opcyclesIsoSc' (r - 2) (r - 1) r hp hn ≪≫
      (P.sc' (r - 2) (r - 1) r).moduleCatOpcyclesIso).toLinearEquiv ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hk ≪≫ₗ (P.d (r - 1) r).hom.quotKerEquivRange
  refine ⟨Module.Flat.of_linearEquiv e.symm, ?_⟩
  have := (hfree (r - 1)).1
  have := (hfree (r - 1)).2
  have := (hfree (r - 2)).2
  apply Module.finitePresentation_of_free_of_surjective
    (P.d (r - 1) r).hom.rangeRestrict
    (LinearMap.surjective_rangeRestrict (P.d (r - 1) r).hom)
  rw [LinearMap.ker_rangeRestrict, ← hk]
  exact Submodule.fg_range _

/-- For a bounded-above finite-free complex whose associated sheaf complex on `U` has
Tor amplitude in `[a,b]`, the image
of the differential entering degree `r < a` becomes flat and finitely presented after
localization at every principal open contained in the chosen quasi-compact open.
Source: Stacks Project, Tag 08EG, proof paragraph invoking
`cohomology-lemma-last-one-flat`
(blueprint: lem-sc-affine-truncation-kernel-flat).

Proof:
1. Fix f with D(f) contained in U. The principal-open tensor-exactness lemma
   identifies the sheaf Tor-amplitude hypothesis with exactness of the localized
   tensor complex in every degree below a.
2. Tensor with the unit and transport along the right unitor. Exactness in
   degree r - 1 gives range(d^(r-2)) = ker(d^(r-1)). The quotient description of
   opcycles and the first isomorphism theorem identify opcycles in degree r - 1
   with the differential image in degree r.
3. Apply the flat-opcycles criterion at r - 1, using tensor exactness at r - 2.
   Transfer flatness along the preceding linear equivalence. The surjection
   from P_f^(r-1) onto its differential image has finitely generated kernel,
   the range of P_f^(r-2), so the image is finitely presented.
4. Exact localization preserves categorical images. Compose the image/range
   comparisons with the canonical Shrink linear equivalence to identify this
   localized differential image with LocalizedModule.Away f of the original
   image. Transfer both properties across that equivalence.
-/
theorem affine_truncation_kernel_flat
    (A : Type u) [CommRing A]
    (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i))
    (hfree : ∀ i : ℤ, Module.Free A (P.X i) ∧ Module.Finite A (P.X i))
    (U : (Spec (.of A)).Opens) (hU : IsCompact (U : Set (Spec (.of A))))
    [HasDerivedCategory.{wX}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    [HasDerivedCategory.{wU}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (a b : ℤ) (r : ℤ) (hr : r < a)
    (hamp : ∀ G : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i →
        schemeDerivedTensorCohomologyVanishes U.toScheme
          ((@Functor.mapDerivedCategory
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) _ _ _
            (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) _ _ _
            ((SheafOfModules.overFunctor.{u}
                (moduleRings (Spec (.of A)).toRingedSpace) U) ⋙
              Equivalence.functor
                (C := SheafOfModules.{u}
                  ((moduleRings (Spec (.of A)).toRingedSpace).over U))
                (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
                (Scheme.Modules.overEquiv U))
            (Functor.additive_of_preserves_binary_products _)
            (comp_preservesFiniteLimits _ _) (comp_preservesFiniteColimits _ _)).obj
            (DerivedCategory.Q.obj
              ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
                (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) _ _ _ _
                (tilde.functor (.of A)) ⟨fun _ _ ↦ tilde.map_zero⟩
                (ComplexShape.up ℤ)).obj P))) G i) :
    ∀ f : A, PrimeSpectrum.basicOpen f ≤ U →
      Module.Flat (Localization.Away f)
          (LocalizedModule.Away f (LinearMap.range (P.d (r - 1) r).hom)) ∧
        Module.FinitePresentation (Localization.Away f)
          (LocalizedModule.Away f (LinearMap.range (P.d (r - 1) r).hom)) := by
  intro f hf
  let S := Submonoid.powers f
  let L := ModuleCat.localizedModuleFunctor S
  let Q := (L.mapHomologicalComplex (.up ℤ)).obj P
  have hQ (i : ℤ) : Module.Free (Localization.Away f) (Q.X i) ∧
      Module.Finite (Localization.Away f) (Q.X i) := by
    change Module.Free (Localization.Away f) ((P.X i).localizedModule S) ∧
      Module.Finite (Localization.Away f) ((P.X i).localizedModule S)
    have := (hfree i).1
    have := (hfree i).2
    exact ⟨Module.free_of_isLocalizedModule S ((P.X i).localizedModuleMkLinearMap S),
      Module.Finite.of_isLocalizedModule S ((P.X i).localizedModuleMkLinearMap S)⟩
  have hx := affine_open_localized_tensor_exact A P hP hfree U hU a b hamp f hf
  obtain ⟨hflat, hfp⟩ := image_flat_finitePresentation Q hQ a r hr hx
  let d := P.d (r - 1) r
  let e : LinearMap.range (Q.d (r - 1) r).hom ≃ₗ[Localization.Away f]
      LocalizedModule.Away f (LinearMap.range d.hom) :=
    ((ModuleCat.imageIsoRange (L.map d)).symm ≪≫ PreservesImage.iso L d ≪≫
      L.mapIso (ModuleCat.imageIsoRange d)).toLinearEquiv ≪≫ₗ
        Shrink.linearEquiv (Localization.Away f) _
  exact ⟨Module.Flat.of_linearEquiv e.symm, Module.FinitePresentation.of_equiv e⟩

end AlgebraicGeometry
