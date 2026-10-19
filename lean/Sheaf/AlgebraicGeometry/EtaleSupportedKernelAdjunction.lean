/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q133
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import WeilConjectures.SixFunctors.Etale.Derived.ClosedImmersionUpperShriek

/-!
# The support kernel and the right adjoint of closed etale direct image

Source: Stacks Project, Tag 09XQ, `lemma-sections-with-support-acyclic`, its proof and
preceding definition of the supported subsheaf; Tag 04CA,
`proposition-closed-immersion-pushforward`
(blueprint: lem-pur-etale-supported-kernel-adjunction).

## Main definitions

- `AlgebraicGeometry.Etale.supportedKernel`: the kernel of the open adjunction unit.
- `AlgebraicGeometry.Etale.supportedClosedInverseImage`: its inverse image on the closed part.

## Main statements

- `AlgebraicGeometry.Etale.supportedKernel_closedAdjunction`: the canonical supported unit is
  invertible, closed direct image is exact, and supported inverse image is its right adjoint.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The functor `P_Z(F) = ker(F → j_*j⁻¹F)`, formed as the kernel of the adjunction unit
in the functor category. Limits of functors are computed pointwise, so its value is the
kernel in abelian etale sheaves, with its canonical action on morphisms.
Source: Stacks Project, Tag 09XQ, the supported subsheaf preceding the lemma
(blueprint: lem-pur-etale-supported-kernel-adjunction). -/
noncomputable def supportedKernel {O X : Scheme.{u}} (j : O ⟶ X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).unit

/-- The underived supported inverse image `i^!₀F = i⁻¹P_Z(F)`.
Source: Stacks Project, Tag 09XQ, the supported sheaf viewed on the closed subscheme by
Tag 04CA (blueprint: lem-pur-etale-supported-kernel-adjunction). -/
noncomputable def supportedClosedInverseImage {Z O X : Scheme.{u}}
    (i : Z ⟶ X) (j : O ⟶ X) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  supportedKernel j ⋙ upperStar AddCommGrpCat.{u + 1} i

private noncomputable def supportedKernelIso {O X : Scheme.{u}} (j : O ⟶ X) :
    supportedKernel j ≅ sectionsWithSupport AddCommGrpCat.{u + 1} j :=
  NatIso.ofComponents
    (fun F ↦ PreservesKernel.iso
      ((evaluation _ _).obj F) (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).unit)
    (by
      intro F G f
      apply (cancel_mono
        (kernel.ι ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).unit.app G))).1
      simp only [PreservesKernel.iso_hom, sectionsWithSupport, Category.assoc,
        kernel.lift_ι]
      erw [kernelComparison_comp_ι]
      rw [← Category.assoc]
      erw [kernelComparison_comp_ι]
      exact (kernel.ι
        (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} j).unit).naturality f)

/-- The closed adjunction unit on the support kernel is a natural isomorphism;
closed direct image is exact and is left adjoint to supported inverse image.
The `Nonempty` adjunction supplies bijections on Hom sets natural in both sheaves.
Source: Stacks Project, Tags 09XQ and 04CA
(blueprint: lem-pur-etale-supported-kernel-adjunction).

Proof:
1. A closed immersion is finite (`lem-weil-pbc-closed-immersion-finite`), and finite
   direct image is exact (`lemma-weil-pbc-finite-direct-image-exact`).
2. Naturality of the open unit induces the maps between its kernels, and uniqueness
   gives the functor laws (`def-pur-abelian-sheaf-kernel`). Exactness of inverse image
   (`prop-weil-pbc-inverse-image-exact`) and the invertible open counit
   (`lem-kun-open-immersion-restriction`) show that the kernel restricts to zero on O.
3. The stalk comparison (`lem-weil-pbc-inverse-image-stalk-germ`) and conservative
   geometric stalks (`lemma-weil-pbc-geometric-stalk-conservative`) identify restriction
   to zero on O with support in Z. The essential-image description (`lem-kun-04ca`)
   puts P_Z(F) in the image of i_* and also gives j⁻¹i_*G = 0.
4. The closed counit is invertible (`prop-openclosed-lowerstar-fully-faithful`). The
   triangle identity makes the unit invertible on i_*B. Naturality transfers this to
   every supported sheaf, hence to P_Z(F), naturally in F.
5. Every h : i_*G → F has zero composite with the open unit: by open adjunction it
   corresponds to a map from j⁻¹i_*G = 0. Thus it factors uniquely through P_Z(F).
   Kernel uniqueness makes the resulting Hom bijection natural in G and F.
6. Compose this bijection with the canonical isomorphism P_Z(F) → i_*i^!₀F, then
   use full faithfulness of i_* (`lem-kun-04ca`). Its inverse sends k to i_*k followed
   by the inverse canonical unit and the kernel inclusion. The two formulas are inverse
   and natural, giving i_* ⊣ i^!₀. -/
theorem supportedKernel_closedAdjunction
    {Z O X : Scheme.{u}} (i : Z ⟶ X) (j : O ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (hcompl : IsCompl (Set.range i.base) (Set.range j.base)) :
    IsIso (Functor.whiskerLeft (supportedKernel j)
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit) ∧
      PreservesFiniteLimits (lowerStar AddCommGrpCat.{u + 1} i) ∧
      PreservesFiniteColimits (lowerStar AddCommGrpCat.{u + 1} i) ∧
      Nonempty (lowerStar AddCommGrpCat.{u + 1} i ⊣ supportedClosedInverseImage i j) := by
  have hij : Set.range i.base = (Set.range j.base)ᶜ := hcompl.eq_compl
  let e := supportedKernelIso j
  have hz (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
      IsZero ((upperStar AddCommGrpCat.{u + 1} j).obj ((supportedKernel j).obj F)) :=
    (isZero_upperStar_sectionsWithSupport AddCommGrpCat.{u + 1} j F).of_iso
      ((upperStar AddCommGrpCat.{u + 1} j).mapIso (e.app F))
  have hu : IsIso (Functor.whiskerLeft (supportedKernel j)
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit) := by
    have (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
        IsIso ((Functor.whiskerLeft (supportedKernel j)
          (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} i).unit).app F) :=
      isIso_upperStarLowerStarAdjunction_unit_app_of_isZero
        AddCommGrpCat.{u + 1} i j hij (hz F)
    exact NatIso.isIso_of_isIso_app _
  refine ⟨hu, inferInstance, inferInstance, ⟨?_⟩⟩
  exact (lowerStarClosedUpperShriekAdjunction AddCommGrpCat.{u + 1} i j hij).ofNatIsoRight
    (Functor.isoWhiskerRight e (upperStar AddCommGrpCat.{u + 1} i)).symm

end AlgebraicGeometry.Etale
