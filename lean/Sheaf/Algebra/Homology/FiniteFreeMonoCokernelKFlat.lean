/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-!+# Normalized finite-free cokernel resolutions on a ringed site

Source: Stacks Project, Cohomology on Sites, Tag 06YQ; Homology, Tag 0115;
Derived Categories, definition-cone
(blueprint: lem-sfb-finite-free-mono-cokernel-kflat).

The cone of the degree-zero map represents the two-term complex with differential `+u`.
Its augmentation uses the specified cokernel projection, without choosing another map.
-/

@[expose] public section

set_option autoImplicit false

universe a b u v r

open CategoryTheory CategoryTheory.Limits

private lemma flat_finite_coproduct
    {D : Type*} [Category* D] [Abelian D] [MonoidalCategory D]
    [BraidedCategory D] [MonoidalClosed D] {I : Type} [Finite I]
    (F : I → D) (hF : ∀ i, ObjectProperty.flat (F i)) :
    ObjectProperty.flat (∐ F) := by
  have : HasFiniteBiproducts D := Abelian.hasFiniteBiproducts
  have (i : I) : PreservesFiniteLimits (MonoidalCategory.tensorLeft (F i)) := (hF i).1.1
  rw [ObjectProperty.flat_iff_preservesFiniteLimits]
  have : PreservesColimit (Discrete.functor F) (MonoidalCategory.curriedTensor D) :=
    MonoidalCategory.Limits.preservesCoLimit_curriedTensor _
  have e : MonoidalCategory.tensorLeft (∐ F) ≅
      (Discrete.functor F ⋙ MonoidalCategory.curriedTensor D).flip ⋙ colim :=
    preservesColimitIso (MonoidalCategory.curriedTensor D) (Discrete.functor F) ≪≫
      colimitIsoFlipCompColim _
  have : PreservesFiniteLimits
      ((Discrete.functor F ⋙ MonoidalCategory.curriedTensor D).flip) :=
    preservesFiniteLimits_of_evaluation _ (fun j ↦
      inferInstanceAs (PreservesFiniteLimits (MonoidalCategory.tensorLeft (F j.as))))
  have : PreservesFiniteLimits (colim (J := Discrete I) (C := D)) :=
    preservesFiniteLimits_of_natIso HasBiproductsOfShape.colimIsoLim.symm
  have := comp_preservesFiniteLimits
    ((Discrete.functor F ⋙ MonoidalCategory.curriedTensor D).flip)
    (colim (J := Discrete I) (C := D))
  exact preservesFiniteLimits_of_natIso e.symm

namespace CochainComplex

section Construction

variable {A : Type a} [Category.{b} A] [Abelian A]

/-- The two-term complex of a morphism, represented by the canonical cone on its
degree-zero single complex. Under the canonical identifications its terms are `P` in
degree `-1`, `Q` in degree `0`, and zero elsewhere; its differential is `+u`.
Source: Stacks Project, Derived Categories, definition-cone
(blueprint: lem-sfb-finite-free-mono-cokernel-kflat). -/
noncomputable def monoCokernelComplex {P Q : A} (u : P ⟶ Q) : CochainComplex A ℤ :=
  mappingCone ((singleFunctor A 0).map u)

/-- The specified quotient augmentation: zero on the shifted source summand and the
given projection on the unshifted target summand. `S.zero` is exactly the condition
that the projection kills the differential; no exactness is needed to construct it.
Source: Stacks Project, Derived Categories, discussion before Tag 0152
(blueprint: lem-sfb-finite-free-mono-cokernel-kflat). -/
noncomputable def monoCokernelAugmentation (S : ShortComplex A) :
    monoCokernelComplex S.f ⟶ (singleFunctor A 0).obj S.X₃ :=
  mappingCone.descShortComplex (S.map (singleFunctor A 0))

end Construction

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- A monomorphism between specified finite direct sums of the regular module sheaf
has the normalized K-flat cokernel resolution, for arbitrary coefficients on a small site.
`S.X₁`, `S.X₂`, `S.X₃`, `S.f`, `S.g` are respectively `P`, `Q`, `T`, `u`, `q`.
The cokernel universal property retains the supplied projection, not just its object.
The last equation records the positive differential using the canonical cone inclusions.
Source: Stacks Project, Cohomology on Sites, Tag 06YQ; Homology, Tag 0115;
Derived Categories, definition-cone
(blueprint: lem-sfb-finite-free-mono-cokernel-kflat).

Proof:
1. In the abelian category of module sheaves, monicity of `S.f` and the cokernel
   universal property give the short exact sequence `0 → P → Q → T → 0`
   (def-weil-sheaf-of-modules-category). The single functor puts it in degree zero
   (def-pc-cochain-complex-modules). The relation `S.zero` constructs the augmentation.
2. The cone differential is `(d_Q,u;0,-d_P)` (def-weil-abstract-derived-category).
   Single complexes have zero differentials, so only `+u` in degrees `-1,0` remains.
   The unshifted-summand inclusion has degree-zero component the identity of `Q`.
3. Apply lem-pc-cone-short-exact-quasi-iso to that short exact sequence of complexes.
   Its canonical cone map is exactly monoCokernelAugmentation; it is a quasi-isomorphism
   (def-pc-quasi-iso-modules). Its composite with the inclusion is the given `q[0]`.
4. The tensor unit isomorphism (lem-pc-sheaf-modules-tensor-closed) makes the regular
   module flat (def-pc-flat-sheaf-modules).
5. By lem-pc-sites-modules-coproduct-flat, both finite sums are flat, including rank zero.
   Transport along the specified isomorphisms gives flatness of `P,Q`. The empty sum
   also gives flatness of zero. Thus every term of all three displayed complexes is flat.
6. They all vanish above degree zero. Apply lem-pc-bounded-above-flat-kflat-site
   separately to each. By def-pc-kflat-complex the specified quasi-isomorphism is a
   K-flat resolution. No flatness of the cokernel, scalar origin of `u`, or constant
   origin of `R` is used. -/
theorem finite_free_mono_cokernel_kflat
    (S : ShortComplex (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
    [Mono S.f] (hq : IsColimit (CokernelCofork.ofπ S.g S.zero)) (m n : ℕ)
    (eP : S.X₁ ≅ ∐ (fun (_ : Fin m) ↦ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)))
    (eQ : S.X₂ ≅ ∐ (fun (_ : Fin n) ↦ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))) :
    QuasiIso (monoCokernelAugmentation S) ∧
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R)
        ((monoCokernelComplex S.f).X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R)
        (((singleFunctor _ 0).obj S.X₁).X i)) ∧
      (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R)
        (((singleFunctor _ 0).obj S.X₂).X i)) ∧
      IsKFlatIndependentCoefficients (J := J) (R := R) (monoCokernelComplex S.f) ∧
      IsKFlatIndependentCoefficients (J := J) (R := R) ((singleFunctor _ 0).obj S.X₁) ∧
      IsKFlatIndependentCoefficients (J := J) (R := R) ((singleFunctor _ 0).obj S.X₂) ∧
      IsKFlatResolutionIndependentCoefficients (J := J) (R := R)
        (monoCokernelAugmentation S) ∧
      mappingCone.inr ((singleFunctor _ 0).map S.f) ≫ monoCokernelAugmentation S =
        (singleFunctor _ 0).map S.g ∧
      (mappingCone.inl ((singleFunctor _ 0).map S.f)).v 0 (-1) rfl ≫
          (monoCokernelComplex S.f).d (-1) 0 =
        ((singleFunctor _ 0).map S.f).f 0 ≫
          (mappingCone.inr ((singleFunctor _ 0).map S.f)).f 0 := by
  classical
  let A := ringedSiteModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.tensorPreadditive R
  let := (SheafOfModules.nonempty_monoidalClosed_independentCoefficients (R := R)).some
  have hunit : ObjectProperty.flat (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) := by
    exact ObjectProperty.prop_unit _
  have hP : ObjectProperty.flat S.X₁ :=
    (ObjectProperty.flat.prop_iff_of_iso eP).2
      (flat_finite_coproduct _ (fun _ ↦ hunit))
  have hQ : ObjectProperty.flat S.X₂ :=
    (ObjectProperty.flat.prop_iff_of_iso eQ).2
      (flat_finite_coproduct _ (fun _ ↦ hunit))
  have hsingle (M : A) (hM : ObjectProperty.flat M) (i : ℤ) :
      ObjectProperty.flat (((singleFunctor A 0).obj M).X i) := by
    by_cases hi : i = 0
    · subst i
      exact (ObjectProperty.flat.prop_iff_of_iso
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M)).2 hM
    · exact ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)
  have hsite (M : A) (hM : ObjectProperty.flat M) :
      SheafOfModules.IsFlatOnSite (C := C) (J := J) (R := R) M :=
    (exactFunctor A A).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (C := C) (J := J) R M).symm hM.2
  have hfP := fun i ↦ hsite _ (hsingle _ hP i)
  have hfQ := fun i ↦ hsite _ (hsingle _ hQ i)
  have hfC (i : ℤ) : SheafOfModules.IsFlatOnSite (C := C) (J := J) (R := R)
      ((monoCokernelComplex S.f).X i) := by
    by_cases hi : i = -1
    · subst i
      apply hsite
      apply (ObjectProperty.flat.prop_iff_of_iso
        (HomologicalComplex.homotopyCofiber.XIsoBiprod ((singleFunctor A 0).map S.f)
          (-1) 0 (by decide))).2
      exact (ObjectProperty.flat.prop_iff_of_iso (isoBiprodZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₂ (-1) (by decide)))).1
          (hsingle _ hP 0)
    · by_cases hi' : i = 0
      · subst i
        apply hsite
        apply (ObjectProperty.flat.prop_iff_of_iso
          (HomologicalComplex.homotopyCofiber.XIsoBiprod ((singleFunctor A 0).map S.f)
            0 1 (by decide))).2
        exact (ObjectProperty.flat.prop_iff_of_iso (isoZeroBiprod
          (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₁ 1 (by decide)))).1
            (hsingle _ hQ 0)
      · apply hsite
        apply ObjectProperty.flat_of_isZero
        exact (mappingCone.isZero_X_iff _ i).2
          ⟨HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₁ (i + 1) (by omega),
            HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₂ i hi'⟩
  have hle : (monoCokernelComplex S.f).IsStrictlyLE 0 := by
    rw [isStrictlyLE_iff]
    intro i hi
    exact (mappingCone.isZero_X_iff _ i).2
      ⟨HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₁ (i + 1) (by omega),
        HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₂ i (by omega)⟩
  have hkC := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    R (monoCokernelComplex S.f) 0 hfC
  have hkP := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    R ((singleFunctor A 0).obj S.X₁) 0 hfP
  have hkQ := SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    R ((singleFunctor A 0).obj S.X₂) 0 hfQ
  have : Epi S.g := epi_of_isColimit_cofork hq
  have hs : S.ShortExact := ⟨S.exact_of_g_is_cokernel hq⟩
  have : PreservesFiniteLimits (singleFunctor A 0) :=
    inferInstanceAs (PreservesFiniteLimits (HomologicalComplex.single A (.up ℤ) 0))
  have : PreservesFiniteColimits (singleFunctor A 0) :=
    inferInstanceAs (PreservesFiniteColimits (HomologicalComplex.single A (.up ℤ) 0))
  have hqi : QuasiIso (monoCokernelAugmentation S) :=
    mappingCone.quasiIso_descShortComplex (hs.map_of_exact (singleFunctor A 0))
  refine ⟨hqi, hfC, hfP, hfQ, hkC, hkP, hkQ, ⟨hqi, hkC⟩, ?_, ?_⟩
  · exact mappingCone.inr_descShortComplex (S.map (singleFunctor A 0))
  · simpa only [monoCokernelComplex, singleFunctor_obj_d, zero_comp, sub_zero] using
      mappingCone.inl_v_d ((singleFunctor A 0).map S.f) 0 (-1) 1 rfl rfl

end CochainComplex
