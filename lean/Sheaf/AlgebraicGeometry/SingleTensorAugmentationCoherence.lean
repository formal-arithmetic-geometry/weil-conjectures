/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.ModuleCupCanonicalHZeroIdentification
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.RingedDerivedTensorNative
import Sheaf.Algebra.Homology.RingedTensorComplexConstraints
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Coherence of the canonical single-complex tensor augmentation

Source: Stacks Project, Cohomology, Tags 06YH and 0FPB; the explicit augmentation refinement
in the DAG (blueprint: lem-sfb-single-tensor-augmentation-coherence).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

/-- The full assertion about the canonical augmentation, bundled to keep the chosen sheaf
and derived tensor structures explicit without installing additional global instances.
The maps are fixed to `μ Q` followed by the unsigned single-complex tensor isomorphism.
The unit is fixed to the native localization comparison, hence is the identity under
that comparison's normalized identification of the derived unit with O_X[0].
The final equation specifies the representative for every pair of nonpositive flat K-flat
resolutions; its source comparison is asserted invertible, rather than assumed.
Source: Stacks Project, Cohomology, Tags 06YH and 0FPB
(blueprint: lem-sfb-single-tensor-augmentation-coherence). -/
def SchemeSingleTensorAugmentationCoherence (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] : Prop := by
  letI := SheafOfModules.monoidalCategory X.sheaf
  letI := SheafOfModules.symmetricCategory X.sheaf
  letI : MonoidalPreadditive (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  letI : MonoidalClosed (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  letI : HasColimitsOfSize.{0, 0} (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} _
  letI := schemeModule_hasFunctorialFlatResolution X
  letI := DerivedCategory.hasDerivedMonoidalCategory
    (SheafOfModules.{u} (moduleRings X.toRingedSpace))
  letI := schemeDerivedTensorMonoidal X
  letI := CategoryTheory.RingedDerivedNative.derivedSymmetric
    (A := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let t := CochainComplex.singleFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0
  let s := DerivedCategory.singleFunctor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0
  let Q := DerivedCategory.Q.{w} (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let m := fun (F G : SheafOfModules.{u} (moduleRings X.toRingedSpace)) ↦
    Functor.LaxMonoidal.μ Q (t.obj F) (t.obj G) ≫
      Q.map (DerivedCategory.moduleCup_singleTensorIso F G).hom
  exact ∃ h : s.LaxBraided,
    (∀ F G : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      h.toLaxMonoidal.μ F G = m F G) ∧
    h.toLaxMonoidal.ε = Functor.LaxMonoidal.ε Q ∧
    IsIso (Functor.LaxMonoidal.ε Q) ∧
    ∀ (F G : SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (P T : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (a : P ⟶ t.obj F) (b : T ⟶ t.obj G),
      P.IsStrictlyLE 0 → T.IsStrictlyLE 0 → QuasiIso a → QuasiIso b →
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
      (∀ i : ℤ, ObjectProperty.flat (T.X i)) →
      CochainComplex.IsKFlatIndependentCoefficients (R := X.sheaf) P →
      CochainComplex.IsKFlatIndependentCoefficients (R := X.sheaf) T →
      IsIso (Functor.LaxMonoidal.μ Q P T) ∧
        (Q.map a ⊗ₘ Q.map b) ≫ m F G =
          Functor.LaxMonoidal.μ Q P T ≫
            Q.map ((a ⊗ₘ b) ≫ (DerivedCategory.moduleCup_singleTensorIso F G).hom)

/-- The degree-zero embedding of all O_X-module sheaves is lax symmetric monoidal for
its canonical derived-to-ordinary tensor augmentation, with the normalized unit and the
specified representative on every pair of nonpositive termwise-flat K-flat resolutions.
Source: Stacks Project, Cohomology, Tags 06YH and 0FPB, explicit DAG refinement
(blueprint: lem-sfb-single-tensor-augmentation-coherence).

Proof: (1) On the small Zariski site, additive sheafification is exact and its equivalences
are the locally bijective maps (lem-weil-pbc-sheafification-exact and
lem-weil-pbc-site-sheafification-iso-locally-bijective). Apply
lem-sf-ringed-derived-native-tensor: localization has its canonical lax tensorator, the
inverse K-flat model comparison, and its normalized unit comparison.
(2) The unsigned single tensor isomorphism is supported only on the (0,0) summand.
The formulas of lem-sf-ringed-tensor-complex-constraints identify its associator, braiding
and unitors with the ordinary ones: the Koszul sign at (0,0) is 1, and the unit maps
are scalar multiplication. Thus the single-complex functor is strong symmetric monoidal.
(3) Compose its tensorator with localization's lax tensorator. Naturality gives the
last equation for every pair of augmentations. The source tensorator is invertible by
K-flatness, so inverting it gives exactly the tensor of augmentations as representative,
independently of either resolution. Neither target sheaf needs to be flat.
(4) Expand these composites in the associativity diagram. Naturality moves the single
comparisons through the localization tensorators. Their lax associativity law and the
single-complex associativity from (2) identify the two paths, even when F tensor G is
not flat.
(5) The same calculation gives symmetry, using K-flat replacements from
lem-pc-kflat-resolution and cancellation of their localized tensor isomorphism if needed.
The two lax unit laws and (2) give both displayed unitor equations; the fixed unit map
is the identity under its normalized identification. These are precisely the naturality,
associativity, braiding and unit fields of the asserted lax braided structure. -/
theorem scheme_single_tensor_augmentation_coherence (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    SchemeSingleTensorAugmentationCoherence.{u, w} X := by
  sorry

end AlgebraicGeometry
