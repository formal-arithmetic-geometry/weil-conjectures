/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleClosedEssentialImage
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Data.ZMod.Basic
import Sheaf.AlgebraicGeometry.ProEtaleSupportedModuleUnits

/-!
# Supported kernels and their natural short exact complex sequences

Source: blueprint main-20261015, smooth purity, sk-prop-sf-localization,
lem-exc-proetale-support-triangle, supported-kernel identification and assembly
(blueprint: lem-exc-proetale-supported-kernel-complex).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

variable {T U Z : Scheme.{u}} (i : Z ⟶ T) (j : U ⟶ T) (A : Type (u + 1))
  [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]

/-- The induced map between kernels of the actual open units.
Source: blueprint support-triangle, supported-kernel paragraph
(blueprint: lem-exc-proetale-supported-kernel-complex). -/
noncomputable def finiteSupportedKernelMap
    {N N' : FiniteCoefficientModules T A} (a : N ⟶ N') :
    kernel ((finiteModuleAdjunction j A).unit.app N) ⟶
      kernel ((finiteModuleAdjunction j A).unit.app N') :=
  kernel.map _ _ a
    ((finiteCoefficientModulePullback j A ⋙ finiteModulePushforward j A).map a)
    ((finiteModuleAdjunction j A).unit.naturality a).symm

/-- Kernel maps preserve identity morphisms.
Source: blueprint support-triangle, supported-kernel paragraph
(blueprint: lem-exc-proetale-supported-kernel-complex).
Proof: compose both maps with the target kernel inclusion. The kernel map equation
reduces both composites to the same inclusion; cancel its monomorphism. -/
theorem finiteSupportedKernelMap_id (N : FiniteCoefficientModules T A) :
    finiteSupportedKernelMap j A (𝟙 N) = 𝟙 _ := by
  apply (cancel_mono (kernel.ι ((finiteModuleAdjunction j A).unit.app N))).1
  simp [finiteSupportedKernelMap]

/-- Kernel maps preserve composition.
Source: blueprint support-triangle, supported-kernel paragraph
(blueprint: lem-exc-proetale-supported-kernel-complex).
Proof: compose with the target kernel inclusion and use the kernel map equations
successively. Associativity gives the same composite; cancel the monic inclusion. -/
theorem finiteSupportedKernelMap_comp {N N' N'' : FiniteCoefficientModules T A}
    (a : N ⟶ N') (b : N' ⟶ N'') :
    finiteSupportedKernelMap j A (a ≫ b) =
      finiteSupportedKernelMap j A a ≫ finiteSupportedKernelMap j A b := by
  apply (cancel_mono (kernel.ι ((finiteModuleAdjunction j A).unit.app N''))).1
  simp [finiteSupportedKernelMap, Category.assoc]

/-- The sectionwise kernel of the actual open unit, with its induced maps.
Source: blueprint support-triangle, supported-kernel paragraph
(blueprint: lem-exc-proetale-supported-kernel-complex). -/
noncomputable def finiteSupportedKernel :
    FiniteCoefficientModules T A ⥤ FiniteCoefficientModules T A where
  obj N := kernel ((finiteModuleAdjunction j A).unit.app N)
  map := finiteSupportedKernelMap j A
  map_id := finiteSupportedKernelMap_id j A
  map_comp := finiteSupportedKernelMap_comp j A

/-- Addition of the induced kernel maps is computed sectionwise.
Source: blueprint support-triangle, supported-kernel paragraph
(blueprint: lem-exc-proetale-supported-kernel-complex).
Proof: after composition with the target kernel inclusion, the kernel map equations
and distributivity identify the map of a sum with the sum of the maps. Cancel the
monic inclusion. This is the additive structure of the kernel functor in Step 4. -/
theorem finiteSupportedKernel_additive : (finiteSupportedKernel j A).Additive := by
  constructor
  intro N N' a b
  apply (cancel_mono (kernel.ι ((finiteModuleAdjunction j A).unit.app N'))).1
  simp [finiteSupportedKernel, finiteSupportedKernelMap, Preadditive.add_comp]

attribute [instance] finiteSupportedKernel_additive

/-- Kernel inclusions commute with the induced maps.
Source: blueprint support-triangle, supported-kernel paragraph
(blueprint: lem-exc-proetale-supported-kernel-complex).
Proof: the defining kernel map equation identifies both composites with the original
map preceded by the source kernel inclusion. This is the naturality used in Step 5. -/
theorem finiteSupportedKernelInclusion_naturality
    (N N' : FiniteCoefficientModules T A) (a : N ⟶ N') :
    (finiteSupportedKernel j A).map a ≫
        kernel.ι ((finiteModuleAdjunction j A).unit.app N') =
      kernel.ι ((finiteModuleAdjunction j A).unit.app N) ≫ a := by
  simp [finiteSupportedKernel, finiteSupportedKernelMap]

/-- The natural kernel inclusion into the original module sheaf.
Source: blueprint support-triangle, supported-kernel paragraph
(blueprint: lem-exc-proetale-supported-kernel-complex). -/
noncomputable def finiteSupportedKernelInclusion : finiteSupportedKernel j A ⟶ 𝟭 _ where
  app N := kernel.ι ((finiteModuleAdjunction j A).unit.app N)
  naturality := finiteSupportedKernelInclusion_naturality j A

/-- The functor H(N) = i* ker(N → j* j* N), on the specified left module categories.
Source: blueprint support-triangle, supported-kernel paragraph
(blueprint: lem-exc-proetale-supported-kernel-complex). -/
noncomputable def finiteSupportedH :
    FiniteCoefficientModules T A ⥤ FiniteCoefficientModules Z A :=
  finiteSupportedKernel j A ⋙ finiteCoefficientModulePullback i A

/-- H is additive, as the composite of the additive kernel construction and pullback.
Source: blueprint support-triangle, supported-kernel paragraph
(blueprint: lem-exc-proetale-supported-kernel-complex). -/
noncomputable instance finiteSupportedH_additive : (finiteSupportedH i j A).Additive :=
  inferInstanceAs ((finiteSupportedKernel j A ⋙ finiteCoefficientModulePullback i A).Additive)

/-- Termwise kernel complexes; their differentials are the induced kernel maps.
Source: blueprint support-triangle, assembly paragraph
(blueprint: lem-exc-proetale-supported-kernel-complex). -/
noncomputable abbrev finiteSupportedKernelComplex :=
  (finiteSupportedKernel j A).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The natural inclusion of the kernel complexes.
Source: blueprint support-triangle, assembly paragraph
(blueprint: lem-exc-proetale-supported-kernel-complex). -/
noncomputable def finiteSupportedKernelComplexInclusion :
    finiteSupportedKernelComplex j A ⟶ 𝟭 (CochainComplex (FiniteCoefficientModules T A) ℤ) :=
  (finiteSupportedKernelInclusion j A).mapHomologicalComplex (ComplexShape.up ℤ) ≫
    (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom

/-- The actual open unit on complexes, with the canonical identity-complex comparison.
Source: blueprint support-triangle, assembly paragraph
(blueprint: lem-exc-proetale-supported-kernel-complex). -/
noncomputable def finiteOpenComplexUnit :
    𝟭 (CochainComplex (FiniteCoefficientModules T A) ℤ) ⟶
      (finiteCoefficientModulePullback j A ⋙ finiteModulePushforward j A).mapHomologicalComplex
        (ComplexShape.up ℤ) :=
  (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).inv ≫
    (finiteModuleAdjunction j A).unit.mapHomologicalComplex (ComplexShape.up ℤ)

/-- The hypothesis on complexes in the statement, with all maps between them retained.
Source: blueprint support-triangle, assembly paragraph
(blueprint: lem-exc-proetale-supported-kernel-complex). -/
def finiteOpenEpicComplex : ObjectProperty (CochainComplex (FiniteCoefficientModules T A) ℤ) :=
  fun I ↦ ∀ q : ℤ, Epi ((finiteModuleAdjunction j A).unit.app (I.X q))

/-- Inclusion of the full category of complexes satisfying the termwise epimorphism hypothesis.
Source: blueprint support-triangle, assembly paragraph
(blueprint: lem-exc-proetale-supported-kernel-complex). -/
noncomputable abbrev finiteOpenEpicComplexInclusion := (finiteOpenEpicComplex j A).ι

/-- Finite-ring supported units, vanishing of open restriction of closed direct image,
and the natural short exact complex sequence obtained from the kernel of the open unit.
The isomorphism e is natural on complexes with epic open units; its components in every degree
are exactly the closed units. Its inverse followed by the kernel inclusion is the first
arrow. Evaluating the natural short complex at I states exactness in the category of
complexes, and the final clause explicitly states exactness in every degree.

The assumed commutative criterion is the recorded closed-essential-image statement for
B = Z/n, n the additive order of 1 in A, in its canonical constant-ring presentation.
This presentation is identified with the continuous-function coefficient sheaf by the
constant-preserving comparisons of prop-weil-pbc-proetale-constant-ring-map.

Source: blueprint main-20261015, smooth purity, sk-prop-sf-localization,
lem-exc-proetale-support-triangle, supported-kernel identification and assembly
(blueprint: lem-exc-proetale-supported-kernel-complex).

Proof:
1. Restrict scalars along the central map Z/n → A sending r to r times 1. It is well
   defined since n times 1 is zero. By lem-exc-proetale-finite-scalar-unit-comparison,
   this commutes with inverse and direct images and preserves their actual units.
   Scalar restriction detects zero and reflects isomorphisms: it leaves underlying
   abelian sheaves unchanged, and the inverse of an invertible linear map is linear.
2. Apply the assumed lem-exc-proetale-closed-essential-image criterion to B. A sheaf
   with zero open restriction has invertible closed unit; reflect this to A. Applied
   to closed direct images, the other direction gives j* i_* M = 0. Naturality is
   that of the closed unit. Quasi-compactness is exactly the hypothesis on j.
3. The restriction of the open unit to U is the identity, by
   lem-pur-proetale-open-unit-evaluation and the scalar comparison. Exactness in
   prop-weil-pbc-proetale-constant-exact makes its kernel have zero open restriction.
   Step 2 identifies that kernel with its closed pullback followed by direct image.
4. Naturality of the open unit restricts every differential to the kernel. Its square
   is zero by cancellation of the monic kernel inclusion. Apply i* termwise to obtain
   H(I). Naturality of the closed unit gives the displayed chain map and its inverse.
5. The open units are epic by hypothesis, so their kernel sequences are short exact
   in the abelian category def-weil-sheaf-of-modules-category. Substitute the inverse
   closed unit followed by the kernel inclusion for the first arrow. Apply
   lem-weil-pbc-cochain-complexes-degreewise-exact to get short exactness of complexes.
   All kernel maps, inclusions and closed units commute with maps I → I', hence the
   resulting short exact sequence is natural in I. -/
theorem finiteSupportedKernelComplex_shortExact
    [IsLocallyNoetherian T] [CompactSpace T]
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (hB : ∀ N : Scheme.proEtaleRingModules T
        (Scheme.proEtaleConstantRing T (ULift.{u} (ZMod (addOrderOf (1 : A))))),
      ((Scheme.proEtaleConstantRingPushforward
          (ULift.{u} (ZMod (addOrderOf (1 : A)))) i).essImage N ↔
        IsZero ((Scheme.proEtaleConstantRingPullback
          (ULift.{u} (ZMod (addOrderOf (1 : A)))) j).obj N)) ∧
      (IsZero ((Scheme.proEtaleConstantRingPullback
          (ULift.{u} (ZMod (addOrderOf (1 : A)))) j).obj N) →
        IsIso ((Scheme.proEtaleConstantRingAdjunction
          (ULift.{u} (ZMod (addOrderOf (1 : A)))) i).unit.app N))) :
    (∀ N : FiniteCoefficientModules T A,
      IsZero ((finiteCoefficientModulePullback j A).obj N) →
        IsIso ((finiteModuleAdjunction i A).unit.app N)) ∧
    (∀ M : FiniteCoefficientModules Z A,
      IsZero ((finiteCoefficientModulePullback j A).obj
        ((finiteModulePushforward i A).obj M))) ∧
    ∃ e : finiteOpenEpicComplexInclusion j A ⋙ finiteSupportedKernelComplex j A ≅
        finiteOpenEpicComplexInclusion j A ⋙
          (finiteSupportedH i j A ⋙ finiteModulePushforward i A).mapHomologicalComplex
            (ComplexShape.up ℤ),
      (∀ (I : (finiteOpenEpicComplex j A).FullSubcategory) (q : ℤ),
        (e.hom.app I).f q = (finiteModuleAdjunction i A).unit.app
          ((finiteSupportedKernel j A).obj (I.obj.X q))) ∧
      ∃ w : (e.inv ≫ Functor.whiskerLeft (finiteOpenEpicComplexInclusion j A)
          (finiteSupportedKernelComplexInclusion j A)) ≫
            Functor.whiskerLeft (finiteOpenEpicComplexInclusion j A)
              (finiteOpenComplexUnit j A) = 0,
        ∀ I : (finiteOpenEpicComplex j A).FullSubcategory,
          ((ShortComplex.mk
            (e.inv ≫ Functor.whiskerLeft (finiteOpenEpicComplexInclusion j A)
              (finiteSupportedKernelComplexInclusion j A))
            (Functor.whiskerLeft (finiteOpenEpicComplexInclusion j A)
              (finiteOpenComplexUnit j A)) w).map ((evaluation _ _).obj I)).ShortExact ∧
          ∀ q : ℤ, (((ShortComplex.mk
            (e.inv ≫ Functor.whiskerLeft (finiteOpenEpicComplexInclusion j A)
              (finiteSupportedKernelComplexInclusion j A))
            (Functor.whiskerLeft (finiteOpenEpicComplexInclusion j A)
              (finiteOpenComplexUnit j A)) w).map ((evaluation _ _).obj I)).map
                (HomologicalComplex.eval _ (ComplexShape.up ℤ) q)).ShortExact := by
  obtain ⟨hc, hz, hop⟩ := finiteSupportedModuleUnits i j A hU hB
  have hk (N : FiniteCoefficientModules T A) :
      IsZero ((finiteCoefficientModulePullback j A).obj
        ((finiteSupportedKernel j A).obj N)) := by
    have := (finiteCoefficientModulePullback_exact j A).1
    exact (isZero_kernel_of_mono ((finiteCoefficientModulePullback j A).map
      ((finiteModuleAdjunction j A).unit.app N))).of_iso
        (PreservesKernel.iso (finiteCoefficientModulePullback j A) _)
  have hu (N : FiniteCoefficientModules T A) :
      IsIso ((finiteModuleAdjunction i A).unit.app
        ((finiteSupportedKernel j A).obj N)) := hc _ (hk N)
  let v : finiteSupportedKernel j A ⟶
      finiteSupportedH i j A ⋙ finiteModulePushforward i A :=
    Functor.whiskerLeft (finiteSupportedKernel j A) (finiteModuleAdjunction i A).unit
  have hv (N : FiniteCoefficientModules T A) : IsIso (v.app N) := hu N
  have : IsIso v := NatIso.isIso_of_isIso_app _
  let e : finiteOpenEpicComplexInclusion j A ⋙ finiteSupportedKernelComplex j A ≅
      finiteOpenEpicComplexInclusion j A ⋙
        (finiteSupportedH i j A ⋙ finiteModulePushforward i A).mapHomologicalComplex
          (ComplexShape.up ℤ) :=
    Functor.isoWhiskerLeft (finiteOpenEpicComplexInclusion j A)
      (NatIso.mapHomologicalComplex (asIso v) (ComplexShape.up ℤ))
  refine ⟨hc, hz, e, ?_, ?_⟩
  · intro I q
    rfl
  · have w : (e.inv ≫ Functor.whiskerLeft (finiteOpenEpicComplexInclusion j A)
          (finiteSupportedKernelComplexInclusion j A)) ≫
        Functor.whiskerLeft (finiteOpenEpicComplexInclusion j A)
          (finiteOpenComplexUnit j A) = 0 := by
      ext I q
      simp [finiteSupportedKernelComplexInclusion, finiteOpenComplexUnit,
        finiteSupportedKernelInclusion, Category.assoc]
    refine ⟨w, ?_⟩
    intro I
    have hd (q : ℤ) : (((ShortComplex.mk
          (e.inv ≫ Functor.whiskerLeft (finiteOpenEpicComplexInclusion j A)
            (finiteSupportedKernelComplexInclusion j A))
          (Functor.whiskerLeft (finiteOpenEpicComplexInclusion j A)
            (finiteOpenComplexUnit j A)) w).map ((evaluation _ _).obj I)).map
              (HomologicalComplex.eval _ (ComplexShape.up ℤ) q)).ShortExact := by
      have : Epi ((finiteModuleAdjunction j A).unit.app (I.obj.X q)) := I.property q
      let f := (finiteModuleAdjunction j A).unit.app (I.obj.X q)
      let s := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
      have hs : s.ShortExact := { exact := ShortComplex.exact_kernel f }
      apply ShortComplex.shortExact_of_iso _ hs
      let eq := (HomologicalComplex.eval _ (ComplexShape.up ℤ) q).mapIso (e.app I)
      refine ShortComplex.isoMk eq (Iso.refl _) (Iso.refl _) ?_ ?_
      · change eq.hom ≫ eq.inv ≫ kernel.ι f = kernel.ι f ≫ 𝟙 _
        simp only [Iso.hom_inv_id_assoc, Category.comp_id]
      · change 𝟙 _ ≫ f = f ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id]
    exact ⟨HomologicalComplex.shortExact_of_degreewise_shortExact _ hd, hd⟩

end AlgebraicGeometry.ProEtale
