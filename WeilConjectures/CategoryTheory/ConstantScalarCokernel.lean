/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ConstantFiniteFreePresentationExtension
public import WeilConjectures.CategoryTheory.SiteConstantModuleHomSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIsoSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherenceSupplement
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import all WeilConjectures.CategoryTheory.ConstantFiniteFreePresentationExtension
import all WeilConjectures.CategoryTheory.SiteConstantModuleHomSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIsoSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all Mathlib.Algebra.Category.ModuleCat.Products
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherenceSupplement
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all WeilConjectures.AlgebraicGeometry.PurInverseImageScalarComparison
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Constant module realization preserves cokernels

Source: Stacks Project, Tags 03CY, 03EI and 03EK; Bhatt--Scholze,
Proposition 6.8.14(2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ConstantFiniteFreePresentationExtension

/-- Constant module sheafification followed by scalar extension preserves every
cokernel, with its prescribed quotient map. No flatness assumption is needed.
Source: Stacks Project, Tags 03CY, 03EI and 03EK; Bhatt--Scholze,
Proposition 6.8.14(2).
(blueprint: lem-per-constant-scalar-cokernel).

Proof: The underlying additive constant sheaf functor preserves finite colimits:
it is constant presheaf formation followed by left adjoint sheafification, and
ordinary modules have colimits on their underlying abelian groups. The forgetful
functor from module sheaves preserves and reflects these colimits, so the constant
module functor preserves finite colimits. Extension of scalars is left adjoint to
restriction of scalars, hence also preserves finite colimits. Their composite
therefore preserves cokernels. The canonical cokernel comparison has the stated
quotient-map equation. -/
theorem constantScalarCokernel {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) (R : Type (max u v)) [CommRing R]
    [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasWeakSheafify J AddCommGrpCat.{max u v}]
    [HasWeakSheafify J RingCat.{max u v}]
    [HasWeakSheafify J CommRingCat.{max u v}]
    (B : Sheaf J CommRingCat.{max u v})
    (σ : (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of R) ⟶ B)
    {M N : ModuleCat.{max u v} R} (d : M ⟶ N) :
    ∃ w : extension J R B σ (cokernel d) ≅ cokernel (extensionMap J R B σ d),
      extensionMap J R B σ (cokernel.π d) ≫ w.hom =
        cokernel.π (extensionMap J R B σ d) := by
  let H := constantModuleHomFunctor J R
  let G := SheafOfModules.toSheaf (homRing J R)
  have : PreservesFiniteColimits (H ⋙ G) := by
    change PreservesFiniteColimits
      (forget₂ (ModuleCat R) AddCommGrpCat ⋙ constantSheaf J AddCommGrpCat)
    have : PreservesFiniteColimits (constantSheaf J AddCommGrpCat.{max u v}) :=
      comp_preservesFiniteColimits _ _
    exact comp_preservesFiniteColimits _ _
  have : PreservesFiniteColimits H := preservesFiniteColimits_of_reflects_of_preserves H G
  let T := AlgebraicGeometry.Scheme.PurScalar.tensorFunctor σ
  have : T.IsLeftAdjoint :=
    (AlgebraicGeometry.Scheme.PurScalar.tensorAdjunction σ).isLeftAdjoint
  have : PreservesFiniteColimits (H ⋙ T) := comp_preservesFiniteColimits _ _
  let F := extensionFunctor J R B σ
  have : PreservesFiniteColimits F := inferInstanceAs (PreservesFiniteColimits (H ⋙ T))
  have : F.PreservesZeroMorphisms := by infer_instance
  exact ⟨PreservesCokernel.iso F d, PreservesCokernel.π_iso_hom F d⟩

end CategoryTheory.ConstantFiniteFreePresentationExtension
