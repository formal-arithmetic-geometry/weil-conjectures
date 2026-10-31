/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.LocalizedStrictTensorData
public import WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherenceSupplement

/-! # Generator-normalized slice tensor coefficient coherence

Source: Stacks Project, Modules on Sites, Tags 03DI, 03CY and 0E8I;
the agent's generator and strict-coherence refinement
(blueprint: def-sf-slice-tensor-generator-interfaces).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules.LocalizedStrictTensor

namespace SheafOfModules.SliceTensorGenerator

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- Package the existing scalar-extension objects and maps as their functor.
Source: Stacks 03EK (blueprint: lem-sf-cbc-slice-tensor-generator-coherence). -/
def extend {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) :
    Modules.{c, v, r} R ⥤ Modules.{c, v, r} S where
  obj M := changeOfRingsOfUniverses.{v, c, max c v r, max c v r} (J := J) a M
  map f := changeOfRingsHomOfUniverses.{v, c, max c v r, max c v r} (J := J) a _ f
  map_id M := scalarExtension_map_id a M
  map_comp f g := scalarExtension_map_comp a f g

/-- Identify the actual underlying tensor with scalar extension followed by restriction.
Source: Stacks 03EK and 03D7
(blueprint: lem-sf-cbc-slice-tensor-generator-coherence). -/
abbrev TensorLift (R : Sheaf J CommRingCat.{max c v r}) (A : Under R) :=
  MonoidalCategory.tensorRight (algebraModule.{c, v, r} R A) ≅
    extend.{c, v, r} A.hom ⋙ scalars.{c, v, r} R A

/-- The identification keeps the original scalar tensor and its sheafification unit.
Source: Stacks 03EK and 03CY
(blueprint: lem-sf-cbc-slice-tensor-generator-coherence). -/
def TensorLiftNormalized (R : Sheaf J CommRingCat.{max c v r}) (A : Under R)
    (t : TensorLift.{c, v, r} R A) : Prop :=
  ∀ (M : Modules.{c, v, r} R) (W : Cᵒᵖ) (m : M.val.obj W)
    (s : A.right.obj.obj W),
    (t.hom.app M).val.app W (SheafOfModules.LocalizedStrictTensor.pure.{c, v, r} R M _ W m s) =
      scalarExtensionSection.{c, v, max c v r, max c v r} A.hom M W s m

variable (R : Sheaf J CommRingCat.{max c v r}) (V : C)
  [HasSheafify (J.over V) AddCommGrpCat.{max c v r}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]

/-- The scalar-linear comparison uses actual scalar extension on both sides.
Source: Stacks 0E8I and 03EK
(blueprint: lem-sf-cbc-slice-tensor-generator-coherence). -/
abbrev LinearComparison (A : Under R) :=
  localizedSystemExtension.{c, v, r} R V ⋙ extend.{c, v, r} A.hom ≅
    extend.{max c v, v, r} ((sliceAlgebras.{c, v, r} R V).obj A).hom ⋙
      localizedSystemExtension.{c, v, r} A.right V

/-- Normalization on actual direct-sum and scalar tensor sheafification units.
Scalar extension writes the scalar first: `s ⊗ m` represents the paper's `m ⊗ s`.
Source: Stacks 03DI, 03CY, 03EK and 0E8I
(blueprint: lem-sf-cbc-slice-tensor-generator-coherence). -/
def LinearNormalized (A : Under R) (e : LinearComparison.{c, v, r} R V A) : Prop :=
  ∀ (M : Modules.{max c v, v, r} (R.over V)) (W : C) (a : W ⟶ V)
    (m : M.val.obj (op (Over.mk a))) (s : A.right.obj.obj (op W)),
    (e.hom.app M).val.app (op W)
      (scalarExtensionSection.{c, v, max c v r, max c v r} A.hom _ (op W) s
        (extensionSection.{c, v, r} R V M W a m)) =
      extensionSection.{c, v, r} A.right V _ W a
        (scalarExtensionSection.{max c v, v, max c v r, max c v r}
          ((sliceAlgebras.{c, v, r} R V).obj A).hom
          M (op (Over.mk a)) s m)

end SheafOfModules.SliceTensorGenerator
