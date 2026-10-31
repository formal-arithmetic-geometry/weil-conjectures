/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldDerivedTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # The separability retraction before totalization

Source: Stacks Project, Tags 0C2X, 03EK and 0GMW.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory
open scoped TensorProduct
namespace FiniteFieldDerivedTensor
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J CommRingCat.{max u v}]
  (F B : Type (max u v)) [Field F] [Field B] [Algebra F B]

/-- Restrict both tensor factors to the smaller constant field.
Source: Stacks 03EK (blueprint: lem-pur-separable-field-tensor-sheaf). -/
noncomputable def sheafSource : Modules J B ⥤ Modules J B ⥤ Modules J F :=
  (((Functor.whiskeringLeft₂ (Modules J F)).obj
    (SheafOfModules.restrictScalars (coefficientMap J F B))).obj
      (SheafOfModules.restrictScalars (coefficientMap J F B))).obj
        (tensorFunctor J F)

/-- Tensor over the larger constant field and then restrict coefficients.
Source: Stacks 03EK (blueprint: lem-pur-separable-field-tensor-sheaf). -/
noncomputable def sheafTarget : Modules J B ⥤ Modules J B ⥤ Modules J F :=
  (Functor.postcompose₂.obj
    (SheafOfModules.restrictScalars (coefficientMap J F B))).obj
      (tensorFunctor J B)

/-- The pure-section formula for the two coefficient actions.
Source: Stacks 03EK (blueprint: lem-pur-separable-field-tensor-sheaf). -/
def IsSheafTensorAction (a : (B ⊗[F] B) →+* End (sheafSource J F B)) : Prop :=
  ∀ (M N : Modules J B) (b c : B) (X : Cᵒᵖ)
        (m : M.val.obj X) (n : N.val.obj X),
        ((((a (b ⊗ₜ[F] c)).app M).app N).val.app X)
          (tensorSection J F
            ((SheafOfModules.restrictScalars (coefficientMap J F B)).obj M)
            ((SheafOfModules.restrictScalars (coefficientMap J F B)).obj N) X m n) =
        tensorSection J F
          ((SheafOfModules.restrictScalars (coefficientMap J F B)).obj M)
          ((SheafOfModules.restrictScalars (coefficientMap J F B)).obj N) X
            (constantSection J B X b • m) (constantSection J B X c • n)

/-- The pure-section formula for the balanced quotient.
Source: Stacks 03EK (blueprint: lem-pur-separable-field-tensor-sheaf). -/
def IsSheafBalancedMap (q : sheafSource J F B ⟶ sheafTarget J F B) : Prop :=
  ∀ (M N : Modules J B) (X : Cᵒᵖ) (m : M.val.obj X) (n : N.val.obj X),
        (((q.app M).app N).val.app X)
          (tensorSection J F
            ((SheafOfModules.restrictScalars (coefficientMap J F B)).obj M)
            ((SheafOfModules.restrictScalars (coefficientMap J F B)).obj N) X m n) =
        tensorSection J B M N X m n

/-- The canonical split balanced quotient of sheaf tensor products.
Source: Stacks Project, Tag 0C2X, finite separable diagonal, and Tags 03EK and 0GMW,
bilinear universal property and module sheafification
(blueprint: lem-pur-separable-field-tensor-sheaf).
Proof: The commuting actions on the two factors give the tensor-ring action. On
constant-presheaf sections, send m tensor_B n to the action of e on m tensor_F n.
The annihilator condition proves balancing and multiplication(e)=1 proves that
quotient after section is the identity; the reverse composite is the e-action.
These constructions commute with module morphisms and restrictions. Extend them
through module sheafification. The universal properties of bilinear extension and
of the sheaf tensor identify the resulting objects with the existing tensor objects.
Uniqueness proves the two retraction identities, naturality, and the specified
pure-tensor formulas, even for sections of the constant sheaf which are only locally
constant. The construction applies to zero modules and the empty site as well. -/
theorem exists_separableFieldTensorSheaf (e : B ⊗[F] B)
    (hμ : Algebra.TensorProduct.lmul' F e = 1)
    (he : ∀ b : B, (b ⊗ₜ[F] (1 : B) - (1 : B) ⊗ₜ[F] b) * e = 0) :
    ∃ (a : (B ⊗[F] B) →+* End (sheafSource J F B))
      (q : sheafSource J F B ⟶ sheafTarget J F B)
      (s : sheafTarget J F B ⟶ sheafSource J F B),
      s ≫ q = 𝟙 _ ∧ q ≫ s = a e ∧
      IsSheafTensorAction J F B a ∧
      IsSheafBalancedMap J F B q := by
  sorry
end FiniteFieldDerivedTensor
