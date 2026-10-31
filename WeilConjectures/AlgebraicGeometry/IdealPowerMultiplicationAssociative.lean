/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections

/-! # Associativity and units of ideal-power multiplication

Source: blueprint main-20261015, Nagata compactification, blow-ups,
lemma-nagata-sheaf-ideal-powers-assoc; Stacks Project, Tags 01I8, 01CA, 00CX, 01IT.
(blueprint: lemma-nagata-sheaf-ideal-powers-assoc)

The factorization through the ideal inclusion characterizes each multiplication
map uniquely. The conclusion includes existence of these global maps; it imposes
no choice of multiplication as a hypothesis. Degree equalities are transported
explicitly, so the coherence identities are equalities of sheaf morphisms.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.IdealSheafData

set_option autoImplicit false

/-- The canonical tensor multiplication maps between powers of a quasi-coherent
ideal are associative and have the zeroth power as their two-sided unit.

Source: blueprint main-20261015, Nagata compactification, blow-ups,
lemma-nagata-sheaf-ideal-powers-assoc
(blueprint: lemma-nagata-sheaf-ideal-powers-assoc).

The first equation uniquely characterizes multiplication: composing with the
monic inclusion into the structure sheaf gives ordinary multiplication there.
The canonical inclusion of the zeroth power is an isomorphism to the tensor unit.
The remaining equations are associativity and the left and right unit laws,
with the canonical identifications of the degrees written as `eqToHom`.

Proof:
1. On an affine open U = Spec A, the powers have sections J^r, with J = I(U)
   and J^0 = A (def-sbc-ideal-sheaf-powers). The affine tensor comparison is
   bijective, identifies pure tensor sections with module pure tensors, and
   preserves quasi-coherence (lem-weil-pbc-quasi-coherent-tensor-product-affine-sections).
   Multiplication x tensor y maps to xy in J^(m+n), by J^m J^n = J^(m+n).
   The tensor universal property determines the map uniquely
   (def-weil-pbc-module-tensor-product), and the ideal inclusion is injective.
2. The two triple products send (x tensor y) tensor z to (xy)z and x(yz),
   after the standard associator. Ring associativity makes them equal.
   Triple pure tensors generate, so the maps agree on every affine open.
3. In degree zero the inclusion J^0 = A is the identity. Left multiplication
   sends a tensor y to ay, the left unitor; its inverse sends y to 1 tensor y.
   Right multiplication sends y tensor a to ya, the right unitor; its inverse
   sends y to y tensor 1. Balancing and generation give both unit identities.
4. Ring restriction preserves multiplication and 1, and tensor restriction
   preserves pure tensors (def-pur-sheaf-tensor-product and
   def-weil-sheaf-of-modules-category). Thus the maps commute with restriction;
   on principal opens this is multiplication of fractions. They therefore glue.
5. Affine opens form a basis (lem-weil-pbc-affine-opens-basis). For sections
   over an arbitrary open, restrict to an affine cover and use sheaf uniqueness
   to obtain the global equations. The degree-zero inclusion is an isomorphism
   by its affine identifications. No affine-intersection hypothesis is needed.
-/
theorem exists_powMultiplication_associative_unital {X : Scheme.{u}} (I : X.IdealSheafData) :
    ∃ μ : ∀ m n : ℕ, (I ^ m).toModules ⊗ (I ^ n).toModules ⟶ (I ^ (m + n)).toModules,
      (∀ m n : ℕ, μ m n ≫ (I ^ (m + n)).toModulesι =
        ((I ^ m).toModulesι ⊗ₘ (I ^ n).toModulesι) ≫
          (λ_ (𝟙_ X.Modules)).hom) ∧
      IsIso (I ^ 0).toModulesι ∧
      (∀ m n k : ℕ,
        (μ m n ▷ (I ^ k).toModules) ≫ μ (m + n) k ≫
            eqToHom (congrArg (fun r : ℕ ↦ (I ^ r).toModules) (Nat.add_assoc m n k)) =
          (α_ (I ^ m).toModules (I ^ n).toModules (I ^ k).toModules).hom ≫
            ((I ^ m).toModules ◁ μ n k) ≫ μ m (n + k)) ∧
      (∀ n : ℕ,
        μ 0 n ≫ eqToHom (congrArg (fun r : ℕ ↦ (I ^ r).toModules) (Nat.zero_add n)) =
          ((I ^ 0).toModulesι ▷ (I ^ n).toModules) ≫ (λ_ (I ^ n).toModules).hom) ∧
      (∀ n : ℕ,
        μ n 0 ≫ eqToHom (congrArg (fun r : ℕ ↦ (I ^ r).toModules) (Nat.add_zero n)) =
          ((I ^ n).toModules ◁ (I ^ 0).toModulesι) ≫ (ρ_ (I ^ n).toModules).hom) := by
  sorry

end AlgebraicGeometry.Scheme.IdealSheafData
