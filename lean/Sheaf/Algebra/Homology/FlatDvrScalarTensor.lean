/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q23
-/
module

public import Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.LinearAlgebra.DvrMatrixSmithPowers
import Sheaf.CategoryTheory.FiniteTypeConstantExact
import Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients

/-! # Derived tensor of finite scalar models over a flat DVR algebra sheaf

Source: blueprint main-20261015, sk-lem-integral-models-operations.proof.md,
paragraph (2), corrected explicit scalar-model calculation
(blueprint: lem-sfb-flat-dvr-scalar-tensor).

Scalar extension and the derived tensor below are compositions of the recorded
constant realization, sheafified extension of scalars, and K-flat tensor descent.
The cyclic module is presented by extension of the scalar quotient; right exactness
identifies this presentation canonically with the sheaf quotient R / pi^n R.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules.FlatDvrScalar

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type (max u v)} [CommRing A] {R : Sheaf J CommRingCat.{max u v}}

/-- The scalar model R tensor underline P, using the recorded constant realization and
ordinary sheafified extension of scalars. Source: blueprint main-20261015,
paragraph (2) of sk-lem-integral-models-operations.proof.md; Stacks 03EK and 093J
(blueprint: lem-sfb-flat-dvr-scalar-tensor). -/
def scalarExtension (α : realizationRing J A ⟶ R) (P : ModuleCat.{max u v} A) :
    SheafOfModules.{max u v, v, u, max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) :=
  changeOfRingsOfUniverses.{v, u, max u v, max u v} (J := J) α
    ((commutativeSiteConstantModuleFunctor J A).obj P)

/-- The canonical scalar-quotient presentation of R / pi^n R as an R-module sheaf.
Extension of scalars preserves the scalar cokernel A --pi^n--> A, giving this
presentation of the sheaf quotient, including n = 0. Source: Stacks 03EK and blueprint
main-20261015, sk-lem-integral-models-operations.proof.md, paragraph (2)
(blueprint: lem-sfb-flat-dvr-scalar-tensor). -/
def cyclic (α : realizationRing J A ⟶ R) (π : A) (n : ℕ) :
    SheafOfModules.{max u v, v, u, max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R) :=
  scalarExtension J α (ModuleCat.of A (A ⧸ Ideal.span {π ^ n}))

variable [CategoryTheory.HasSheafify J AddCommGrpCat.{max u v}]

variable [HasDerivedCategory.{w, max u v, (max u v) + 1} (SheafOfModules.{max u v, v, u, max u v}
  ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))]

/-- Apply the recorded unbounded derived tensor to two module sheaves placed in degree zero.
Source: Stacks 06YU and blueprint main-20261015,
sk-lem-integral-models-operations.proof.md, paragraph (2)
(blueprint: lem-sfb-flat-dvr-scalar-tensor). -/
def tensor (M N : SheafOfModules.{max u v, v, u, max u v}
    ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) :
    DerivedCategory.{w, max u v, (max u v) + 1} (SheafOfModules.{max u v, v, u, max u v}
      ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) :=
  (siteDerivedTensorIndependentCoefficients.{u, v, max u v, w} J R).obj
    ((DerivedCategory.singleFunctor.{w, max u v, (max u v) + 1} _ 0).obj M,
      (DerivedCategory.singleFunctor.{w, max u v, (max u v) + 1} _ 0).obj N)

/-- Finite scalar models over a flat DVR algebra sheaf have derived tensor cohomology
in degrees -1 and 0, again finite scalar models. Cyclic powers give the minimum exponent
in both degrees, and a free factor is a tensor unit in degree zero.

Source: blueprint main-20261015, sk-lem-integral-models-operations.proof.md,
paragraph (2), explicit DVR scalar-model calculation
(blueprint: lem-sfb-flat-dvr-scalar-tensor).

Proof:
1. Present P and Q by finite scalar matrices. Apply lem-sfb-dvr-matrix-smith-powers;
   discard exponent-zero pivots. Each module is a finite sum of A and A/(pi^r), r >= 1.
   Empty sums and zero-dimensional presentations are included.
2. Constant realization is exact by lem-weil-pbc-finite-type-constant-exact (Stacks 093J).
   Flatness makes tensoring with R exact (def-pc-flat-sheaf-modules, Stacks 03ER).
   Thus T(M) = R tensor underline M preserves kernels, cokernels and finite sums,
   T(A) is R, and T(A/(pi^r)) is R/pi^r R, by def-pur-sheaf-tensor-product (03EK).
3. Domain cancellation makes multiplication by pi^r injective on A. Exact T gives
   the resolution [R --pi^r--> R] in degrees -1,0 of R/pi^r R. A free summand uses
   R[0]. Finite sums give bounded finite free resolutions of the two scalar models.
4. These resolutions are K-flat by lem-pc-bounded-above-flat-kflat-site (06YQ).
   Use lem-weil-pbc-site-derived-tensor-descent and
   lem-pur-kflat-tensor-quasiiso-independent (06YP) to tensor the first resolution
   with the second module in degree zero. Symmetry with the Koszul sign puts this
   into the cited K-flat theorem's orientation. A cyclic pair is consequently
   [R/pi^s R --pi^r--> R/pi^s R] (def-pc-tensor-complex-sheaves).
5. If r >= s, this differential is zero. If r < s, its scalar cokernel is A/pi^r,
   and multiplication by pi^(s-r) identifies its scalar kernel with A/pi^r:
   pi^r a = pi^s b iff a = pi^(s-r)b, by domain cancellation. Exact T carries
   these identifications to sheaves. Both cohomology sheaves have exponent min r s.
6. Finite block sums compute the general case. Free/free, free/cyclic and cyclic/free
   pairs contribute only degree zero; cyclic/cyclic pairs use step 5. Their scalar
   modules have finite presentations obtained by concatenating these finite presentations.
   All other degrees vanish. The tensor unit map r tensor q maps to rq, with inverse
   q maps to 1 tensor q, gives both free-factor identifications in degree zero. -/
theorem flat_dvr_scalar_tensor [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) (_hπ : IsLocalRing.maximalIdeal A = Ideal.span {π})
    (α : realizationRing J A ⟶ R)
    (_hflat : IsFlatOnSite.{u, v, max u v, max u v} (J := J) (R := realizationRing J A)
      ((restrictScalars.{max u v}
        ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).map α)).obj
          (unit ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))))
    (P Q : ModuleCat.{max u v} A) [Module.FinitePresentation A P]
    [Module.FinitePresentation A Q] :
    (∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor.{w, max u v, (max u v) + 1} _ i).obj
        (tensor J (scalarExtension J α P) (scalarExtension J α Q)))) ∧
    (∀ i : ℤ, ∃ N : ModuleCat.{max u v} A, Module.FinitePresentation A N ∧
      Nonempty ((DerivedCategory.homologyFunctor.{w, max u v, (max u v) + 1} _ i).obj
        (tensor J (scalarExtension J α P) (scalarExtension J α Q)) ≅
          scalarExtension J α N)) ∧
    (∀ r s : ℕ, 1 ≤ r → 1 ≤ s →
      Nonempty ((DerivedCategory.homologyFunctor.{w, max u v, (max u v) + 1} _ (-1)).obj
        (tensor J (cyclic J α π r) (cyclic J α π s)) ≅ cyclic J α π (min r s)) ∧
      Nonempty ((DerivedCategory.homologyFunctor.{w, max u v, (max u v) + 1} _ 0).obj
        (tensor J (cyclic J α π r) (cyclic J α π s)) ≅ cyclic J α π (min r s))) ∧
    Nonempty (tensor J
      (unit ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R))
      (scalarExtension J α Q) ≅
        (DerivedCategory.singleFunctor.{w, max u v, (max u v) + 1} _ 0).obj
          (scalarExtension J α Q)) ∧
    Nonempty (tensor J (scalarExtension J α P)
      (unit ((sheafCompose J (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj R)) ≅
        (DerivedCategory.singleFunctor.{w, max u v, (max u v) + 1} _ 0).obj
          (scalarExtension J α P)) := by
  sorry

end SheafOfModules.FlatDvrScalar
