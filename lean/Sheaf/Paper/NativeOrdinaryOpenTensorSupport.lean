/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import Sheaf.Paper.NativeOpenTensorOperations

/-! # Support of the ordinary open tensor

Source: Stacks 0E8I, 0GL1 and 015F.
(blueprint: lem-sf-native-ordinary-open-tensor-support).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
universe u a b
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- Tensor with an extended input remains supported on the geometric open.

Source: Stacks 0GL1, sites-cohomology.tex, lemma-j-shriek-and-tensor, and
Stacks 0E8I, sites-modules.tex, lemma-j-shriek-and-tensor.

Proof: Represent the open input by a complex and the ambient input by a
flat-term K-flat complex. Exact extension represents its derived extension.
The fixed ordinary tensor model identifies the derived tensor with the
direct-sum total tensor of the representatives. The underived projection
formula identifies each summand with an extension by zero of its restriction,
compatibly with both signed differentials. Extension is exact and commutes
with the total coproducts. Hence this total complex is itself an extension.
Its localized object belongs to the essential image of derived extension.
The open unit is invertible, so extension is fully faithful and its counit
is invertible on its essential image. Transport along the representative
isomorphism gives the asserted counit for arbitrary derived inputs. This
argument allows the empty open and unbounded inputs. It constructs no open
tensor comparison and asserts no compatibility with forgetting Weil structures.
(blueprint: lem-sf-native-ordinary-open-tensor-support). -/
theorem native_ordinary_open_tensor_support
    (M : DerivedCategory (ProEtale.AdicSheaf l
      (U ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    (N : DerivedCategory (ProEtale.AdicSheaf l
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber)) :
    IsIso ((ProEtale.adicOpenImmersionLowerShriekAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapExactDerivedCategory.counit.app
        ((nativeDerivedClosedComparison k₀ l Z).ordinaryClosed.tensor.obj
          ((ProEtale.adicOpenImmersionLowerShriek l
            (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory.obj M, N))) :=
  by sorry

end AlgebraicGeometry.ProEtaleWeilSheaf
