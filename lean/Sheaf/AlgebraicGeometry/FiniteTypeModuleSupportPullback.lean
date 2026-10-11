/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Sheaf.AlgebraicGeometry.Modules.ResidueFiber
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Support and pullback of finite type quasi-coherent modules

Source: Stacks Project, Morphisms of Schemes, Lemma 056J (lemma-support-finite-type)
(blueprint: lem-weil-pbc-support-pullback-finite-type).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The support of a finite type quasi-coherent module is closed, is detected by its
residue-field fibres, and pulls back to the inverse image under every scheme morphism.
Support is the inline nonzero-stalk locus of def-weil-pbc-closed-subset-proper-over-base;
membership in it is nonvanishing of the stalk by definition, so part (2) is stated as the
Nakayama equivalence with the residue fibre `residueFiber F x` (κ(x) ⊗ F_x).
Source: Stacks Project, Morphisms of Schemes, Lemma 056J (lemma-support-finite-type).
(blueprint: lem-weil-pbc-support-pullback-finite-type)

Proof:
1. Apply lem-weil-pbc-finite-type-module-support-closed to obtain closedness.
2. Membership in support is nonvanishing of the stalk by
   def-weil-pbc-closed-subset-proper-over-base.
3. Choose an affine neighbourhood of x (def-pc-scheme). By the affine description in
   lem-weil-pbc-finite-type-module-support-closed, its finite module localizes to F_x.
   The images of a finite generating family generate this localization, hence F_x is finite.
4. The stalk ring is local and its residue field is def-weil-residue-field. Apply
   lem-weil-pbc-nakayama-local-generators to the empty family: F_x vanishes precisely
   when its tensor product with the residue field vanishes. This proves both equivalences.
5. The pullback is finite type by lem-weil-pbc-module-pullback-finite-type and
   quasi-coherent by lem-weil-pbc-module-pullback-quasi-coherent, so part (2) applies to it.
6. For y mapping to x, lem-weil-pbc-module-stalk-pullback identifies the pullback stalk
   with F_x tensor O_{Y,y}. The local stalk map (def-weil-locally-ringed-space-morphism)
   induces kappa(x) to kappa(y) (def-weil-residue-field). Tensor associativity therefore
   identifies its residue fibre with (F_x tensor kappa(x)) tensor over kappa(x) kappa(y).
7. Scalar extension along a field extension detects nonzero vector spaces: a basis
   extends to a basis, and its index set is nonempty exactly when the vector space is nonzero.
8. Apply part (2) on Y and X to conclude y is in the pullback support exactly when
   f(y) is in the support of F, which gives the asserted set equality. -/
theorem finiteType_module_support_pullback {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] :
    IsClosed {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ∧
      (∀ x : X, ¬ Subsingleton (F.presheaf.stalk x) ↔ ¬ Subsingleton (residueFiber F x)) ∧
      ∀ (Y : Scheme.{u}) (f : Y ⟶ X),
        ((tensorPullback f).obj F).IsFiniteType ∧
          {y : Y | ¬ Subsingleton (((tensorPullback f).obj F).presheaf.stalk y)} =
            f.base ⁻¹' {x : X | ¬ Subsingleton (F.presheaf.stalk x)} := by
  sorry

end AlgebraicGeometry.Scheme.Modules
