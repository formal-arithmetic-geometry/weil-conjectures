/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import Sheaf.AlgebraicGeometry.EtaleSetConstantPullbackComparison
public import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits

/-! # Identity transport of a map out of a constant sheaf

Source: Stacks Project, Tags 03CB, 03CC, and 03P5.
(blueprint: lem-weil-pbc-etale-set-constant-transport-identity).
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Transporting a map from a constant sheaf along the identity changes only
its target by the identity-composition cast. The map need not be invertible.

Source: Stacks Project, Tags 03CB, 03CC, and 03P5.
(blueprint: lem-weil-pbc-etale-set-constant-transport-identity).

Proof: the inverse-image adjunction for the identity is identified with the identity
adjunction by restriction along the canonical isomorphism from base change by the
identity to the identity functor. Its unit equation identifies the chosen composition
comparison with this identity comparison on the inverse image of F: both have the
same value on every twice unit-pulled section, so fixed-sheaf uniqueness in
etaleSetInverseImageCompositionUnits applies. The constant comparison is constructed
by uniqueness of left adjoints and therefore satisfies the same identity unit equation
on the constant sheaf. Naturality of the identity comparison with respect to tau
cancels the two identity comparisons. The only remaining map is transport from s to
identity composed with s, which is exactly the inverse of the displayed eqToHom. -/
theorem etaleSetConstantTransportIdentity
    (S P : Scheme.{u}) (s : P ⟶ S)
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (A : Type (u + 1))
    (τ : (constantSheaf P.smallEtaleTopology (Type (u + 1))).obj A ⟶
      (Scheme.etaleSetPullback s).obj F) :
    (etaleSetConstantPullbackComparison (𝟙 P)).inv.app A ≫
        (Scheme.etaleSetPullback (𝟙 P)).map τ ≫
        ((Classical.choose etaleSetInverseImageCompositionUnits.2.2)
          S P P s (𝟙 P)).hom.app F =
      τ ≫ eqToHom (congrArg
        (fun k : P ⟶ S ↦ (Scheme.etaleSetPullback k).obj F)
        (Category.id_comp s)).symm := by sorry

end AlgebraicGeometry
