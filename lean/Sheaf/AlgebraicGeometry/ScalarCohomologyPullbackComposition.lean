/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
import Sheaf.AlgebraicGeometry.TensorPullback

/-! # Composition of scalar cohomology pullbacks

Source: Stacks Project, Tags 0097 and 01F7 (cohomology-equation-functorial).
(blueprint: lem-sc-scalar-cohomology-pullback-composition).
-/

@[expose] public section

universe w
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Successive scalar cohomology pullbacks agree with pullback along the composite,
after the normalized tensor-pullback comparison.
Source: Stacks Project, Tags 0097 and 01F7 (cohomology-equation-functorial).
(blueprint: lem-sc-scalar-cohomology-pullback-composition)
Proof: Put L_t = tensorPullback t and use the normalized adjunction
L_t ⊣ t_*. The adjunction defining scalarPullbackCompIso identifies the unit
of L_(a ≫ b) with the successive units for L_b and L_a, followed by the
pushforward-composition comparison. Apply inverse-image adjunction on sheaves
of k-vector spaces. The sectionwise characterization of scalarPullbackCoefficient
then identifies the coefficient map for the composite with the composite of
the two coefficient maps, followed by the inverse of scalarPullbackCompIso.
Indeed, their adjoints have the same component on every section by the unit
identity; hence they are equal by sheaf-morphism extensionality and injectivity
of the adjunction hom equivalence. The comparison of inverse images also
identifies scalarInverseUnitIso for the composite with the successive constant
unit isomorphisms, by naturality of constant-sheaf pullback. For an Ext class,
apply exact-functor composition comparison and naturality with respect to these
two coefficient maps. Associativity of Yoneda composition and the constant-unit
identity give equality of the resulting scalar Ext classes. Finally the
injective-resolution comparison defining scalarCohomologyExtEquiv is natural
in the coefficient module: a resolution lift induces both its derived-functor
map and postcomposition in Ext, independently of the lift by homotopy. This
identifies postcomposition by the inverse pullback comparison with
scalarCohomologyMap and transports the Ext equality to the displayed formula.
All normalization choices here are determined by their unit or resolution
characterization. In degree zero this is composition of section pullback;
identity arrows, zero coefficients and empty schemes satisfy the same argument.
-/
theorem scalarCohomologyPullback_comp
    (k : Type w) [Field k] (A B C : Scheme.{w})
    (fA : A ⟶ Spec (CommRingCat.of k)) (fB : B ⟶ Spec (CommRingCat.of k))
    (fC : C ⟶ Spec (CommRingCat.of k))
    (a : A ⟶ B) (b : B ⟶ C)
    (ha : a ≫ fB = fA) (hb : b ≫ fC = fB)
    (F : C.Modules) (n : ℕ) (x : scalarCohomology fC F n) :
    scalarCohomologyMap fA ((scalarPullbackCompIso a b).app F).inv n
      (scalarCohomologyPullback fB fA a ha ((tensorPullback b).obj F) n
        (scalarCohomologyPullback fC fB b hb F n x)) =
      scalarCohomologyPullback fC fA (a ≫ b) (by rw [Category.assoc, hb, ha]) F n x := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
