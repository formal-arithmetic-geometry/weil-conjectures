/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.Paper.ModuleCupResolutionData

/-! # Scalar and module cup compatibility

Source: Stacks Project, Cohomology, section-cup-product and Tag 0FKV.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

/-- The scalar Ext cup agrees with any cup computed by acyclic module resolutions.
Source: Stacks Project, Cohomology, section-cup-product and Tag 0FKV.
(blueprint: lem-sc-scalar-cup-module-cup-compatibility).

Proof: Choose acyclic resolutions with a sectionwise tensor pairing extending the
augmentation tensor map. Represent the two module cohomology classes by cycles in
these resolutions. Evaluation at 1 identifies the module Hom complex from the unit
with its sections complex. Exact restriction to k and precomposition by the scalar
unit identify these cycles with the classes under scalarCohomologyExtEquiv. The
Yoneda tensor pairing is represented by the signed total tensor of the two cycles.
Its augmentation coefficient is scalarTensorCoefficient, which sends pure tensors
of sections to tmulSection. Thus this pairing is exactly the module resolution
pairing, including its differential sign. Apply IsModuleCupProduct to the paired
cycle. Its target class is the scalar cup by the preceding identification. The
resolution comparison maps and homotopy independence ensure that this conclusion
is independent of all chosen resolutions and representatives. No pullback is used.
In degree zero this is the pure tensor of sections; empty schemes and zero
coefficients have zero classes and the same identities. The cup hypothesis below
is the defining formula of IsModuleCupProduct, expanded to avoid importing its
unrelated existence proof. -/
theorem scalarCup_moduleCup_compatibility
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
        (@id X.Modules (F ⊗ G)))
    (hcup :
      ∀ (D : CupResolutionPairing F G)
        (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          cup (D.left.class p a) (D.right.class q b) = D.target.class (p + q) c)
    (a : scalarCohomology f F p) (b : scalarCohomology f G q) :
    scalarCohomologyCup f F G p q a b = cup a b := by sorry

end AlgebraicGeometry.Scheme.Modules
