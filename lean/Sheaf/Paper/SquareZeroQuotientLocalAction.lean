/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N2
-/
module

public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.CategoryTheory.CommAlgebraSheafModule
public import Sheaf.Paper.DerivedHomMayerVietoris

import Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting

/-! # The quotient action on a square-zero ideal

Source: Stacks Project, Cohomology, Lemma 0B8S, first paragraph of the proof.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A square-zero kernel has a local action by the quotient algebra, compatible with
restriction. No resolutions or cohomology occur in this assertion.
Source: Stacks Project, Cohomology, Lemma 0B8S, first paragraph of the proof.
(blueprint: lem-sc-square-zero-quotient-local-action)

Proof: Short exactness identifies I with the kernel sheaf of p. For a section f of C
on U, choose local lifts b on an open cover of U, using that p is an epimorphism of
sheaves. For x in I(U), the product b * i(x) lies in the kernel, hence has a unique
preimage in I on that open. Two lifts differ by a kernel section, so their products
with i(x) agree by square-zero. These preimages therefore glue uniquely. Define
sigma_U(f)(x) to be this glued section. Multiplication is linear over O_X(U), and
its additive, unit, and composition identities follow after restricting to a cover
with lifts and applying the monomorphism i. The same uniqueness proves compatibility
with restriction. For f = p(b), one may use b itself as the lift, giving the displayed
formula. Empty opens and the zero kernel cause no exception: uniqueness gives the
unique action on the zero module. -/
theorem square_zero_quotient_local_action (X : Scheme.{u})
    (B C : X.CommAlgebraSheaf) (p : B ⟶ C)
    (I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (i : I ⟶ commAlgebraSheafModule X.sheaf B)
    (hw : i ≫ (commAlgebraSheafModuleFunctor X.sheaf).map p = 0)
    (hS : (ShortComplex.mk i ((commAlgebraSheafModuleFunctor X.sheaf).map p) hw).ShortExact)
    (hsq : ∀ (U : X.Opens) (x y : B.right.obj.obj (op U)),
      p.right.hom.app (op U) x = 0 → p.right.hom.app (op U) y = 0 → x * y = 0) :
    ∃ (σ : ∀ U : X.Opens, C.right.obj.obj (op U) →+*
        Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (I.val.obj (op U))),
      (∀ (U : X.Opens) (b : B.right.obj.obj (op U)) (x : I.val.obj (op U)),
        @id (B.right.obj.obj (op U)) (i.val.app (op U) (σ U (p.right.hom.app (op U) b) x)) =
          b * @id (B.right.obj.obj (op U)) (i.val.app (op U) x)) ∧
      (∀ (U V : X.Opens) (j : V ⟶ U) (f : C.right.obj.obj (op U)) (x : I.val.obj (op U)),
        I.val.map j.op (σ U f x) = σ V (C.right.obj.map j.op f) (I.val.map j.op x)) := by
  sorry

end AlgebraicGeometry
