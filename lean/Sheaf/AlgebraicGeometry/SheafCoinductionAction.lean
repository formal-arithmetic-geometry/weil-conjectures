/-
Copyright (c) 2026 M1. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: M1
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-!
# The sheaf coinduction functor and action

Source: Stacks Project, Tag 0A6F and Tag 0BUZ.
(blueprint: lem-sc-sheaf-coinduction-action).
-/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

/-- Restriction of scalars admits a functor lifting internal Hom to modules over the
larger ring sheaf, with the multiplication action formula. No adjunction is asserted here.

Source: Stacks Project, Modules, Tag 0A6F, lemma-adjoint-tensor-restrict;
Duality, Tag 0BUZ, lemma-compute-sheafhom-affine.
(blueprint: lem-sc-sheaf-coinduction-action).

Proof: For an O_X-module F and open U, take the additive group
Hom_{O_X|U}(A|U,F|U). For a in A(U), precompose a section phi with the
O_X-linear endomorphism of A|U which on W sends b to a|W * b. This is
O_X-linear since A is commutative and the scalar map is a ring map.
These endomorphisms commute with restriction. The identities for addition,
zero, one and multiplication give the A(U)-module laws (commutativity
removes the order reversal from precomposition). Restricting the A-action
along f-sharp gives the existing O_X action on internal Hom, by O_X-linearity
of phi. The restriction maps are additive and semilinear for A, so these
modules form a presheaf. Its additive presheaf is exactly the internal Hom
presheaf; the existing internal Hom sheaf condition makes it an A-module
sheaf. For F -> F', postcomposition defines an A-linear natural morphism.
Identity and composition hold componentwise, yielding H. After restriction
of scalars the identity maps give the natural isomorphism i to K. Unfolding
precomposition gives the claimed action formula. This works also for empty
opens and zero rings, where all modules concerned have the forced zero action. -/
theorem sheafHom_restrictScalars_with_action
    {X Y : Scheme.{u}} (f : Y ⟶ X) :
    let A := ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      RingCat.{u} _ _).obj Y.ringCatSheaf
    let T := SheafOfModules.restrictScalars.{u} f.toRingCatSheafHom
    let M := T.obj (SheafOfModules.unit A)
    let K := (SheafOfModules.homFunctor X.sheaf).obj (op M)
    ∃ H : SheafOfModules.{u} X.ringCatSheaf ⥤ SheafOfModules.{u} A,
      ∃ i : H ⋙ T ≅ K,
        ∀ (F : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
          (a : A.obj.obj (op U)) (φ : (H.obj F).val.obj (op U))
          (W : Over U) (b : A.obj.obj (op W.left)),
          (((i.hom.app F).val.app (op U)).hom (a • φ)).app (op W) b =
            (((i.hom.app F).val.app (op U)).hom φ).app (op W)
              (A.obj.map W.hom.op a * b) := by
  sorry

end AlgebraicGeometry
