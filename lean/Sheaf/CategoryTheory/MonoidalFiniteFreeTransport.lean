/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian

/-!
# Additive monoidal transport of a finite free internal module

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md, third sentence.
(blueprint: lem-sfb-monoidal-finite-free-transport)

The biproducts are taken in the existing category of internal modules. Their actions
are componentwise, as constructed in `CategoryTheory.ModuleObjects.Abelian`.
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ v₁ v₂

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

-- Mathlib exposes this finite-to-binary conversion as a theorem, not an instance.
attribute [local instance] CategoryTheory.Limits.hasBinaryBiproducts_of_finite_biproducts

namespace CategoryTheory.Functor

/-- An additive strong monoidal functor transports a specified finite free basis,
including its coordinate maps and the Kronecker and finite-sum identities.

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-sfb-cartesian-coefficients/lem-sfb-subfield-flat.proof.md, third sentence.
(blueprint: lem-sfb-monoidal-finite-free-transport)

Proof:
1. Form the biproduct of regular modules with the componentwise action. On its
   underlying biproduct the action is the sum of projection, multiplication and
   inclusion. Projecting its unit and associativity equations reduces them to the
   regular-module axioms. Tensor additivity and the Kronecker identities make both
   inclusions and projections linear (sk-def-sfb-module-objects).
2. Put u_i = inclusion_i followed by theta, and v_i = theta inverse followed by
   projection_i. They are linear, v_i u_j is the Kronecker identity, and the sum
   of u_i v_i is the identity, using bilinearity of composition
   (def-weil-preadditive-category).
3. Apply mapMod from def-sfb-modobj-transport to these maps. The transported regular
   action is exactly the multiplication of the transported ring. The strong monoidal
   structure supplies its lax structure, with no symmetry requirement.
4. Additivity of P preserves zero and finite sums; functoriality therefore gives
   the same Kronecker and total identities for P(u_i) and P(v_i)
   (def-weil-pbc-additive-functor).
5. Define alpha as the sum of target projections followed by P(u_i), and beta as
   the sum of P(v_i) followed by target inclusions. Every summand is linear;
   tensor additivity and bilinearity make their finite sums linear too.
6. Expand both composites of alpha and beta and use the identities of step 4 and
   the target biproduct identities. They are identities, and composing with one
   inclusion or projection gives the two required formulas. For n = 0 all sums
   are empty, the target biproduct is zero, and step 4 gives id on P(M) equal to
   zero, so the same construction remains an isomorphism.
-/
theorem monoidalFiniteFreeTransport
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [MonoidalCategory C]
    [HasFiniteBiproducts C] [MonoidalPreadditive C]
    {D : Type u₂} [Category.{v₂} D] [Preadditive D] [MonoidalCategory D]
    [HasFiniteBiproducts D] [MonoidalPreadditive D]
    (P : C ⥤ D) [P.Additive] [P.Monoidal] (R : C) [MonObj R]
    (M : Mod C R) (n : ℕ) (θ : (⨁ fun _ : Fin n => Mod.regular R) ≅ M) :
    ∃ α : (⨁ fun _ : Fin n => Mod.regular (P.obj R)) ≅ (P.mapMod R).obj M,
      (∀ i : Fin n,
        (biproduct.ι (fun _ : Fin n => Mod.regular (P.obj R)) i).hom ≫ α.hom.hom =
          P.map ((biproduct.ι (fun _ : Fin n => Mod.regular R) i).hom ≫ θ.hom.hom)) ∧
      (∀ i : Fin n,
        α.inv.hom ≫ (biproduct.π (fun _ : Fin n => Mod.regular (P.obj R)) i).hom =
          P.map (θ.inv.hom ≫ (biproduct.π (fun _ : Fin n => Mod.regular R) i).hom)) ∧
      (∀ i j : Fin n,
        P.map ((biproduct.ι (fun _ : Fin n => Mod.regular R) j).hom ≫ θ.hom.hom) ≫
            P.map (θ.inv.hom ≫ (biproduct.π (fun _ : Fin n => Mod.regular R) i).hom) =
          if i = j then 𝟙 (P.obj R) else 0) ∧
      (∑ i : Fin n,
        P.map (θ.inv.hom ≫ (biproduct.π (fun _ : Fin n => Mod.regular R) i).hom) ≫
          P.map ((biproduct.ι (fun _ : Fin n => Mod.regular R) i).hom ≫ θ.hom.hom)) =
        𝟙 (P.obj M.X) := by
  sorry

end CategoryTheory.Functor
