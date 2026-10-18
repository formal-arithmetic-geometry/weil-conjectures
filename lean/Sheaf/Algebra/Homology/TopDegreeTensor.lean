/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q156
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Top cohomology of the total tensor of bounded-above finite free complexes

Source: literature/stacks-project/more-algebra.tex, Section "Tensor products of complexes",
and the direct top-degree quotient calculation in the DAG
(blueprint: lem-trf-local-top-degree-tensor).

The two equations in the statement specify the canonical representative map: tensor the
cycle inclusions, include the top summand in the total complex, and pass to cohomology.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CochainComplex

/-- For bounded-above complexes of finite free modules, tensoring the top cycle
representatives induces an isomorphism on top cohomology. Here `e.hom` is characterized
by its compatibility with cycle representatives, and `t` is uniquely determined by the
first equation because the inclusion of cycles is a monomorphism.

Source: literature/stacks-project/more-algebra.tex, Section "Tensor products of complexes";
the direct top-degree calculation (blueprint: lem-trf-local-top-degree-tensor).

Proof:
1. The bounds imply that only the summand `(a,b)` survives in total degree `a+b`, and
   every term above that degree vanishes. The only incoming summands are `(a-1,b)` and
   `(a,b-1)`, using def-pc-cochain-complex-modules and def-pc-tensor-complex-sheaves.
2. The outgoing differentials vanish, so the top cohomologies of `P` and `Q` are their
   top terms modulo their incoming images. The incoming image in the total top term is
   the sum of the images of `d_P tensor 1` and `(-1)^a 1 tensor d_Q`. The sign does not
   change this image, by the differential convention of def-pc-tensor-complex-sheaves.
3. Apply lem-weil-pbc-tensor-right-exact twice. Quotienting `P^a tensor Q^b` by the first
   image gives `H^a(P) tensor Q^b`, and quotienting further by the second image gives
   `H^a(P) tensor H^b(Q)`. Thus the quotient by the incoming total image is this tensor.
4. This quotient identification sends the tensor of two top classes to the class of
   their tensor in the `(a,b)` summand of the total complex. Its inverse is the displayed
   isomorphism `e`, with the two representative equations of the conclusion. -/
theorem exists_topDegreeTensorIso
    (R : Type u) [CommRing R] (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (a b : ℤ)
    (hPfree : ∀ i : ℤ, Module.Free R (P.X i))
    (hPfinite : ∀ i : ℤ, Module.Finite R (P.X i))
    (hQfree : ∀ i : ℤ, Module.Free R (Q.X i))
    (hQfinite : ∀ i : ℤ, Module.Finite R (Q.X i))
    (hP : ∀ i : ℤ, a < i → IsZero (P.X i))
    (hQ : ∀ i : ℤ, b < i → IsZero (Q.X i)) :
    ∃ (e : P.homology a ⊗ Q.homology b ≅
        (mapBifunctor P Q (curriedTensor (ModuleCat.{u} R))).homology (a + b))
      (t : P.cycles a ⊗ Q.cycles b ⟶
        (mapBifunctor P Q (curriedTensor (ModuleCat.{u} R))).cycles (a + b)),
      t ≫ (mapBifunctor P Q (curriedTensor (ModuleCat.{u} R))).iCycles (a + b) =
        (P.iCycles a ⊗ₘ Q.iCycles b) ≫
          ιMapBifunctor P Q (curriedTensor (ModuleCat.{u} R)) a b (a + b) rfl ∧
      (P.homologyπ a ⊗ₘ Q.homologyπ b) ≫ e.hom =
        t ≫ (mapBifunctor P Q (curriedTensor (ModuleCat.{u} R))).homologyπ (a + b) := by
  sorry

end CochainComplex
