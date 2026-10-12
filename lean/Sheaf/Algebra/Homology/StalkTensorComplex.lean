/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Sheaf.Algebra.Category.ModuleCat.Sheaf.StalkTensor
import Sheaf.Topology.StalkDirectSums

/-!
# Stalks commute with total tensor complexes

Source: Stacks Project, Cohomology, Lemma 06YB, tensor-stalk identification
(blueprint: lem-pc-stalk-tensor-complex).
-/

@[expose] public section

universe u₁

open CategoryTheory MonoidalCategory TopologicalSpace AlgebraicGeometry

namespace CochainComplex

variable (X : RingedSpace.{u₁}) (x : X)

set_option hygiene false in
local notation "O" => (sheafCompose (Opens.grothendieckTopology (X : Type u₁))
  (forget₂ CommRingCat.{u₁} RingCat.{u₁})).obj X.sheaf
set_option hygiene false in
local notation "S" => (RingedSpace.moduleStalkFunctor X x).mapHomologicalComplex (.up ℤ)

noncomputable local instance : MonoidalCategory (SheafOfModules.{u₁} O) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- (blueprint: lem-pc-stalk-tensor-complex) Stacks Project, Cohomology, Lemma 06YB:
there is an isomorphism from the stalk of the total tensor complex to the total tensor
complex of the stalks, natural in both complexes. Both total complexes use direct sums
in degree `n` over `p + q = n` and differential `d_F ⊗ 1 + (-1)^p 1 ⊗ d_K`.

Proof:
1. By `def-pc-tensor-complex-sheaves`, the degree `n` term is the direct sum of `F^p ⊗ K^q`.
   Apply `lem-pc-stalk-direct-sums` to move the stalk through this direct sum.
2. Apply `lem-pc-ringed-space-module-stalk-tensor` to each summand. Its natural comparison
   identifies the summands with `F_x^p ⊗ K_x^q`, giving the degreewise isomorphisms.
3. Naturality of the module comparison carries the differentials on the two factors to
   their stalk maps. Additivity preserves the sign `(-1)^p`. Thus the maps commute with
   the total differential and form isomorphisms of complexes. The same naturality on each
   summand gives the asserted square for every pair of morphisms of complexes. -/
theorem exists_stalk_tensor_complex_iso :
    ∃ e : ∀ (F K : CochainComplex (SheafOfModules.{u₁} O) ℤ),
      (S).obj (mapBifunctor F K (curriedTensor _)) ≅
        mapBifunctor ((S).obj F) ((S).obj K) (curriedTensor _),
      ∀ (F K F' K' : CochainComplex (SheafOfModules.{u₁} O) ℤ)
        (f : F ⟶ F') (g : K ⟶ K'),
        (S).map (HomologicalComplex.mapBifunctorMap f g (curriedTensor _) (.up ℤ)) ≫
            (e F' K').hom =
          (e F K).hom ≫ HomologicalComplex.mapBifunctorMap
            ((S).map f) ((S).map g) (curriedTensor _) (.up ℤ) := by
  sorry

end CochainComplex
