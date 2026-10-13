/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

/-!
# The unsigned tensor bicomplex

Source: Stacks Project, Algebra, Tag 00M3, first paragraph of the proof.
(blueprint: def-weil-pbc-tensor-bicomplex)
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace HomologicalComplex₂

variable {R : Type u} [CommRing R]

/-- The commuting tensor bicomplex, with terms `Pᵢ ⊗ Qⱼ` and no totalization signs.
-- The construction is the canonical Mathlib bifunctor.
Source: Stacks Project, Algebra, Tag 00M3, proof, first paragraph.
(blueprint: def-weil-pbc-tensor-bicomplex) -/
abbrev tensorBicomplex (P Q : ChainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex₂ (ModuleCat.{u} R) (.down ℕ) (.down ℕ) :=
  ((Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R)) (.down ℕ)
      (.down ℕ)).obj P).obj Q

/-- A pair of chain maps acts termwise on the tensor bicomplex.
Source: Stacks Project, Algebra, Tag 00M3, functoriality paragraph.
(blueprint: def-weil-pbc-tensor-bicomplex) -/
abbrev tensorBicomplexMap {P P' Q Q' : ChainComplex (ModuleCat.{u} R) ℕ}
    (a : P ⟶ P') (b : Q ⟶ Q') :=
  (Functor.uncurry.obj
    (Functor.mapBifunctorHomologicalComplex (curriedTensor (ModuleCat.{u} R))
      (.down ℕ) (.down ℕ))).map (X := (P, Q)) (Y := (P', Q')) (a, b)

/-- The tensor of a chain map with a module map, formed by mapping the chain map
and then the module map.
Source: Stacks Project, Algebra, Tag 00M3, functoriality paragraph.
(blueprint: def-weil-pbc-tensor-bicomplex) -/
def chainTensorMap {P P' : ChainComplex (ModuleCat.{u} R) ℕ}
    {N N' : ModuleCat.{u} R} (a : P ⟶ P') (g : N ⟶ N') :
    ((tensorRight N).mapHomologicalComplex (.down ℕ)).obj P ⟶
      ((tensorRight N').mapHomologicalComplex (.down ℕ)).obj P' :=
  -- Canonical composite of the two induced chain maps.
  ((tensorRight N).mapHomologicalComplex (.down ℕ)).map a ≫
    (NatTrans.mapHomologicalComplex ((tensoringRight (ModuleCat R)).map g)
      (.down ℕ)).app P'

end HomologicalComplex₂
