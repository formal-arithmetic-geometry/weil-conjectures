/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF lead L
-/
import Mathlib.CategoryTheory.Galois.Basic

/-!
# Galois categories in the sense of the Stacks Project

Source: the blueprint of the Weil conjectures, chapter `sec-curve-estimates`, unit `sk-prop-h2`
(blueprint: def-galois-category); Stacks Project, Fundamental Groups of Schemes,
Tag 0BMY (Definition), and Tag 0BMQ (Section) for the topology on `Aut(F)`.

Mathlib's `CategoryTheory.GaloisCategory` with `PreGaloisCategory.FiberFunctor` follows the
axioms G1–G6 of SGA1 / Lenstra, which differ from Stacks' clause by clause (Mathlib assumes
fewer colimits and a weaker exactness of the fibre functor, but assumes G3, and derives the
decomposition into connected objects as `has_decomp_connected_components`); the two notions
agree only through the main theorem. This file states Stacks' axioms as they stand.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace CategoryTheory

/-- (blueprint: def-galois-category) Stacks, Tag 0BMY. Let `C` be a category and
`F : C ⥤ Type w` a functor to sets. The pair `(C, F)` is a *Galois category* if
1. `C` has finite limits and finite colimits;
2. every object `X` of `C` is a finite (possibly empty) coproduct of connected objects: there are
   a finite type `ι`, objects `f i` and morphisms `g i : f i ⟶ X` with `Cofan.mk X g` a colimit
   cofan and each `f i` connected (`PreGaloisCategory.IsConnected`: not initial, and every
   monomorphism `Y ⟶ X` from a non-initial `Y` is an isomorphism);
3. `F.obj X` is finite for every object `X`;
4. `F` is exact (preserves finite limits and finite colimits) and reflects isomorphisms.

The last paragraph of the node (`Aut(F)` as the subgroup of `∏_X Aut(F(X))` of tuples induced
by natural automorphisms, with the topology induced from the product of the discrete
topologies, Tag 0BMQ) is a construction, not a condition: it is Mathlib's instance
`PreGaloisCategory.instTopologicalSpaceAutFunctorFintypeCat`, induced by
`PreGaloisCategory.autEmbedding`, applied to `F` regarded as a functor to `FintypeCat`. -/
structure IsStacksGaloisCategory {C : Type u} [Category.{v} C] (F : C ⥤ Type w) : Prop where
  /-- (1) `C` has finite limits. -/
  hasFiniteLimits : HasFiniteLimits C
  /-- (1) `C` has finite colimits. -/
  hasFiniteColimits : HasFiniteColimits C
  /-- (2) Every object is a finite (possibly empty) coproduct of connected objects. -/
  exists_finite_coproduct_isConnected (X : C) :
    ∃ (ι : Type) (_ : Finite ι) (f : ι → C) (g : (i : ι) → f i ⟶ X),
      Nonempty (IsColimit (Cofan.mk X g)) ∧ ∀ i, IsConnected (f i)
  /-- (3) `F(X)` is finite for every object `X`. -/
  finite_obj (X : C) : Finite (F.obj X)
  /-- (4) `F` is left exact. -/
  preservesFiniteLimits : PreservesFiniteLimits F
  /-- (4) `F` is right exact. -/
  preservesFiniteColimits : PreservesFiniteColimits F
  /-- (4) `F` reflects isomorphisms. -/
  reflectsIsomorphisms : F.ReflectsIsomorphisms

end CategoryTheory
