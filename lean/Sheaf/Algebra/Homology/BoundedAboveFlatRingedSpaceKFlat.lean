/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Geometry.RingedSpace.Basic

/-!
# Bounded-above flat complexes on a ringed space are K-flat

Source: Stacks Project, Cohomology, Lemma 20.26.9 (Tag 06YD),
label `lemma-bounded-flat-K-flat` (blueprint: lem-pc-bounded-above-flat-kflat).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

namespace CochainComplex

/-- Every bounded-above complex of flat module sheaves on a ringed space is K-flat.
Source: Stacks Project, Cohomology, Lemma 20.26.9 (Tag 06YD)
(blueprint: lem-pc-bounded-above-flat-kflat).

Proof:
1. Fix a point `x`. By `lem-pc-flat-sheaf-stalk-flat`, each stalk of each term is
   flat over the stalk ring. The stalk complex remains bounded above because the
   stalk functor sends zero objects to zero objects.
2. Apply `lem-pc-module-bounded-flat-kflat` to this bounded-above complex of flat
   modules over the stalk ring. Its total tensor with every acyclic stalk complex
   is acyclic.
3. Apply the reverse implication of `lem-pc-kflat-stalk-criterion`: K-flatness of
   every stalk complex implies K-flatness of the original sheaf complex. -/
theorem isKFlat_of_boundedAbove_flat_ringedSpace
    (X : RingedSpace.{u})
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ)
    (hbounded : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (K.X i))
    (hflat : ∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) : K.IsKFlat := by
  sorry

end CochainComplex
