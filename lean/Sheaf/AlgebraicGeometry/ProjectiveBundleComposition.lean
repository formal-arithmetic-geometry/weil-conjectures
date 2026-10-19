/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.TraceFormula.ProjectiveBundleProper

/-!
# Composition of projective-bundle morphisms over a qcqs base

Source: Stacks Project, Morphisms, Lemma 0C4P (lemma-composition-projective),
(blueprint: lem-per-projective-bundle-composition).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- If `f : A ⟶ B` and `g : B ⟶ C` are projective in the projective-bundle sense and
`C` is quasi-compact and quasi-separated, then `f ≫ g` is projective in that sense.

Source: Stacks Project, Morphisms, Lemma 0C4P (lemma-composition-projective).
Proof plan:
1. Apply `lem-trf-projective-bundle-proper` to both maps to get properness. Apply
   `lem-per-projective-bundle-relative-ample` to each map to obtain finite type and
   an invertible module relatively ample for that map. These are the two
   quasi-projectivity conditions and require no qcqs hypothesis on `B`.
2. Use `lem-weil-pbc-proper-composition` to make `f ≫ g` proper. Apply
   `lem-per-quasiprojective-qc-composition` with base `C`, using its quasi-compactness
   and the two relatively ample invertible modules from Step 1. The composite is of
   finite type and admits a relatively ample invertible module `N`.
3. Apply `lem-per-proper-relative-ample-projective-bundle` to `f ≫ g` and `N`.
   Its properness was obtained in Step 2, and its base `C` is qcqs by hypothesis.
   This yields the asserted projective-bundle projectivity.
(blueprint: lem-per-projective-bundle-composition). -/
theorem projectiveBundle_comp {A B C : Scheme.{u}} [CompactSpace C] [QuasiSeparatedSpace C]
    (f : A ⟶ B) (g : B ⟶ C) (hf : IsProjectiveBundle f) (hg : IsProjectiveBundle g) :
    IsProjectiveBundle (f ≫ g) := by
  sorry

end AlgebraicGeometry

end
