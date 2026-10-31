/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.TraceFormula.ProjectiveBundleProper
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Composition of projective-bundle morphisms

Source: Stacks Project, Morphisms, Lemma 0C4P (lemma-composition-projective)
(blueprint: lem-sfb-projective-bundle-composition).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Over a quasi-compact quasi-separated final base, the composite of two morphisms
projective in the projective-bundle sense is projective in that same sense.

Source: Stacks Project, Morphisms, Lemma 0C4P (lemma-composition-projective).

Proof: First apply `lem-trf-projective-bundle-proper` to both morphisms to obtain
properness. Apply `lem-sfb-projective-bundle-relative-ample` to each projective-bundle
factorization to obtain finite type and respectively relatively ample invertible
modules L on A and M on B. No quasi-compactness or quasi-separatedness of B is required.
Second, `lem-weil-pbc-proper-composition` gives properness of the composite. Apply
`lem-sfb-quasiprojective-qc-composition` to f, g, L and M, using quasi-compactness of C,
to obtain finite type of the composite and an invertible module N on A relatively ample
for that composite. Finally apply `lem-sfb-proper-relative-ample-projective-bundle`
to the proper composite and N, using that C is quasi-compact and quasi-separated. It
embeds A as a closed subscheme of the projective bundle of a finite-type quasi-coherent
module on C, which is exactly the conclusion.
(blueprint: lem-sfb-projective-bundle-composition). -/
theorem projectiveBundle_comp {A B C : Scheme.{u}} [CompactSpace C]
    [QuasiSeparatedSpace C] (f : A ⟶ B) (g : B ⟶ C)
    (hf : IsProjectiveBundle f) (hg : IsProjectiveBundle g) :
    IsProjectiveBundle (f ≫ g) := by
  sorry

end AlgebraicGeometry
