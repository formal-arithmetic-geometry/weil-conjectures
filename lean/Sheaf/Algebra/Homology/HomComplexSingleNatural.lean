/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M3
-/
module

public import Sheaf.Algebra.Homology.HomComplex
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Homology.Additive

/-! # Naturality of the Hom-complex comparison from a degree-zero source

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, section-hom-complexes.
(blueprint: lem-sc-hom-complex-single-natural).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace CategoryTheory

/-- The single-source Hom-complex identification is natural in the coefficient complex.

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, section-hom-complexes.
(blueprint: lem-sc-hom-complex-single-natural).

Proof:
1. In degree n, project the product defining Hom-complex(P[0],K) to its p = 0 factor.
   The source P[0]^0 is P, and 0 + n = n, so this factor is internal Hom(P,K^n).
   Every other factor is zero because P[0]^p is zero. Insertion of the identity in
   the surviving factor and zero in all other factors is the inverse projection.
   The inverse identities follow by composing with every product projection.
2. The differential formula of homComplex_exists has a postcomposition term and a
   signed precomposition term. The latter is zero because the source differential
   vanishes. Thus the projections form chain maps to termwise internal Hom.
3. For f : K → L, specialize the map formula of homComplex_exists to the identity
   of P[0] and f, then project to p = 0. It says exactly that the degree-n Hom-complex
   map followed by projection equals projection followed by internal Hom(P,f^n).
   Extensionality for chain maps proves the naturality square for these projections.
4. Assemble the component chain isomorphisms with NatIso.ofComponents. Naturality of
   their inverses follows from the inverse identities. This uses only the product
   universal property, so includes zero P, the empty scheme, and unbounded K. -/
theorem homComplex_single_natIso (X : AlgebraicGeometry.Scheme.{u})
    (P : SheafOfModules.{u} (AlgebraicGeometry.moduleRings X.toRingedSpace))
    [((SheafOfModules.homFunctor X.sheaf).obj (op P)).Additive] :
    Nonempty ((homComplexFunctor (R := X.sheaf)).obj
      (op ((CochainComplex.singleFunctor
        (SheafOfModules.{u} (AlgebraicGeometry.moduleRings X.toRingedSpace)) 0).obj P)) ≅
      ((SheafOfModules.homFunctor X.sheaf).obj (op P)).mapHomologicalComplex (.up ℤ)) := by
  sorry

end CategoryTheory
