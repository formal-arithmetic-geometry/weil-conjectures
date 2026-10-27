/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J6
-/
module

public import Sheaf.Paper.SectionCompactSourceMaps

/-! # Scalar endpoint square for section compact-source exchange

Source: blueprint rank-one Thom proof, Step 3; Stacks Tags 099R and 095L.
(blueprint: lem-pur-section-source-constant-square)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SectionCompactSource

/-- The scalar endpoint square used to transport the section-source map.

Source: blueprint rank-one Thom proof, Step 3; Stacks Tags 099R and 095L.
Proof: identify the etale and pro-etale constants by the terminal scalar-unit
comparison. Naturality of `Functor.mapDerivedCategoryPlusSingleFunctor` and
the composition comparison for derived functors lift that underived square to
degree zero. The resulting four edges are respectively `compareConstant`,
`constantPull`, `proConstantPull`, and `fixedComparisonPullbackPlus`. This
argument is independent of sections and compactifications and works for every
finite commutative coefficient ring.
-/
theorem constant_square (A : Type (u + 1)) [CommRing A] [Finite A]
    {B' B : Scheme.{u}} (g : B' ⟶ B) :
    (ProEtale.fixedComparisonPullbackPlus A g).hom.app (etaleConstant A B) ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategoryPlus.map
          (compareConstant A B).hom ≫ (proConstantPull A g).hom =
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) B').mapDerivedCategoryPlus.map
        (constantPull A g).hom ≫ (compareConstant A B').hom := by sorry

end AlgebraicGeometry.SectionCompactSource
