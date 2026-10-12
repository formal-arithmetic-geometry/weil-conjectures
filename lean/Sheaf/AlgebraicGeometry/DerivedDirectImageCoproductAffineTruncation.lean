/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Limits.Shapes.Products

import Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums
import Sheaf.AlgebraicGeometry.Modules.QuasicoherentBinarySum
import Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections
import Sheaf.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound
import Sheaf.Algebra.Homology.KInjectiveRestrictOpen

/-! # Uniform truncation of the two sides over an affine open

Source: Stacks Project, Tags 08DZ and 08D5(2)
(blueprint: lem-pc-derived-direct-image-coproduct-affine-truncation).
-/

@[expose] public section

universe u₁ w₁ w₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Over one affine open, the two vertical maps of the coproduct comparison square
are isomorphisms for a common lower truncation. The integer may depend on that open.
Source: Stacks Project, Tag 08DZ, truncation argument using Tag 08D5(2)
(blueprint: lem-pc-derived-direct-image-coproduct-affine-truncation).

Proof. The ambient coproduct has quasi-coherent cohomology, since exact sums commute
with homology and sums of quasi-coherent modules are quasi-coherent (finite partial
sums followed by a directed colimit). Restrict f to the affine open U. Its source is
qcqs, and its target is quasi-compact. Exact restriction preserves coproducts and
commutes with truncation. A restricted K-injective representative is K-injective,
so restriction computes derived direct image for this restricted morphism. Choose
its uniform upper bound N on all quasi-coherent objects with no positive cohomology.
Choose a ≤ q-N. The upper-truncation term τ<a of every E i and of S has
cohomology only in degrees ≤ a-1, so its direct image vanishes in degrees m with
N+a-1 ≤ m, by shifting the same uniform bound. This kills both degrees q and q+1,
independently of i. The truncation triangle then makes
H^q(Rf_*E i) → H^q(Rf_*τ≥a E i) and the analogous map for S isomorphisms after
restriction to U. Since restriction preserves sums, the sum of the former maps is
also an isomorphism after restriction. Evaluation at U preserves these isomorphisms,
giving exactly the two assertions. For an empty index type the first map is the
isomorphism between zero coproducts. No compactness of Y or familywise choice of
object-dependent truncation bounds is used. -/
theorem exists_derivedDirectImage_coproduct_affine_truncation
    {X Y : Scheme.{u₁}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))]
    (I : Type u₁) (E : I → schemeDerivedQCohCategory X)
    (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (q : ℤ) (U : Y.Opens) (hU : IsAffineOpen U) :
    ∃ a : ℤ,
      IsIso ((SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op U)).map
        (Limits.Sigma.map (fun i ↦ (schemeHigherDirectImage f q).map
          ((DerivedCategory.TStructure.t.truncGEπ a).app (E i).obj)))) ∧
      IsIso ((SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op U)).map
        ((schemeHigherDirectImage f q).map
          ((DerivedCategory.TStructure.t.truncGEπ a).app S))) := by
  sorry

end AlgebraicGeometry
