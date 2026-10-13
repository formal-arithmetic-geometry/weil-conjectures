/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # The derived qcqs projection isomorphism in fixed localizations

Source: Stacks Project, Tag 08EU, Lemma 36.22.1.
(blueprint: lem-pc-qcqs-derived-projection-iso-universes).
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

/-- The qcqs projection formula for quasi-coherent derived objects.
Source: Stacks Project, Tag 08EU, Lemma 36.22.1.
(blueprint: lem-pc-qcqs-derived-projection-iso-universes).

Proof: use the derived pullback/direct-image adjunction and the K-flat tensor
comparison to form the canonical projection map. Its isomorphy is local on Y,
since the three derived operations commute with restriction to target opens.
On an affine target Spec A, fix E and consider those K for which this map is
invertible. Pullback and tensor preserve coproducts, and qcqs direct image preserves
coproducts on quasi-coherent objects; hence the class is closed under coproducts.
Exactness of these functors and compatibility of the canonical map with translation
make it closed under distinguished triangles. For every shift of A the projection
map is the unit and shift comparison and is invertible. The equivalence between
D(A) and D_QCoh(Spec A), and generation by the shifts of A, prove invertibility
for every K. Detect it on an affine cover of Y and take the associated isomorphism.
Perform the argument in standard localizations and transport along the unique
localization equivalences to the supplied source and target categories. The
K-flat tensor, derived pullback and K-injective direct-image comparisons identify
the transported objects with exactly the displayed objects. No Noetherianity,
coherence, support condition or bound is required. Zero factors and empty schemes
are included by the same unit, coproduct and restriction computations. -/
theorem nonempty_qcqs_derivedProjection_iso_universes
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (K : schemeDerivedCategory Y) (hK : schemeDerivedQCohProperty Y K) :
    Nonempty (((schemeDerivedDirectImage f).obj E) ⊗ K ≅
      (schemeDerivedDirectImage f).obj (E ⊗ (derivedPullback f).obj K)) := by sorry

end AlgebraicGeometry
