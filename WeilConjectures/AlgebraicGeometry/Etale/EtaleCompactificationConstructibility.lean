/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.Etale.Affine.EtaleAffineLineShriekSheafConstructible
import WeilConjectures.AlgebraicGeometry.Etale.EtaleShriekQcqsComposition
import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteShriekConstructible
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.Compactification.Affine
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Etale.EtaleShriekRelativeMayerVietoris
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleEtaleModuleQcqsAffineLocal
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion

/-!
# Constructibility of the etale compact-support candidate

Source: Stacks Project, Tag 0GL0, theorem-constructible-shriek,
finite-ring bounded-below specialization.
(blueprint: lem-weil-pbc-etale-compactification-constructibility).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
