/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedMapPresheaves
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSiteBoundedConstantModels
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.ConstructibleSheaf.Pullback
import Mathlib.Topology.Connected.Clopen
import Mathlib.CategoryTheory.Sites.Point.Over
import all Mathlib.CategoryTheory.Functor.TypeValuedFlat
import WeilConjectures.CategoryTheory.DerivedCategory.ProperBaseChange.FiniteRingDerivedHomFinite
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstantDerivedMappingSheaves
import WeilConjectures.AlgebraicGeometry.Derived.DerivedMappingPresheavesRestriction
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-!
# Finite-ring derived local constancy

Source: Stacks Project, Tag 094G, lemma-locally-constant; the bounded finite-source
extension of Tag 09BE and connected constancy described in the DAG
(blueprint: lem-weil-pbc-finite-ring-derived-local-constancy).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
