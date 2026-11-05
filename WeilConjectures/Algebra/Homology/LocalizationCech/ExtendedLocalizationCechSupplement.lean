/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Data.Finset.Sort
public import WeilConjectures.AlgebraicGeometry.ExtendedLocalizationCech

/-! # Extended localization Čech complexes on ringed sites

Source: Stacks Project, Tags 0913 and 099H
(blueprint: def-weil-pbc-extended-localization-cech).

The construction uses the explicit cochain Koszul colimit of Tag 0913. Its degree-q
summands are indexed by subsets of cardinality q, including the empty subset in degree
zero. The transition on the subset I multiplies by the product of the f_i in I.
Thus its termwise colimit is the sheafification of the localization at that product;
the differential is the alternating localization differential. Finite coproducts are
finite products. The empty-subset transition is the identity, identifying degree zero
canonically with the original ring sheaf. For an empty family only degree zero remains.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules
namespace LocalizationCech

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

end LocalizationCech
end SheafOfModules
