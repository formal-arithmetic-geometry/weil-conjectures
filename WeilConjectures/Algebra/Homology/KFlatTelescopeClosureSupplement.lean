/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import WeilConjectures.Algebra.Homology.KFlatTelescopeClosure

/-!
# K-flatness and flatness under the telescope construction

Source: Stacks Project, Cohomology on Sites, proof of Lemma 06YS, with Lemmas 06YQ,
06YR and 07A3; Modules on Sites, Lemma 03EU (blueprint: lem-pc-kflat-closure).

The site and module universes are those of the landed `SheafOfModules.IsFlat`
(`C : Type u`, `Category.{u} C`, rings and modules in `u`).
-/
