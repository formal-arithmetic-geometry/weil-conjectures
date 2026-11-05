/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CohomologyFractionPresentation
public import WeilConjectures.AlgebraicGeometry.Ample
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.LocalizedCohomologyMayerVietoris
import WeilConjectures.AlgebraicGeometry.CohomologySectionLocalizationGluingAux

/-! # Mayer--Vietoris gluing for localization of twisted cohomology

Source: Stacks Project, Cohomology of Schemes, Lemma 09MR, Mayer--Vietoris paragraph
(blueprint: lem-sc-invert-s-cohomology-gluing).
-/

@[expose] public section

universe uG

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
