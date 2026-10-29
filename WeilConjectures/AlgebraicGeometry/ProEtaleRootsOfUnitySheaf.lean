/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.AlgebraicGeometry.ProEtaleUnitsSheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Grp.EpiMono

/-! # Roots of unity on the small pro-etale site

Source: Stacks Project, Section 59.28, Tag 03PK; Definition 59.23.1, Tag 03P4
(auxiliary; not a blueprint node).

The power map, kernel, constant-ring module and transition maps use the original
sectionwise global-sections rings. No invertibility hypothesis on the exponent is imposed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The `N`-th power morphism on `G_m`, written additively as `N • 𝟙`.
Source: Stacks Project, Tag 03PK (auxiliary; not a blueprint node). -/
def proEtaleUnitsPower (S : Scheme.{u}) (N : ℕ) :
    proEtaleUnitsSheaf S ⟶ proEtaleUnitsSheaf S :=
  N • 𝟙 (proEtaleUnitsSheaf S)

/-- The sheaf of `N`-th roots of unity, the kernel of the power map on `O_Sˣ`.
Source: Stacks Project, Tags 03PK and 03P4 (auxiliary; not a blueprint node). -/
noncomputable def proEtaleRootsOfUnitySheaf (S : Scheme.{u}) (N : ℕ) :
    Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1} :=
  kernel (proEtaleUnitsPower S N)

/-- The canonical inclusion of roots of unity into units.
Source: Stacks Project, Tags 03PK and 03P4 (auxiliary; not a blueprint node). -/
noncomputable def proEtaleRootsOfUnityInclusion (S : Scheme.{u}) (N : ℕ) :
    proEtaleRootsOfUnitySheaf S N ⟶ proEtaleUnitsSheaf S :=
  kernel.ι (proEtaleUnitsPower S N)

end AlgebraicGeometry.Scheme
