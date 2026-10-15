/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Sheaves on the small etale site

Source: the blueprint of the Weil conjectures, chapter `sec-abelian-varieties`, unit
`sk-prop-av-finite-etale-points` (blueprint: def-weil-pbc-etale-sheaves).

## Main definitions

* `IsLocallyConstantEtaleSheafOfSets`: etale locally constant sheaves of sets.
* `IsFiniteLocallyConstantEtaleSheafOfSets`: those with finite geometric stalks.
* `IsConstructibleEtaleSheafOfSets`: finite locally constant on constructible strata.
* `HasTorsionEtaleCohomology`: derived objects with torsion cohomology sheaves.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A sheaf of sets on the small etale site of `T` is locally constant when an etale cover
of `T` makes its restriction to each member constant. The restriction `F.over U` is the
sheaf on the site localized at `U`, canonically equivalent to the small etale site of `U`.
Source: blueprint `sec-abelian-varieties/sk-prop-av-finite-etale-points`, definition
(blueprint: def-weil-pbc-etale-sheaves). -/
def IsLocallyConstantEtaleSheafOfSets {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) : Prop :=
  ∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i : 𝒰.I₀,
    (F.over (𝒰.etalePrecoverageToEtale i)).IsConstant
      (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))

/-- A locally constant sheaf of sets is finite locally constant when all its geometric
stalks are finite. Source: blueprint `sec-abelian-varieties/sk-prop-av-finite-etale-points`,
definition (blueprint: def-weil-pbc-etale-sheaves). -/
def IsFiniteLocallyConstantEtaleSheafOfSets {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) : Prop :=
  IsLocallyConstantEtaleSheafOfSets F ∧
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ T),
      Finite (((pointSmallEtale s).sheafFiber (A := Type (u + 1))).obj F)

/-- On sheaves of sets, *lisse* is synonymous with finite locally constant.
Source: blueprint `sec-abelian-varieties/sk-prop-av-finite-etale-points`, definition
(blueprint: def-weil-pbc-etale-sheaves). -/
abbrev IsLisseEtaleSheafOfSets {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) : Prop :=
  IsFiniteLocallyConstantEtaleSheafOfSets F

/-- Pullback of set-valued sheaves along a morphism of schemes: left Kan extension along
base change on small etale sites, followed by sheafification. Source: blueprint
`sec-abelian-varieties/sk-prop-av-finite-etale-points`, constructible-sheaf clause
(blueprint: def-weil-pbc-etale-sheaves). -/
noncomputable def etaleSetPullback {T Z : Scheme.{u}} (g : Z ⟶ T) :
    Sheaf T.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf Z.smallEtaleTopology (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
    (T.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)

/-- A sheaf of sets is constructible if a finite stratification into constructible,
locally closed subschemes makes its sheaf pullback to each stratum finite locally constant.
Source: blueprint `sec-abelian-varieties/sk-prop-av-finite-etale-points`, definition
(blueprint: def-weil-pbc-etale-sheaves). -/
def IsConstructibleEtaleSheafOfSets {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) : Prop :=
  ∃ S : Stratification T, ∀ i : Fin S.n,
    IsFiniteLocallyConstantEtaleSheafOfSets
      ((etaleSetPullback (S.immersion i)).obj F)

/-- A derived object of abelian sheaves has torsion cohomology when each of its
cohomology sheaves is torsion in the local-section sense. Source: blueprint
`sec-abelian-varieties/sk-prop-av-finite-etale-points`, definition
(blueprint: def-weil-pbc-etale-sheaves). -/
def HasTorsionEtaleCohomology {T : Scheme.{u}}
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) : Prop :=
  ∀ r : ℤ, CategoryTheory.Sheaf.IsTorsion
    ((DerivedCategory.homologyFunctor
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) r).obj K)

end AlgebraicGeometry.Scheme
