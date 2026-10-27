/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O3
-/
module

public import Sheaf.AlgebraicGeometry.SpaceDerivedTensorPullback
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceRelativePerfect
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite

/-! # Relative perfectness over an arbitrary algebraic space

Source: Stacks Project, More on Morphisms of Spaces, Tags 0DKN and 0DKQ
(blueprint: def-sfb-space-relative-perfect-general).
Use the existing scheme-target predicate on all target charts. Bounds remain local.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The scheme represented by an étale target chart, mapped to its algebraic space.
Source: Stacks, Tag 03ED (blueprint: def-sfb-space-relative-perfect-general). -/
def chartSpaceMap {S : Scheme.{u}} (Y : AlgebraicSpace S) (V : Y.EtaleSite) :
    schemeSpace V.obj.left ⟶ Y := ObjectProperty.homMk ⟨V.obj.hom⟩

/-- The actual sheaf fibre product over the chart, bundled as an algebraic space.
This is the existing `enlargedFibreProduct` of `f` and the chart map.
Source: Stacks, Tags 03ED and 03G2 (blueprint: def-sfb-space-relative-perfect-general). -/
abbrev chartBaseChange {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : Y.EtaleSite) : AlgebraicSpace S :=
  enlargedFibreProduct f (chartSpaceMap Y V)

/-- Projection of the chart fibre product to the original source.
Source: Stacks, Tag 0DKQ (blueprint: def-sfb-space-relative-perfect-general). -/
abbrev chartBaseChangeFst {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : Y.EtaleSite) : chartBaseChange f V ⟶ X :=
  enlargedFibreProductFst f (chartSpaceMap Y V)

/-- Projection of the chart fibre product to the represented target scheme.
Source: Stacks, Tag 0DKQ (blueprint: def-sfb-space-relative-perfect-general). -/
def chartBaseChangeSnd {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (V : Y.EtaleSite) : chartBaseChange f V ⟶ schemeSpace V.obj.left :=
  ObjectProperty.homMk (Limits.pullback.snd f.hom (chartSpaceMap Y V).hom)

/-- The standard chart localization is used only internally by the predicate. Ambient
localization morphism size remains arbitrary.
Source: Stacks, Tag 05RU (blueprint: def-sfb-space-relative-perfect-general). -/
instance chartBaseChangeHasDerivedCategory {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (V : Y.EtaleSite) :
    HasDerivedCategory.{u + 1} (chartBaseChange f V).SmallModules :=
  HasDerivedCategory.standard _

/-- Relative perfectness for a space target, using the same scheme-target notion on its
étale charts. That notion tests pseudo-coherence and Tor dimension against every module
sheaf over the inverse-image structure sheaf, with a locally chosen finite interval.
For flat locally finitely presented f this is precisely Definition 0DKN by Lemma 0DKQ.
Source: Stacks, Tags 0DKN and 0DKQ (blueprint: def-sfb-space-relative-perfect-general). -/
def IsPerfectRelativeToSpace {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [HasDerivedCategory.{w} X.SmallModules] (K : X.DerivedModules) : Prop :=
  ∀ V : Y.EtaleSite, IsPerfectRelativeToScheme V.obj.left (chartBaseChangeSnd f V)
    ((derivedTensorPullback (chartBaseChangeFst f V)).obj K)

end AlgebraicGeometry.AlgebraicSpace
