/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import Sheaf.Paper.CompositeIntegrationOperations

/-! # Native integration maps and their structural identities -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityIntegration

variable {C E T : Type w} [Category.{v} C] [Category.{v} E] [Category.{v} T]
  [MonoidalCategory C] [MonoidalCategory E] [MonoidalCategory T]
  [BraidedCategory C] [BraidedCategory E] [BraidedCategory T]

/-- Inverse projection naturality and unit normalization, without adjunction counits.
Source: inverse naturality and unit constraints of native projection maps
(blueprint: lem-pur-native-integration-projection-laws). -/
def IntegrationProjectionLaws (o : IntegrationOperations C T) : Prop :=
  (∀ (L : C) (K K' : T) (h : K ⟶ K')
      (hK : IsIso (o.pf L K)) (hK' : IsIso (o.pf L K')),
    o.F.map (L ◁ o.P.map h) ≫ q o L K' hK' = q o L K hK ≫ (o.F.obj L ◁ h)) ∧
  (∀ (L : C) (hunit : IsIso (o.pf L (𝟙_ T))),
    o.F.map (twistUnit o L).inv ≫ o.F.map (β_ (o.P.obj (𝟙_ T)) L).hom ≫
      q o L (𝟙_ T) hunit = (ρ_ (o.F.obj L)).inv)

/-- The selected site's actual operations and canonical braidings.
Source: site-wise calculation (blueprint: lem-pur-native-integration-projection-laws). -/
def nativeProjectionAssertion
    (b : Bool) (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] : Prop :=
  match b with
  | false =>
      letI := nativeBraiding (Sheaf (X.smallEtaleTopology) (ModuleCat.{u + 1} R))
      letI := nativeBraiding (Sheaf (Y.smallEtaleTopology) (ModuleCat.{u + 1} R))
      letI := nativeBraiding (Sheaf (Z.smallEtaleTopology) (ModuleCat.{u + 1} R))
      IntegrationProjectionLaws (etaleOperations R f g).fg
  | true =>
      letI := nativeBraiding (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} R))
      letI := nativeBraiding (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} R))
      letI := nativeBraiding (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} R))
      IntegrationProjectionLaws (proEtaleOperations R f g).fg

/-- Inverse projection naturality and unit normalization for the native composite map.
Source: `def-exchange-projection`, natural-transformation construction, and the unit
paragraph of `lem-pur-composite-integration-counit`, Steps 3--4
(blueprint: lem-pur-native-integration-projection-laws).

Proof: identify the operation fields with the published maps using their equality
specifications. At fixed L, multiply the projection naturality square for h on both
sides by the two component inverses; this is the first identity and requires no other
invertible components. For the second identity use native projection right unitality:
PF(L,1) followed by F of the pullback unit comparison and the right unitor equals the
right unitor of F L. Invert it. Braiding-unit compatibility identifies the inverse
right-unit source map with inverse twistUnit followed by the displayed symmetry.
For native compactification projection, right unitality follows by expanding the
proper projection as the counit mate of the tensorator, applying monoidal unitality
and the adjunction triangle, and cancelling the unit comparisons of the open tensor
map and pullback compositor. The ordinary-site version is also the published
`Etale.projectionMap_rightUnitality`. The same counit/open construction gives the
pro-etale version. Apply these calculations separately at the two selected sites. -/
theorem nativeIntegrationProjectionLaws
    (b : Bool) (R : Type (u + 1)) [CommRing R] [Finite R]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] :
    nativeProjectionAssertion b R f g := by
  sorry

end WeilConjectures.PurityIntegration
