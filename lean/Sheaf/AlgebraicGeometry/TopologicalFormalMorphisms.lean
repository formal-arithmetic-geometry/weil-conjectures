/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.AlgebraicGeometry.AdicPrincipalChartData
public import Mathlib.Geometry.RingedSpace.OpenImmersion

/-! # Continuous local morphisms of adic formal spaces

Source: Stacks Project, Tags 0AHY and 0AHZ, section-formal-schemes-EGA
(blueprint: def-per-topological-formal-morphisms).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- Topologies on all section rings of a ringed space.
Source: Stacks Tag 0AHY (blueprint: def-per-topological-formal-morphisms). -/
abbrev FormalSectionTopologies (X : RingedSpace.{u}) :=
  ∀ U : Opens X, TopologicalSpace (X.presheaf.obj (op U))

/-- A local, sectionwise continuous morphism. Locality refers to the actual stalk maps.
Source: Stacks Tags 0AHY, 0AHZ (blueprint: def-per-topological-formal-morphisms). -/
def IsContinuousFormalMorphism {X Y : RingedSpace.{u}}
    (τX : FormalSectionTopologies X) (τY : FormalSectionTopologies Y) (f : X ⟶ Y) : Prop :=
  (∀ x : X, IsLocalHom (f.hom.stalkMap x).hom) ∧
    ∀ U : Opens Y, @Continuous _ _ (τY U) (τX ((Opens.map f.hom.base).obj U))
      (f.hom.c.app (op U))

/-- A topology is formal if locally it is the inverse-limit topology of a complete Noetherian
formal spectrum. The homeomorphism condition is on all opens inside each chart image.
Source: Stacks Tag 0AHY (blueprint: def-per-topological-formal-morphisms). -/
def IsAdicFormalSectionTopology (X : RingedSpace.{u})
    (τ : FormalSectionTopologies X) : Prop :=
  ∀ x : X, ∃ (R : CommRingCat.{u}) (K : Ideal R),
    IsNoetherianRing R ∧ IsAdicComplete K R ∧
      ∃ a : adicFormalSpec R K ⟶ X,
        SheafedSpace.IsOpenImmersion a ∧ x ∈ Set.range a.hom.base ∧
          ∀ (U : Opens X), (U : Set X) ⊆ Set.range a.hom.base →
            @IsHomeomorph _ _ (τ U)
              (adicFormalSectionTopology R K ((Opens.map a.hom.base).obj U))
              (a.hom.c.app (op U))

/-- A formal fibre-product cone, with the universal property tested on arbitrary locally
Noetherian adic formal spaces and continuous local morphisms, not just adic morphisms.
Source: Stacks Tags 0AHY, 0AHZ (blueprint: def-per-topological-formal-morphisms). -/
def IsContinuousFormalPullback {P X Y S : RingedSpace.{u}}
    (τP : FormalSectionTopologies P) (τX : FormalSectionTopologies X)
    (τY : FormalSectionTopologies Y) (τS : FormalSectionTopologies S)
    (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S) : Prop :=
  p ≫ f = q ≫ g ∧ IsContinuousFormalMorphism τX τS f ∧
    IsContinuousFormalMorphism τY τS g ∧ IsContinuousFormalMorphism τP τX p ∧
    IsContinuousFormalMorphism τP τY q ∧
    ∀ (T : RingedSpace.{u}) (τT : FormalSectionTopologies T),
      IsAdicFormalSectionTopology T τT →
      ∀ (a : T ⟶ X) (b : T ⟶ Y),
        IsContinuousFormalMorphism τT τX a → IsContinuousFormalMorphism τT τY b →
        a ≫ f = b ≫ g →
        ∃! l : T ⟶ P, IsContinuousFormalMorphism τT τP l ∧ l ≫ p = a ∧ l ≫ q = b

end AlgebraicGeometry
