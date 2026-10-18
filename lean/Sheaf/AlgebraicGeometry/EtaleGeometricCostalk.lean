/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.AlgebraicGeometry.IndEtaleClosedSupportBaseChange
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import Sheaf.AlgebraicGeometry.EtaleSupportedSections
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Geometric costalks of bounded below étale module complexes

Source: Gabber, Exposé XVII, Definition 1.1.1 and its footnote, printed pp. 258–259
(blueprint: def-per-etale-geometric-costalk).

The ordinary costalk is formed on the ordinary local scheme, before taking a
geometric fibre. In particular, the strict-local comparison is not its definition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- The closed point immersion of the ordinary local scheme at `z`.
Source: Gabber XVII, Definition 1.1.1
(blueprint: def-per-etale-geometric-costalk). -/
abbrev localClosedPoint (X : Scheme.{u}) (z : X) :
    Spec (X.residueField z) ⟶ Spec (X.presheaf.stalk z) :=
  Spec.map (X.residue z)

/-- Ordinary costalk: restrict to the ordinary local scheme and apply the right
derived supported-kernel inverse image for its closed point.
Source: Gabber XVII, Definition 1.1.1
(blueprint: def-per-etale-geometric-costalk). -/
abbrev etaleCostalk (R : Type (u + 1)) [CommRing R] [Finite R] (X : Scheme.{u}) (z : X) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory.Plus
        (Sheaf (Spec (X.residueField z)).smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  (upperStar (ModuleCat.{u + 1} R) (X.fromSpecStalk z)).mapDerivedCategoryPlus ⋙
    closedSupportPlus R (localClosedPoint X z)

/-- The exact geometric-stalk functor applied to a bounded below complex.
Source: Gabber XVII, Definition 1.1.1
(blueprint: def-per-etale-geometric-costalk). -/
abbrev etaleDerivedGeometricStalk (R : Type (u + 1)) [CommRing R] [Finite R]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory.Plus (ModuleCat.{u + 1} R) :=
  letI := (pointSmallEtale s).sheafFiber_additive (A := ModuleCat.{u + 1} R)
  (pointSmallEtale s).sheafFiber.mapDerivedCategoryPlus

/-- Geometric costalk, using the residue-field embedding of the given geometric point.
Source: Gabber XVII, Definition 1.1.1
(blueprint: def-per-etale-geometric-costalk). -/
abbrev etaleGeometricCostalk (R : Type (u + 1)) [CommRing R] [Finite R]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory.Plus (ModuleCat.{u + 1} R) :=
  etaleCostalk R X ((Scheme.SpecToEquivOfField Ω X) s).1 ⋙
    etaleDerivedGeometricStalk R (Spec.map ((Scheme.SpecToEquivOfField Ω X) s).2)

/-- Supported cohomology on the strict localization, with its closed point as support.
Source: Gabber XVII, Definition 1.1.1 and its footnote
(blueprint: def-per-etale-geometric-costalk). -/
abbrev strictLocalSupportedCostalk (R : Type (u + 1)) [CommRing R] [Finite R]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ X) :
    DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory.Plus (ModuleCat.{u + 1} R) :=
  letI : IsLocalRing (strictHenselization s) := isLocalRing_strictHenselization s
  (upperStar (ModuleCat.{u + 1} R) (strictLocalizationToBase s)).mapDerivedCategoryPlus ⋙
    (supportedEtaleSections R (strictLocalization s)
      ⟨{IsLocalRing.closedPoint (strictHenselization s)}ᶜ,
        (IsLocalRing.isClosed_singleton_closedPoint _).isOpen_compl⟩).rightDerivedFunctorPlus

end AlgebraicGeometry.Etale
