/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedTensorStalk
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero

/-! # Geometric stalk functors with fixed module coefficients

Source: Stacks Project, etale-cohomology.tex, Tag 03PT; sites-modules.tex, Tag 04EQ;
proetale.tex, Tag 0F6B and its pointed-neighbourhood construction
(blueprint: def-sf-fixed-module-geometric-stalk-functors).

This definition interface re-exports the existing fixed-module geometric stalk functors
and their additive structures. It keeps the original names available:
`AlgebraicGeometry.ProEtale.geometricModuleStalkFunctor`,
`AlgebraicGeometry.ProEtale.geometricModuleStalkFunctor_additive`, and
`AlgebraicGeometry.Etale.moduleSheafFiber_additive`.
The two abbreviations below are definitional aliases, with no second colimit construction
or instance. In particular, the pro-etale source category is the fixed-ring module-valued
sheaf category, rather than a category of modules over an independently presented ring
sheaf with a lifted coefficient ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Etale

/-- The existing geometric etale stalk on fixed A-module sheaves. Its additive structure
is the re-exported `moduleSheafFiber_additive`; its map is the existing stalk map.
Source: Stacks Project, Tags 03PT and 04EQ
(blueprint: def-sf-fixed-module-geometric-stalk-functors). -/
abbrev fixedModuleGeometricStalkFunctor (A : Type (u + 1)) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) :
    Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  (pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

/-- A re-export alias of the existing fixed-module pro-etale geometric stalk functor.
Its additive structure is the existing `geometricModuleStalkFunctor_additive`.
The abbreviation preserves both the original colimit data and its map on morphisms.
Source: Stacks Project, Tag 0F6B and its pointed-neighbourhood construction
(blueprint: def-sf-fixed-module-geometric-stalk-functors). -/
abbrev fixedModuleGeometricStalkFunctor (A : Type (u + 1)) [CommRing A]
    {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (t : Spec (.of Ω) ⟶ T) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  geometricModuleStalkFunctor A t

end AlgebraicGeometry.ProEtale
