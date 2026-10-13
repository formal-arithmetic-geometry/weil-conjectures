/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.IdealSheafFiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.Compactification.FiniteTypeExtension
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Finite-type ideal modules
-/

/-! A finite-type ideal sheaf defines a sheaf of modules of finite type.

Source: Stacks Project, Properties, Tag 01PG, and Sheaves of Modules,
Tag 01B4 (the local finite-generator definition).
(blueprint: lem-pqf-finite-type-ideal-module).

Proof: Cover X by affine opens U. By hI, choose a finite family generating I.ideal U.
The range equality for I.toModulesι on U lifts these generators to sections of the
ideal module; injectivity makes the lifts unique. On every smaller affine open V in U,
map_ideal identifies its ideal with the extension of I.ideal U, so the restricted
generators generate the ideal there. The range equality and injectivity identify these ideal
generators with generators of the module sections. The resulting morphism from the
finite free sheaf to I.toModules restricted to U is therefore surjective on this
basis, hence locally surjective and an epimorphism. These finite generating families
on the affine cover give LocalGeneratorsData.IsFiniteType, and therefore IsFiniteType.
For the zero ideal use the empty generating family; the empty scheme has an empty
affine cover, so the same local criterion applies. No compactness is required. -/
