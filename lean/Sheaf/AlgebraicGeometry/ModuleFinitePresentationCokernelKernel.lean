/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Sheaf.AlgebraicGeometry.ModuleFiniteTypeImageExtension
import Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting

/-! # Finite type of relations for a cokernel

Source: Stacks Project, Modules, Lemma 0H96.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

/-- The relations of the quotient presentation are of finite type.
Source: Stacks Project, Modules, Lemma 0H96, proof, lines 1440-1454
(blueprint: lem-weil-pbc-module-finite-presentation-cokernel-kernel).

Proof: Set c = cokernel.π f and π = P.generators.π on U. The kernel of π is
finite type since P has finitely many relations and their map onto that kernel is epi.
The image of f restricted to U is finite type, since restriction preserves finite type
and finite type passes to epi images. Set N = kernel (π ≫ c|U). The restriction of π
maps N onto image(f|U): lift sections locally through the epi π; their lifts belong to N
because c kills them. Its kernel is kernel π, computed sectionwise. This gives a short
exact sequence from kernel π to N to image(f|U). The finite-type extension theorem gives
the result. This argument also applies when either finite generating family is empty.
-/
theorem kernel_composite_cokernel_isFiniteType
    (X : RingedSpace.{u}) (U : TopologicalSpace.Opens X)
    {G H : SheafOfModules.{u} (moduleRings X)} (f : G ⟶ H) [G.IsFiniteType]
    (P : (H.over U).Presentation) [P.IsFinite] :
    (kernel (P.generators.π ≫
      (SheafOfModules.overFunctor (moduleRings X) U).map (cokernel.π f))).IsFiniteType := by
  sorry

end AlgebraicGeometry.RingedSpace
