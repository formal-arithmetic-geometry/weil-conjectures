/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.FiniteDiscreteFiber
import Sheaf.AlgebraicGeometry.FormalFunctionsStalk
import Sheaf.Paper.ZariskiModuleAbelianCohomologyAgree
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar

/-! # Formal functions vanishing over finite fibres

Source: Stacks Project, Cohomology of Schemes, Lemma 30.20.8 (Tag 02OE)
(blueprint: pqf-lem-fff-vanishing).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- For a proper morphism over a locally Noetherian scheme, higher direct images of a
coherent module have zero stalk at every point whose fibre is finite.
Source: Stacks Project, Cohomology of Schemes, Lemma 30.20.8 (Tag 02OE)
(blueprint: pqf-lem-fff-vanishing).

Proof:
1. Apply the pointwise theorem on formal functions to identify the completed stalk with the
inverse limit of the cohomology of infinitesimal neighbourhoods.
2. The infinitesimal neighbourhoods are Noetherian and have finite discrete underlying space,
so their positive-degree cohomology vanishes.
3. Coherence of proper higher direct images makes the stalk finitely generated, and faithful
flatness of completion together with the completion-tensor identification forces it to vanish.
-/
theorem higherDirectImage_stalk_subsingleton_of_finite_fibre
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]
    [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{u} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (y : Y) (hfinite : Set.Finite (f.base ⁻¹' {y}))
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (p : ℕ) (hp : 0 < p) :
    Subsingleton
      ((RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
        ((AlgebraicGeometry.schemeModuleHigherDirectImage f (p : ℤ)).obj F)) := by
  sorry

end AlgebraicGeometry
