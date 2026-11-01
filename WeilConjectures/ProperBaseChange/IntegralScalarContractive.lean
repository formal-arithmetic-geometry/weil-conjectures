/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact

import all WeilConjectures.ProperBaseChange.CondensedFieldContinuousRealization
import all WeilConjectures.ProperBaseChange.ProfiniteTestObjectFunctor
import all Mathlib.Topology.Connected.TotallyDisconnected
import all WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import all WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import all Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all Mathlib.CategoryTheory.Whiskering
import all Mathlib.Algebra.Category.Ring.Basic

/-! # Scalar units in the integral coefficient sheaf

Source: Bhatt--Scholze, Section 6.8, integral Nakayama argument.
(blueprint: lem-weil-pbc-integral-scalar-contractive)

The continuous-ring realization argument is generalized from the proved comparison in
`Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality` to a totally disconnected
continuous coefficient ring in Type 0. The helpers below also prove regular-module
linearity on sections and the norm-one continuous reciprocal formula.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj



namespace AlgebraicGeometry.ProEtale

private noncomputable def comparisonAdjoint (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] : Profinite.continuousMapRingObj E ⟶
      (pointLowerStar.obj ((lowerStar AddCommGrpCat.{u + 1} (toSpecZ X)).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
            (continuousMapRingSheaf X E)))) :=
  ⟨{ app := fun S ↦ AddCommGrpCat.ofHom
        { toFun := fun f ↦ ULift.up (f.down.comp (profiniteTestProjection X S.unop))
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
     naturality := by
       intro S T f
       apply ConcreteCategory.hom_ext
       intro g
       apply ULift.ext
       change (g.down.comp f.unop.hom.hom).comp (profiniteTestProjection X T.unop) =
         (g.down.comp (profiniteTestProjection X S.unop)).comp
           ((profiniteToProEtOf X).map f.unop).left.base.hom
       simp only [ContinuousMap.comp_assoc]
       erw [profiniteTestProjection_natural] }⟩

private noncomputable def comparison (X : Scheme.{u}) (E : Type)
    [TopologicalSpace E] [Ring E] [IsTopologicalRing E] :
    condensedRingObj (Profinite.continuousMapRingObj E) X ⟶
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousMapRingSheaf X E)) :=
  ((pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv _ _).symm
      (comparisonAdjoint X E)

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale
open MonObj
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing
open MonObj
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

end AlgebraicGeometry.ProEtale.CondensedRing
