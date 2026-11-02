/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFourierTransform
public import WeilConjectures.AlgebraicGeometry.DualBundlePairing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed
public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.FourierKernelLisse
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTensorObj
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.PodCondensedAutomorphismCompactExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GeometricFourier.CondensedFourierBaseLinear
public import WeilConjectures.WeilSheaf.CondensedModule.CondensedModuleLocalFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.FourierTransform.ConstantStalkLocalUnitPoint.ConstantStalkLocalUnitPoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal

/-! # The specified Fourier stalk comparison and its semilinear local data

Source: literature/blueprint/latest/blueprint/part-weights-riemann-hypothesis/
sec-fourier-transform/sec-fourier-inversion/sk-thm-inversion/
lem-fd-stalk-formula.proof.md and lem-wft-fourier-weil.proof.md.
(blueprint: def-fd-canonical-stalk-comparison).

The constructions are given on the ambient ordinary condensed module derived categories.
Their bounded constructible restrictions use precisely the same arrows. The compact-support
exchange is the proper/open composite of det-prop-sf-cbc.

## Main definitions

* `stalkComparison`: the canonical map on the literal Fourier product.
* `finiteStalkComparison`: its finite-field Cartesian-cone presentation.
* `fibreEta`, `fibreIntegralDatum`, `localDatum`: the two semilinear local data.
* `transformLocalDatum`: the local datum with the published transform descent.
* `stalkComparison_isIso`: invertibility of the specified finite-field map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.FourierStalk

open CompactificationReindexing WeilConjectures.ConstantStalkLocalUnitPoint

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing.FourierStalk

namespace AlgebraicGeometry.ProEtale.CondensedRing.FourierStalk

open CompactificationReindexing WeilConjectures.ConstantStalkLocalUnitPoint

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

variable (D₀ : WeilConjectures.FiniteFieldDatum.{u})

end AlgebraicGeometry.ProEtale.CondensedRing.FourierStalk

namespace AlgebraicGeometry.ProEtale.CondensedRing.FourierStalk

open CompactificationReindexing WeilConjectures.ConstantStalkLocalUnitPoint

variable (D₀ : WeilConjectures.FiniteFieldDatum.{u})
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
variable {S₀ V₀ Y₀ : Over (Spec (.of D₀.k₀))}
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- The fibre self-map commutes with restriction to V and fixes the map to the
arithmetic product, so it fixes its descended character kernel.
Source: the induced semilinear automorphism and descended kernel clauses of the node
(blueprint: def-fd-canonical-stalk-comparison).
Proof: compose pullback.map_fst with the geometric first projection. Naturality of
model Frobenius and its positive iterates gives the first commuting square. For the
second identity use pullback.map_fst and that every iterate of id times scalar
Frobenius fixes the arithmetic projection. These are equalities on the arithmetic
and closure projections, so pullback uniqueness proves them. -/
theorem finiteFibreFrobenius_properties (p : V₀ ⟶ S₀) (p' : Y₀ ⟶ S₀)
    (n : ℕ) (hn : 1 ≤ n) (ξ₀ : D₀.extensionPoints Y₀ n hn)
    (ι : D₀.extensionSubfield n hn →+* D₀.k)
    (hι : ι.comp (D₀.extensionEmbedding n hn) = algebraMap D₀.k₀ D₀.k) :
    CommSq (fibreFrobenius D₀ (GeometricFourier.snd D₀ p p') n hn ξ₀ ι hι)
      (pullback.fst (GeometricFourier.map D₀ (GeometricFourier.snd D₀ p p'))
          (embeddingPoint D₀ Y₀ n hn ξ₀ ι hι) ≫
        GeometricFourier.map D₀ (GeometricFourier.fst D₀ p p'))
      (pullback.fst (GeometricFourier.map D₀ (GeometricFourier.snd D₀ p p'))
          (embeddingPoint D₀ Y₀ n hn ξ₀ ι hι) ≫
        GeometricFourier.map D₀ (GeometricFourier.fst D₀ p p'))
      (WeilConjectures.localPositivePower (StrictWeilCondensed.modelFrobenius D₀ V₀).hom (n - 1)) ∧
    fibreFrobenius D₀ (GeometricFourier.snd D₀ p p') n hn ξ₀ ι hι ≫
        (pullback.fst (GeometricFourier.map D₀ (GeometricFourier.snd D₀ p p'))
            (embeddingPoint D₀ Y₀ n hn ξ₀ ι hι) ≫
          GeometricFourier.projection D₀ (GeometricFourier.square D₀ p p')) =
      pullback.fst (GeometricFourier.map D₀ (GeometricFourier.snd D₀ p p'))
          (embeddingPoint D₀ Y₀ n hn ξ₀ ι hι) ≫
        GeometricFourier.projection D₀ (GeometricFourier.square D₀ p p') := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.FourierStalk

namespace AlgebraicGeometry.ProEtale.CondensedRing.FourierStalk

open CompactificationReindexing WeilConjectures.ConstantStalkLocalUnitPoint

end AlgebraicGeometry.ProEtale.CondensedRing.FourierStalk

namespace AlgebraicGeometry.ProEtale.CondensedRing.FourierStalk

open CompactificationReindexing WeilConjectures.ConstantStalkLocalUnitPoint

end AlgebraicGeometry.ProEtale.CondensedRing.FourierStalk
