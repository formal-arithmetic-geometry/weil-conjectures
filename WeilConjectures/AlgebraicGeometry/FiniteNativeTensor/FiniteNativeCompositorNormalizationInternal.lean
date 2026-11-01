/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeCompositorConstruction

/-! # Internal presentation normalization helper -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.FiniteNativeTensor
open FiniteDiscreteOrdinary
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
attribute [local instance 20000] sheafBraidedCategory sheafSymmetricCategory
  sheafMonoidalCategory sheafMonoidalClosed
  preservesColimitsOfSize_tensorLeft_sheaf preservesColimitsOfSize_tensorRight_sheaf
attribute [local instance 2000] Mod.monoidalCategory Mod.monoidalClosed
attribute [local irreducible] Mod.monoidalClosed
attribute [local irreducible] Sheaf.monoidalCategory SheafOfModules.monoidalCategory
variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]

/-- The internal section-action normalization branch of the finite native compositor.
Source: Step 8, internal derived section-action coordinates and encoding compactification
(blueprint: lem-pur-finite-native-compositor-normalization).

Proof: Apply the ambient compositor square and transport it through the faithful fixed
section-action derived equivalence. Expand each compact-support comparison as its proper
and open encoding factors, use their naturality and the encoding counit, and cancel the
adjacent inverse factors. The remaining map is exactly `internalCompositorAt`. -/
theorem finiteNativeCompositor_normalization_internal
    (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))
    [DomainComparison A false E X] [DomainComparison A false E Y]
    [DomainComparison A false E Z]
    (sf : ArrowComparison A false E f cf)
    (sg : ArrowComparison A false E g cg)
    (sh : ArrowComparison A false E (f ≫ g) ch)
    (T : Compactification.Triangle f g) (M : (etaleDomain A X).FullSubcategory) :
    (nativeDomain A false Z).ι.map
        ((canonicalNativeCompositor A false E cf cg ch sf sg sh).hom.app
          ((V A false E X).obj M)) = nativeCompositorAt A false E cf cg ch T M := by
  sorry
end AlgebraicGeometry.ProEtale.FiniteNativeTensor
