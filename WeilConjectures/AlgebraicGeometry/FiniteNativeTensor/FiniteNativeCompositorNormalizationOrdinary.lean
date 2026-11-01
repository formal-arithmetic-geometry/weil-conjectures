/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeCompositorConstruction

/-! # Ordinary presentation normalization helper -/

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

/-- The ordinary derived-category normalization branch of the finite native compositor.
Source: Step 8, ordinary pro-etale coordinates and finite compact-site coherence
(blueprint: lem-pur-finite-native-compositor-normalization).

Proof: Expand the ambient compositor square at `V M`, apply finite compact-site coherence
at `etalePlus M`, and transport the plus-category equality through the bounded/unbounded
compatibility isomorphisms. Cancel the two invertible compact-support comparisons. -/
theorem finiteNativeCompositor_normalization_ordinary
    (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))
    [DomainComparison A true E X] [DomainComparison A true E Y]
    [DomainComparison A true E Z]
    (sf : ArrowComparison A true E f cf)
    (sg : ArrowComparison A true E g cg)
    (sh : ArrowComparison A true E (f ≫ g) ch)
    (T : Compactification.Triangle f g) (M : (etaleDomain A X).FullSubcategory) :
    (nativeDomain A true Z).ι.map
        ((canonicalNativeCompositor A true E cf cg ch sf sg sh).hom.app
          ((V A true E X).obj M)) = nativeCompositorAt A true E cf cg ch T M := by
  sorry
end AlgebraicGeometry.ProEtale.FiniteNativeTensor
