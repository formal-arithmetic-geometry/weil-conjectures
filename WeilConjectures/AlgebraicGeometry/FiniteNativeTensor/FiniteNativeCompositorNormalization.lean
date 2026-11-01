/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeCompositorConstruction
import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeCompositorNormalizationOrdinary
import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeCompositorNormalizationInternal

/-! # Normalization of the finite native compositor

Source: the finite native tensor comparison argument.
(blueprint: lem-pur-finite-native-compositor-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
universe u u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.FiniteNativeTensor
open FiniteDiscreteOrdinary
-- Discard the imported instance with a free coefficient universe.
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
attribute [local instance 20000] sheafBraidedCategory sheafSymmetricCategory
  sheafMonoidalCategory sheafMonoidalClosed
  preservesColimitsOfSize_tensorLeft_sheaf preservesColimitsOfSize_tensorRight_sheaf
attribute [local instance 2000] Mod.monoidalCategory Mod.monoidalClosed
attribute [local irreducible] Mod.monoidalClosed
attribute [local irreducible] Sheaf.monoidalCategory SheafOfModules.monoidalCategory

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]

/-- The compositor constructed by domain-equivalence descent is the specified native
proper/open tower paste, on every etale-origin input and for every compactification triangle.
Source: finite native tensor comparison, Step 8; finiteCompactSiteCoherence; the
section-action operations comparison.
(blueprint: lem-pur-finite-native-compositor-normalization).

Proof: Use canonicalNativeCompositor_ambientSquare to write the constructed map in
terms of the three prescribed B comparisons. First use ordinary pro-etale coordinates.
Apply finiteCompactSiteCoherence to
the bounded-below object etalePlus M. The three plus/unbounded compatibility isomorphisms,
their naturality, and the site pullback compatibility identify its etale side with
canonicalEtaleCompositor and its ordinary side with ordinaryCompositorAt. The B
normalizations identify the remaining boundary factors, so cancellation gives exactly
the value of canonicalNativeCompositor on V M. For internal modules apply the fixed
section-action derived equivalence. Each compact-support comparison is compactEncoding;
its two proper/open factors are the specified derived section-action comparisons.
Move these comparisons through the composite using their naturality. The adjacent
encoding comparisons and their inverses cancel, and the encoding counit identifies
the site-origin object. What remains is precisely the ordinary paste surrounded by
the six boundary factors in internalCompositorAt. The fixed encoding is faithful, so
the original maps agree. The comparison is independent of the triangle because
finiteCompactSiteCoherence holds for every triangle and includes refinement changes. -/
theorem finiteNativeCompositor_normalization
    (ordinary : Bool) (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian Z]
    [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    (cf : Compactification f) (cg : Compactification g) (ch : Compactification (f ≫ g))
    [DomainComparison A ordinary E X] [DomainComparison A ordinary E Y]
    [DomainComparison A ordinary E Z]
    (sf : ArrowComparison A ordinary E f cf)
    (sg : ArrowComparison A ordinary E g cg)
    (sh : ArrowComparison A ordinary E (f ≫ g) ch)
    (T : Compactification.Triangle f g) (M : (etaleDomain A X).FullSubcategory) :
    (nativeDomain A ordinary Z).ι.map
        ((canonicalNativeCompositor A ordinary E cf cg ch sf sg sh).hom.app
          ((V A ordinary E X).obj M)) = nativeCompositorAt A ordinary E cf cg ch T M    := by
  cases ordinary
  · exact finiteNativeCompositor_normalization_internal A E cf cg ch sf sg sh T M
  · exact finiteNativeCompositor_normalization_ordinary A E cf cg ch sf sg sh T M



end AlgebraicGeometry.ProEtale.FiniteNativeTensor
