/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparisonData
/-! # The specified site projection square

Source: the finite native tensor comparison argument.
(blueprint: lem-pur-finite-native-site-projection-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
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

/-- The site inverse image intertwines the literal compactification projections with
its specified bounded-below proper counit mate and exact open comparison.
Source: the finite tensor comparison in sk-prop-sp-composition, proper and open
projection factors; Stacks Tags 099R, 0B65, 0F5Y and 0GL1.
(blueprint: lem-pur-finite-native-site-projection-square).

Proof: transport the native K-flat monoidal structure through the exact comparison's
left-derived/termwise isomorphism. Its inverse tensorator is precisely the published
derived tensor comparison. The inverse-image square is monoidal, by deriving the
underived site square. Restrict the derived pull/push adjunctions along D+ into D;
the restriction unit and counit formulas identify the specified proper mate with
the ambient counit mate on every bounded-below input. Apply the categorical
projection-mate square to the proper factor. For the open factor, apply the exact
site square for extension by zero and restriction. The two inverse open projection
maps have the same adjunct, the open unit tensored with identity, hence agree;
invert the open isomorphisms. Paste the proper and open squares, using naturality
of the proper mate and the pullback-composition square. Expanding the prescribed
bounded-below/ambient compatibility isomorphisms gives exactly the equation below.
Only M and its displayed tensor input need bounded-below witnesses; K may be
unbounded. In particular, this argument also covers the empty scheme and the zero
coefficient ring, since it uses adjunction identities and tensor universal properties.
-/
theorem finiteNativeSiteProjectionSquare {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
  letI := siteMonoidal A X
  letI := siteMonoidal A Y
  let CX := (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory
  let CY := (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) Y).mapDerivedCategory
  ∀ (M : Etale.DerivedCategoryModule (ULift.{u + 1} A) X)
    (K : Etale.DerivedCategoryModule (ULift.{u + 1} A) Y)
    (hM : _root_.DerivedCategory.TStructure.t.plus M)
    (hT : _root_.DerivedCategory.TStructure.t.plus (M ⊗ (etaleU A f).obj K)),
    CY.map (etaleP A c M K) ≫
        ((compactSupportSiteComparison (ULift.{u + 1} A) c).symm.app
          ⟨M ⊗ (etaleU A f).obj K, hT⟩).hom ≫
        (nativeCompact A true c).map
          ((Functor.Monoidal.μIso CX M ((etaleU A f).obj K)).inv ≫
            (𝟙 (CX.obj M) ⊗ₘ
              (derivedComparisonUpperStarUpperStarIso
                (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).inv.app K)) =
      (Functor.Monoidal.μIso CY ((etaleF A c).obj M) K).inv ≫
        (((compactSupportSiteComparison (ULift.{u + 1} A) c).symm.app ⟨M, hM⟩).hom ⊗ₘ
          𝟙 (CY.obj K)) ≫ nativeP A true c (CX.obj M) (CY.obj K) := by sorry

end AlgebraicGeometry.ProEtale.FiniteNativeTensor
