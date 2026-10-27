/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.Topology.ContinuousMapCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Sheaf.Paper.NormContinuousMonodromyData
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.Paper.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Sheaf.AlgebraicGeometry.ProEtaleSheafTopologicalInvariance
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction
import Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.EtaleComparison
import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutionsExact
import Sheaf.CategoryTheory.DerivedCategory.LeftDerivedExactComparison
import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# Rational unit retractions for radicial-etale covers

Source: Stacks Project, Tag 03SE, definition-trace-map and its sum and degree formulas;
Tag 09AB, lemma-thickening; the continuous internal-module extension in the DAG proof.
(blueprint: lem-sfb-radicial-etale-rational-unit-retraction).

The sheet projections below are counit maps, so the local sum formula specifies the
trace without choosing an arbitrary product identification. Derived comparisons are
those of the stipulated total derived functors, with their actual adjunction unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The projection onto a sheet of an etale splitting, defined by the actual counit.
Source: Stacks Tag 03SE, split-cover description of restriction and trace.
(blueprint: lem-sfb-radicial-etale-rational-unit-retraction). -/
def rationalTraceSheetProjection {T S U : Scheme.{u}} (e : T ⟶ S) (q : U ⟶ S)
    (s : U ⟶ T) (hs : s ≫ e = q)
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    (upperStar Λ q).obj ((lowerStar Λ e).obj ((upperStar Λ e).obj M)) ⟶
      (upperStar Λ q).obj M :=
  eqToHom (congrArg (fun g ↦ (upperStar Λ g).obj
      ((lowerStar Λ e).obj ((upperStar Λ e).obj M))) hs.symm) ≫
    (upperStarComp Λ s e).hom.app _ ≫
    (upperStar Λ s).map
      ((upperStarLowerStarAdjunction Λ e).counit.app ((upperStar Λ e).obj M)) ≫
    (upperStarComp Λ s e).inv.app M ≫
    eqToHom (congrArg (fun g ↦ (upperStar Λ g).obj M) hs)

/-- Remove the radicial factor using the inverse of its actual unit, and the recorded
composition isomorphisms. The equality identifying `a.hom` with that unit is asserted below.
Source: Stacks Tags 09AB and 03SE; DAG proof step 5.
(blueprint: lem-sfb-radicial-etale-rational-unit-retraction). -/
def rationalTraceRadicialComparison {W T S : Scheme.{u}} (u₀ : W ⟶ T) (e : T ⟶ S)
    (a : 𝟭 _ ≅ upperStar Λ u₀ ⋙ lowerStar Λ u₀)
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    (lowerStar Λ (u₀ ≫ e)).obj ((upperStar Λ (u₀ ≫ e)).obj M) ≅
      (lowerStar Λ e).obj ((upperStar Λ e).obj M) :=
  (lowerStar Λ (u₀ ≫ e)).mapIso ((upperStarComp Λ u₀ e).app M) ≪≫
    (lowerStarComp Λ u₀ e).symm.app _ ≪≫
    (lowerStar Λ e).mapIso (a.symm.app ((upperStar Λ e).obj M))

/-- The canonical exact-functor comparison on a degree-zero pullback.
Source: Stacks Tag 015F, right derivation of an exact functor; DAG proof step 7.
(blueprint: lem-sfb-radicial-etale-rational-unit-retraction). -/
def rationalTraceDerivedComparison {W S : Scheme.{u}} (f : W ⟶ S)
    (h : PreservesFiniteColimits (lowerStar Λ f))
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    (moduleObjectDerivedPushforward Λ f).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ f).obj M)) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((lowerStar Λ f).obj ((upperStar Λ f).obj M)) :=
  letI := h
  (Functor.singleFunctorCompRightDerivedFunctorIso (lowerStar Λ f)).app
    ((upperStar Λ f).obj M)

/-- The actual derived adjunction unit, followed by the canonical identification of
`Lf^*(M[0])` with `f^*M[0]` and its image under `Rf_*`.
Source: localized adjunction unit formula, DAG proof step 7.
(blueprint: lem-sfb-radicial-etale-rational-unit-retraction). -/
def rationalTraceDerivedUnit {W S : Scheme.{u}} (f : W ⟶ S)
    (M : Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :
    (DerivedCategory.singleFunctor _ 0).obj M ⟶
      (moduleObjectDerivedPushforward Λ f).obj
        ((DerivedCategory.singleFunctor _ 0).obj ((upperStar Λ f).obj M)) :=
  (derivedUpperStarLowerStarAdjunction Λ f).unit.app
      ((DerivedCategory.singleFunctor _ 0).obj M) ≫
    (moduleObjectDerivedPushforward Λ f).map
      ((Functor.singleFunctorCompLeftDerivedFunctorIso (upperStar Λ f)).hom.app M)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

open CondensedRing

/-- Exact direct images and the unique natural sum trace, its degree identity, and
its normalized retraction in the ordinary unbounded derived category.

Source: Stacks Tags 03SE (sum trace and degree), 09AB (radicial invariance), and 015F
(exact derived comparison), extended to continuous internal modules by the DAG proof.
(blueprint: lem-sfb-radicial-etale-rational-unit-retraction).

Proof:
1. Cartesian coefficients and pro-etale topological invariance lift the actual radicial
unit and counit to inverse module isomorphisms. Thus u_* is an additive equivalence,
hence exact; this applies to every module, including e^*M.
2. Split e on an etale cover into d sheets (finite-etale local splitting). Etale maps
are weakly etale and their covers are pro-etale covers. The localization and internal
module/section-module equivalences identify coefficient pullback with slice restriction.
Restriction is exact and these restrictions jointly detect zero objects by the sheaf
axiom, so they detect exactness.
3. On a splitting, the disjoint-cover sheaf axiom identifies e_*H with the finite
product of the sheet restrictions. Finite products are biproducts and are exact.
Consequently e_* is exact, and f_* is exact by pushforward composition.
4. Sum the sheet projections. Two splittings differ locally by a permutation; the
sum is invariant. The separated sheaf axiom and gluing give a unique linear natural
trace for e, with no local-freeness assumption on M.
5. Compose with the inverse radicial unit and the canonical composition isomorphisms.
The composite-adjunction unit formula identifies the unit locally with the diagonal,
so trace after unit is d times identity.
6. The field E has characteristic zero, so d is nonzero. Multiplication by d inverse
is continuous on the full norm coefficient sheaf. Its composite with trace retracts
the ordinary unit, regardless of whether ell divides d.
7. Exactness identifies the total right derived functor with termwise pushforward.
Localization of the degreewise adjunction identifies the actual derived unit with
the image of the ordinary unit, using the canonical left and right comparisons.
8. Place the ordinary retraction in degree zero and compose with the comparison.
The composite with the derived unit is identity. For d = 1 the trace is inverse to
the unit, including a nontrivial purely inseparable factor; no field trace is used.
The zero module and empty base satisfy the same formulas. -/
theorem radicial_etale_rational_unit_retraction
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (hpℓ : p ≠ ℓ)
    (k : Type u) [Field k] [CharP k p]
    (E : Type u) [NormedField E] [NormedAlgebra (Padic ℓ) E]
    [FiniteDimensional (Padic ℓ) E]
    (W T S : Over (Spec (.of k)))
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    [LocallyOfFiniteType T.hom] [QuasiCompact T.hom] [IsSeparated T.hom]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    (u₀ : W ⟶ T) (e : T ⟶ S) [IsFinite u₀.left]
    (hu : (topologically IsHomeomorph).universally u₀.left)
    [IsFinite e.left] [Etale e.left] [Surjective e.left]
    (d : ℕ) (hd : 1 ≤ d) (hdegree : ∀ s : S.left, e.left.fiberDegree s = d) :
    (d : E) ≠ 0 ∧
    PreservesFiniteLimits (CondensedRing.lowerStar (normContinuousRing E).X u₀.left) ∧
    PreservesFiniteColimits (CondensedRing.lowerStar (normContinuousRing E).X u₀.left) ∧
    PreservesFiniteLimits (CondensedRing.lowerStar (normContinuousRing E).X e.left) ∧
    PreservesFiniteColimits (CondensedRing.lowerStar (normContinuousRing E).X e.left) ∧
    PreservesFiniteLimits (CondensedRing.lowerStar (normContinuousRing E).X (u₀.left ≫ e.left)) ∧
    ∃ hF : PreservesFiniteColimits
        (CondensedRing.lowerStar (normContinuousRing E).X (u₀.left ≫ e.left)),
    ∃ a : 𝟭 _ ≅ CondensedRing.upperStar (normContinuousRing E).X u₀.left ⋙
        CondensedRing.lowerStar (normContinuousRing E).X u₀.left,
      a.hom = (CondensedRing.upperStarLowerStarAdjunction (normContinuousRing E).X u₀.left).unit ∧
      ∃! t : CondensedRing.upperStar (normContinuousRing E).X (u₀.left ≫ e.left) ⋙
          CondensedRing.lowerStar (normContinuousRing E).X (u₀.left ≫ e.left) ⟶ 𝟭 _,
        (∀ (U : Scheme.{u}) (q : U ⟶ S.left) [Etale q]
          (s : Fin d → (U ⟶ T.left)) (hs : ∀ j, s j ≫ e.left = q),
          IsColimit (Cofan.mk (pullback e.left q)
            (fun j ↦ pullback.lift (s j) (𝟙 U) (by simpa using hs j))) →
          ∀ M : Mod (Sheaf (Scheme.ProEt.topology S.left) Ab.{u + 1})
              (condensedRingObj (normContinuousRing E).X S.left),
            (CondensedRing.upperStar (normContinuousRing E).X q).map (t.app M) =
              (CondensedRing.upperStar (normContinuousRing E).X q).map
                (rationalTraceRadicialComparison (normContinuousRing E).X
                  u₀.left e.left a M).hom ≫
                ∑ j : Fin d, rationalTraceSheetProjection (normContinuousRing E).X
                  e.left q (s j) (hs j) M ∧
            ∀ j : Fin d,
              (CondensedRing.upperStar (normContinuousRing E).X q).map
                  ((CondensedRing.upperStarLowerStarAdjunction (normContinuousRing E).X
                    (u₀.left ≫ e.left)).unit.app M) ≫
                (CondensedRing.upperStar (normContinuousRing E).X q).map
                  (rationalTraceRadicialComparison (normContinuousRing E).X
                    u₀.left e.left a M).hom ≫
                rationalTraceSheetProjection (normContinuousRing E).X
                  e.left q (s j) (hs j) M = 𝟙 _) ∧
        (∀ M : Mod (Sheaf (Scheme.ProEt.topology S.left) Ab.{u + 1})
            (condensedRingObj (normContinuousRing E).X S.left),
          (CondensedRing.upperStarLowerStarAdjunction (normContinuousRing E).X
              (u₀.left ≫ e.left)).unit.app M ≫ t.app M = d • 𝟙 M) ∧
        (d = 1 → ∀ M : Mod (Sheaf (Scheme.ProEt.topology S.left) Ab.{u + 1})
            (condensedRingObj (normContinuousRing E).X S.left),
          t.app M ≫ (CondensedRing.upperStarLowerStarAdjunction (normContinuousRing E).X
            (u₀.left ≫ e.left)).unit.app M = 𝟙 _) ∧
        ∀ M : Mod (Sheaf (Scheme.ProEt.topology S.left) Ab.{u + 1})
            (condensedRingObj (normContinuousRing E).X S.left),
          rationalTraceDerivedUnit (normContinuousRing E).X (u₀.left ≫ e.left) M ≫
              (rationalTraceDerivedComparison (normContinuousRing E).X
                (u₀.left ≫ e.left) hF M).hom =
            (DerivedCategory.singleFunctor _ 0).map
              ((CondensedRing.upperStarLowerStarAdjunction (normContinuousRing E).X
                (u₀.left ≫ e.left)).unit.app M) ∧
          ∃ r : (CondensedRing.lowerStar (normContinuousRing E).X (u₀.left ≫ e.left)).obj
              ((CondensedRing.upperStar (normContinuousRing E).X (u₀.left ≫ e.left)).obj M) ⟶ M,
            r.hom = (t.app M).hom ≫ normContinuousScalar S.left (d : E)⁻¹ M ∧
            (CondensedRing.upperStarLowerStarAdjunction (normContinuousRing E).X
              (u₀.left ≫ e.left)).unit.app M ≫ r = 𝟙 M ∧
            rationalTraceDerivedUnit (normContinuousRing E).X (u₀.left ≫ e.left) M ≫
                (rationalTraceDerivedComparison (normContinuousRing E).X
                  (u₀.left ≫ e.left) hF M).hom ≫
                (DerivedCategory.singleFunctor _ 0).map r = 𝟙 _ := by
  sorry

end AlgebraicGeometry.ProEtale
