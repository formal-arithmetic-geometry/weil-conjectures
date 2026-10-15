/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.StrictHenselizationFunctoriality
public import Sheaf.Paper.StrictHenselizationPointEvaluation
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
import Sheaf.Paper.KunBcMapOnCohomology
import Sheaf.Paper.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.StrictHenselizationRestriction
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization
import WeilConjectures.SixFunctors.BaseChange.Square

/-! # Testing exchange on strict-local cohomology

Source: Stacks Project, Tag 0EZU, lemma-base-change-f-star-general-stalks
(blueprint: lem-weil-pbc-exchange-strict-local-cohomology).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The degree-q exchange is invertible exactly when its strict-local cohomology
pullbacks are bijective. The ring map `a` is specified by its structural and geometric-point
compatibilities: these characterize the canonical map of strict henselizations. Thus
quantifying over such `a` does not choose an arbitrary map over the base. The target of
`cohomologyMap` uses the iterated inverse image of `F`, canonically identified with its
inverse image under the projection to `T`.

Source: Stacks Project, Tag 0EZU, lemma-base-change-f-star-general-stalks
(blueprint: lem-weil-pbc-exchange-strict-local-cohomology).

Proof:
1. Base change preserves quasi-compactness and quasi-separatedness, so the projection
from `X ×_S T` to `X` is qcqs. Strict-henselization functoriality gives the specified map `a`.
The universal property identifies its strict-local base change with the displayed product.
2. The inverse-image stalk comparison and the unrestricted strict-henselization stalk
formula identify the two stalks of exchange with the two displayed cohomology groups.
The comparisons are the canonical strict-henselization restrictions; no torsion is needed.
3. Represent a stalk class on an affine pointed etale neighbourhood. Refine its pullback
by an affine neighbourhood of the lifted geometric point. The injective-resolution formula
for higher exchange, the underived exchange formula, and the cohomology-pullback recipe
identify the resulting map on representatives with pullback of cohomology classes.
4. The canonical strict-local restrictions send these same representatives to pullbacks
along the limit legs. Compatibility of the functorial strict-local map with neighbourhoods
and functoriality of cohomology pullback show that this identification commutes with
exchange. Thus its stalk map is conjugate to the stated cohomology pullback.
5. The comparisons are invertible, so exchange is invertible on every geometric stalk
exactly when these pullbacks are. Geometric stalks jointly reflect isomorphisms of sheaves
of sets; the sectionwise inverses are additive and natural, hence give an inverse of
abelian sheaves. This also applies when `X` is empty. -/
theorem isIso_exchange_iff_strictLocalCohomology
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact g] [QuasiSeparated g]
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (IsPullback.of_hasPullback f g).toCommSq.flip).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ↔
    ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)
      (a : Scheme.strictHenselizationRing (x ≫ f) ⟶ Scheme.strictHenselizationRing x)
      (_ : Scheme.strictHenselizationPointEvaluation (x ≫ f) =
        (Scheme.strictHenselizationPointEvaluation x).comp a.hom)
      (ha : Spec.map a ≫ Scheme.strictHenselizationStructuralMap (x ≫ f) =
        Scheme.strictHenselizationStructuralMap x ≫ f),
      Function.Bijective (cohomologyMap
        (pullback.map (Scheme.strictHenselizationStructuralMap x ≫ f) g
          (Scheme.strictHenselizationStructuralMap (x ≫ f)) g
          (Spec.map a) (𝟙 T) (𝟙 S)
          ((Category.comp_id _).trans ha.symm)
          ((Category.comp_id g).trans (Category.id_comp g).symm))
        ((upperStar AddCommGrpCat.{u + 1}
          (pullback.snd (Scheme.strictHenselizationStructuralMap (x ≫ f)) g)).obj F) q) := by
  sorry

end AlgebraicGeometry.Etale
