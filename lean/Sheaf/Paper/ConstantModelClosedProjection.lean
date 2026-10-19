/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom

/-!
# Unbounded closed projection formula for condensed coefficients

Source: blueprint main-20261015, sk-lem-integral-models-operations,
parent proof step 10 (blueprint: lem-sfb-constant-model-closed-projection).
-/

@[expose] public section

set_option autoImplicit false

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Mod.extendScalars
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
  AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek


universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The closed projection formula for arbitrary unbounded derived objects.
Source: integral-models-operations proof paragraph (4), parent step 10;
Stacks Tags 09AA, 09BM, 09AH and the projection map Tag 0B56
(blueprint: lem-sfb-constant-model-closed-projection).

Proof: take the complementary open immersion and use the closed projection clause
of openClosedInternalHomFormulas. It supplies the formula for the exact termwise
closed direct image and support pullback. Transport the left tensor factor through
the isomorphism from total right derived direct image to exact termwise direct image.
Transport the right tensor factor through the derived comparison from support
pullback to upperStar. Finally transport exact direct image back to its total right
derived functor. The composite is the required isomorphism. No boundedness or
constructibility is used; zero objects and empty closed loci are included. -/
theorem constantModel_closed_projection
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {Z X : Scheme.{u}}
    [IsNoetherian Z] [IsNoetherian X] (i : Z ⟶ X) [IsClosedImmersion i]
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj Λ Z)))
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    Nonempty ((((derivedTensor Λ X).obj
      ((lowerStar Λ i).rightDerivedFunctor.obj L)).obj M) ≅
      (lowerStar Λ i).rightDerivedFunctor.obj
        (((derivedTensor Λ Z).obj L).obj ((upperStar Λ i).mapDerivedCategory.obj M))) :=
  by
    let V : X.Opens :=
      ⟨(Set.range i)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    obtain ⟨p, _⟩ := openClosedInternalHomFormulas Λ i V.ι (by simp [V])
    let es := (Functor.mapDerivedCategoryNatIso (supportPullbackIsoUpperStar Λ i)).app M
    exact ⟨((derivedTensor Λ X).mapIso
      ((lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory.app L)).app M ≪≫
      p L M ≪≫
      (lowerStar Λ i).mapDerivedCategory.mapIso
        (((derivedTensor Λ Z).obj L).mapIso es) ≪≫
      ((lowerStar Λ i).rightDerivedFunctorIsoMapDerivedCategory.app _).symm⟩

end AlgebraicGeometry.ProEtale.CondensedRing
