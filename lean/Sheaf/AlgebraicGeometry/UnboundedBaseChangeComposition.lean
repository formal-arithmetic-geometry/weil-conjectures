/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import Sheaf.AlgebraicGeometry.DerivedSquareIsoPasting
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Base change for a composite square on unbounded derived categories

Source: Stacks Project, Tag 0EZS, lemma-base-change-compose, and Tag 0E47
(blueprint: sbc-lem-base-change-composition).

Abelian sheaves are encoded as sheaves of modules over `ULift ℤ`, canonically equivalent
to abelian groups in the coefficient universe. No boundedness or torsion is assumed.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Source: Stacks Project, Tag 0EZS (blueprint: sbc-lem-base-change-composition).
For the tower of Cartesian squares, invertibility of the two exchange components implies
invertibility for the outer rectangle, on the full unbounded derived category.

Proof: Paste the Cartesian squares. The inverse-image composition comparisons identify the
outer square comparison with the pasted comparisons. This equality holds termwise on
complexes and descends through localization, since inverse image is exact. Mate pasting and
mate whiskering identify the outer exchange with inverse image of the lower exchange,
followed by the upper exchange and the canonical composition isomorphisms on both ends.
Functors preserve inverses, so every factor is invertible and so is their composite. -/
theorem isIso_derivedBaseChangeMap_app_of_cartesian_tower
    {W Z X Y S T : Scheme.{u}} {j : Z ⟶ W} {k : Z ⟶ Y} {i : W ⟶ X}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (lower : ChosenCartesianSquare h e f g) (upper : ChosenCartesianSquare j k i h)
    (K : DerivedCategoryModule (ULift.{u + 1} ℤ) T)
    (hLower : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      lower.toCommSq.flip).app K))
    (hUpper : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      upper.toCommSq.flip).app
        ((L((e)^*[ModuleCat.{u + 1} (ULift.{u + 1} ℤ)])).obj K))) :
    IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      (upper.toCommSq.flip.horiz_comp lower.toCommSq.flip)).app K) := by
  sorry

/-- Source: Stacks Project, Tag 0EZS (blueprint: sbc-lem-base-change-composition).
The independent degreewise assertion for an abelian sheaf and a single nonnegative degree.
The degreewise maps are cohomology of the unbounded exchange on sheaves in degree zero,
as in sbc-def-base-change-map; no invertibility in any other degree is assumed.

Proof: Apply degree-q cohomology to the mate-pasting equality from the preceding argument.
Exact inverse image preserves kernels, images and their quotient, hence commutes naturally
with cohomology, also on derived roofs. The single-complex comparison identifies pullback
of F[0] with (e inverse-image F)[0]. The two middle factors are therefore inverse image of
the lower degree-q map and the upper degree-q map. The outside factors are cohomology of
composition isomorphisms. All four are invertible under the two stated degree-q hypotheses;
the reverse product of their inverses is the inverse of the outer degree-q map. -/
theorem isIso_homology_derivedBaseChangeMap_of_cartesian_tower
    {W Z X Y S T : Scheme.{u}} {j : Z ⟶ W} {k : Z ⟶ Y} {i : W ⟶ X}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (lower : ChosenCartesianSquare h e f g) (upper : ChosenCartesianSquare j k i h)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) (q : ℕ)
    (hLower : IsIso ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).map
      ((derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
        lower.toCommSq.flip).app ((_root_.DerivedCategory.singleFunctor _ 0).obj F))))
    (hUpper : IsIso ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).map
      ((derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
        upper.toCommSq.flip).app ((_root_.DerivedCategory.singleFunctor _ 0).obj
          ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) e).obj F))))) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ (q : ℤ)).map
      ((derivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
        (upper.toCommSq.flip.horiz_comp lower.toCommSq.flip)).app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) := by
  sorry

end AlgebraicGeometry.Etale
