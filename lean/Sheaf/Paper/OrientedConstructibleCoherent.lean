/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.Paper.OrientedConstructibleSheaf
public import Sheaf.Paper.OrientedNearbyCycles
public import Sheaf.CategoryTheory.Sites.CoherentTopos
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Types.Colimits
import Sheaf.Paper.CoherentSetCriterion
import Sheaf.Paper.OrientedConstructibleSheafVanishing

/-!
# Constructibility and coherence on a vanishing topos

Source: Orgogozo, Modifications et cycles proches sur une base générale,
author draft §8.1, printed pp. 17--18
(blueprint: lem-trf-oriented-constructible-coherent).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.OrientedConstructibleSheaf

namespace AlgebraicGeometry

/-- Standard coproducts of set-valued sheaves on the recorded oriented-product site.
This directly supplies Mathlib's sheafified-presheaf colimits and its sheafification
adjunction, avoiding a recursive search for that adjunction through forgetful functors.
No new colimit construction or mathematical assumption is introduced.
Source: Orgogozo, author draft §8.1, small-site presentation
(blueprint: lem-trf-oriented-constructible-coherent). -/
instance orientedProductSetSheaves_hasCoproducts
    {X Y S : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) :
    HasCoproducts.{max (u + 1) v}
      (Sheaf (productTopology.{u, v} a b) (Type (max (u + 1) v))) :=
  fun _ ↦ @Sheaf.instHasColimitsOfShape _ _ _ _ _ _ _
    HasSheafify.isRightAdjoint inferInstance

/-- Finite-coefficient constructibility on the vanishing topos is equivalent to coherence
of the underlying sheaf of sets. The oriented-product presentation with second map `𝟙 S`
is the vanishing topos, as in the recorded constructibility definition.
Source: Orgogozo, author draft §8.1, printed pp. 17--18
(blueprint: lem-trf-oriented-constructible-coherent).

Proof:
1. Apply `lem-trf-coherent-set-criterion` to the underlying sheaf of sets: coherence is
   equivalent to finite constructible stratifications with finite locally constant values.
2. A finite constant module trivialization gives such a finite constant set trivialization:
   inverse image and constant sheafification commute with forgetting module operations
   (`def-trf-oriented-nearby-cycles`, `def-trf-oriented-constructible-sheaf`).
3. Conversely, on each constant finite-set chart, decompose its covering object into the
   finitely many pieces on which addition, zero, and every scalar operation are constant.
   There are finitely many operations because the coefficient ring is finite. On a
   noninitial piece, equality of constant maps detects equality of the set maps, since
   different summands of a constant finite sheaf are disjoint. Thus the module axioms
   give a finite module structure on the constant set on each piece. Discard initial
   pieces (or use any module there). The refined charts still cover and supply exactly
   `def-trf-oriented-constructible-sheaf`, on the same finite constructible strata. -/
theorem orientedConstructible_iff_coherent
    {X S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (Λ : Type v) [CommRing Λ] [Finite Λ]
    (F : Modules.{u, v} f (𝟙 S) Λ) :
    IsConstructible f (𝟙 S) Λ F ↔
      IsCoherentObject.{max (u + 1) v}
        ((sheafCompose (productTopology.{u, v} f (𝟙 S))
          (forget AddCommGrpCat.{max (u + 1) v})).obj
          ((SheafOfModules.toSheaf _).obj F)) := by
  sorry

end AlgebraicGeometry
