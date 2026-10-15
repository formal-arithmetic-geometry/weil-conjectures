/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Algebra.Homology.ExactSequence

import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Sheaf.AlgebraicGeometry.WContractibleAffineEvaluation
import Sheaf.RingTheory.BoundedWContractibleExtension
import Sheaf.RingTheory.WContractibleClosedLocalization
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.AlgebraicGeometry.ProEtaleShriekSpecializationZero
import Sheaf.AlgebraicGeometry.ProEtaleSpecializationRestrictionSections
import Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageUnderlying
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.CategoryTheory.RingedSiteModules

/-! Ringed pro-etale localization: a geometric step of the open-closed argument. -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The actual counit and unit form the open-closed short exact sequence with
arbitrary module coefficients. This is the local geometric step, without the
formal exactness consequences or the filtered-colimit assertion.

Source: Stacks Project, Tag 09AH, with Tags 0983/0984, 098H, 09AC and 09AG
(blueprint: lem-weil-pbc-proetale-ringed-localization-sequence).

Proof: Refine affine pro-etale objects by bounded w-contractible affine covers.
Write a refined object as `Spec R`, its closed fibre as `Spec (R/I)`. The
quasi-compactness of the complementary open selects finitely many elements of `I`
whose distinguished opens cover that complement. The closed-localization covering
then consists of those distinguished opens and the localization of `R` at elements
invertible modulo `I`. On the open pieces, restriction identifies the counit with
an isomorphism and the closed term with zero. On the localization piece every point
specializes into the closed fibre. The shriek-specialization-zero theorem makes
the shriek source zero, and specialization-restriction identifies the closed unit
with an isomorphism. These identifications concern the actual adjunction maps.
All refinements stay in the same universe: the bounded extension is small, and
localizations are quotients of subsets of the square of its underlying set.
The covering transitivity axiom combines these refinements. Locally the sequence
is therefore a two-term identity sequence with a zero term. Its composite vanishes,
its first map is monic, its last map is epic, and its kernel equals its image.
These assertions descend by the sheaf condition and local lifting of sections.
The unit and counit are linear by the action naturality, so the same exactness holds
for module sheaves. Changing either adjunction changes the end maps only by
isomorphisms of their source or target, preserving all these assertions. -/
theorem proEtale_ringed_localization_sequence {X Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (U : X.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (ai : proEtaleModuleInverseImage i A ⊣
      (SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange i)
      (J := ProEt.topology X) (K := ProEt.topology Z)
      (S := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) (R := ((sheafCompose (ProEt.topology Z)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj A)))
      ⟨Functor.whiskerRight
        ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).unit.app A).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩))
    (aj : (SheafOfModules.extensionByZeroPresheaf.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A) U ⋙
      PresheafOfModules.sheafification (𝟙 ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).obj)) ⊣
      SheafOfModules.overFunctor.{u + 1} ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A) U) :
    ∀ M, Mono (aj.counit.app M) ∧ Epi (ai.unit.app M) ∧
      (ComposableArrows.mk₂ (aj.counit.app M) (ai.unit.app M)).Exact := by
  sorry

end AlgebraicGeometry.Scheme
