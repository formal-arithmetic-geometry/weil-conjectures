/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.LowerShriek.Etale
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.FullyFaithful

/-!

# The canonical comparison `f_! ⟶ f_*`

For a morphism `f : X ⟶ Y` admitting a compactification `X --i--> Z --g--> Y`, this file
constructs the canonical natural transformation

`ι_f : f_! ⟶ f_*`

from the lower shriek to the pushforward on étale sheaves.

The construction proceeds through the adjoint triple `i_! ⊣ i^* ⊣ i_*` of the open
immersion `i`:

- Since `i` is a monomorphism, the localization functor `MorphismProperty.Over.map` of
  the small étale sites along `i` is fully faithful
  (`CategoryTheory.MorphismProperty.Over.full_map`), so the unit of the site-level
  adjunction `MorphismProperty.Over.mapPullbackAdj` is an isomorphism, and hence so is
  the counit of the induced sheaf-level adjunction `i^* ⊣ i_*`
  (`CategoryTheory.Adjunction.isIso_sheafPushforwardContinuous_counit`); this expresses
  that the restriction of a pushforward along an open immersion is the original sheaf.
- Inverting this counit and contracting with the counit of `i_! ⊣ i^*` yields the
  canonical map `i_! ⟶ i_*` (`Etale.openImmersionLowerShriekToLowerStar`).
- Pushing forward along `g` and composing with the composition isomorphism
  `Etale.lowerStarComp` gives `ι_f : f_! = g_* ∘ i_! ⟶ g_* ∘ i_* ≅ f_*`
  (`Etale.lowerShriekToLowerStar`).

For a proper morphism `f`, the comparison `ι_f` is an isomorphism
(`Etale.isIso_lowerShriekToLowerStar`); this is the sorried statement of the file, see the
"Remaining `sorry`" section below.

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriekToLowerStar`: the canonical map
  `i_! ⟶ i_*` for an open immersion `i`.
- `AlgebraicGeometry.Etale.lowerShriekToLowerStar`: the canonical comparison
  `ι_f : f_! ⟶ f_*` for `f` admitting a compactification.

## Main results

- `AlgebraicGeometry.Etale.isIso_openImmersionRestriction_map_lowerShriekToLowerStar`: the
  restriction `i^*` of the comparison is an isomorphism, for *any* open immersion `i`.
- `AlgebraicGeometry.Etale.isIso_lowerShriekToLowerStar_of_isIso`: the formal reduction of
  the comparison for `f` to the comparison for the open immersion of its compactification.
- `AlgebraicGeometry.Etale.isIso_lowerShriekToLowerStar`: for proper `f`, the comparison
  `ι_f` is an isomorphism.

## Remaining `sorry`

`Etale.isIso_lowerShriekToLowerStar` — the comparison for a proper `f` — is the one
statement in this file that is still `sorry`ed. By the proved
`Etale.isIso_lowerShriekToLowerStar_of_isIso` it reduces to the comparison `i_! ⟶ i_*` for
the open immersion `i` of a compactification of `f`, whose range is clopen since `f` is
proper (`AlgebraicGeometry.Compactification.isClopen_range_openImmersion`). The `i^*`
restriction of that comparison is proved to be invertible below
(`Etale.isIso_openImmersionRestriction_map_lowerShriekToLowerStar`); the remaining
mathematical content is that both sides of the comparison vanish on the complement of the
range of `i`, which is where the clopen hypothesis and `HasZeroObject A` enter. The
site-theoretic input for this is available in
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleClopen`
(`Scheme.Etale.isLimitClopenFan` and `Scheme.Etale.isTerminalSectionsOfIsEmpty`), and the
vanishing of both sides on the complement is proved in
`WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Complement`, which imports this
module.

-/

@[expose] public section

universe w u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u} A] [Abelian A] [IsGrothendieckAbelian.{u} A]

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The canonical natural transformation `i_! ⟶ i_*` from the extension by zero to the
pushforward along an open immersion, obtained from the adjoint triple `i_! ⊣ i^* ⊣ i_*`:
insert the inverse of the counit of `i^* ⊣ i_*` and contract with the counit of
`i_! ⊣ i^*`. -/
noncomputable def Etale.openImmersionLowerShriekToLowerStar :
    Etale.openImmersionLowerShriek A j ⟶ Etale.lowerStar A j :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (inv (Etale.openImmersionRestrictionLowerStarAdjunction A j).counit)
      (Etale.openImmersionLowerShriek A j) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (Etale.lowerStar A j)
      (Etale.openImmersionLowerShriekAdjunction A j).counit ≫
    (Functor.rightUnitor _).hom

set_option backward.isDefEq.respectTransparency false in
/-- The components of the comparison `j_! ⟶ j_*`: the unitors and the associator in its
definition are identities, so at `F` it is `j_!` of the inverted counit of `j^* ⊣ j_*`,
followed by the counit of `j_! ⊣ j^*` at `j_* F`. -/
lemma Etale.openImmersionLowerShriekToLowerStar_app (F : Sheaf U.smallEtaleTopology A) :
    (Etale.openImmersionLowerShriekToLowerStar A j).app F =
      (Etale.openImmersionLowerShriek A j).map
          ((inv (Etale.openImmersionRestrictionLowerStarAdjunction A j).counit).app F) ≫
        (Etale.openImmersionLowerShriekAdjunction A j).counit.app
          ((Etale.lowerStar A j).obj F) := by
  simp only [Etale.openImmersionLowerShriekToLowerStar, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.id_obj,
    NatIso.isIso_inv_app, Functor.map_inv, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, id_comp, IsIso.eq_inv_comp, IsIso.hom_inv_id_assoc]
  exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
/-- **`j^*` of the comparison `j_! ⟶ j_*` is an isomorphism**, for any open immersion `j`
and with no hypothesis on the range of `j`.

Both factors of `Etale.openImmersionLowerShriekToLowerStar_app` become invertible after
applying `j^*`: the first is `j_!` of an isomorphism, and the second is
`Etale.isIso_openImmersionRestriction_map_lowerShriekAdjunction_counit`, which holds because
`j_!` is fully faithful along an open immersion. -/
instance Etale.isIso_openImmersionRestriction_map_lowerShriekToLowerStar
    (F : Sheaf U.smallEtaleTopology A) :
    IsIso ((Etale.openImmersionRestriction A j).map
      ((Etale.openImmersionLowerShriekToLowerStar A j).app F)) := by
  rw [Etale.openImmersionLowerShriekToLowerStar_app, Functor.map_comp]
  infer_instance

end OpenImmersion

section Comparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

/-- The canonical comparison `ι_f : f_! ⟶ f_*` from the lower shriek to the pushforward
along a morphism `f` admitting a compactification `X --i--> Z --g--> Y`: it is induced by
the canonical map `i_! ⟶ i_*` for the open immersion `i`, using `f_! = g_* ∘ i_!` and the
composition isomorphism `g_* ∘ i_* ≅ (i ≫ g)_* = f_*`. -/
noncomputable def Etale.lowerShriekToLowerStar :
    Etale.lowerShriek A f ⟶ Etale.lowerStar A f :=
  Functor.whiskerRight
      (Etale.openImmersionLowerShriekToLowerStar A (HasCompactification.compactification f).i)
      (Etale.lowerStar A (HasCompactification.compactification f).g) ≫
    (Etale.lowerStarComp A (HasCompactification.compactification f).i
      (HasCompactification.compactification f).g).hom ≫
    eqToHom (by rw [← (HasCompactification.compactification f).comm])

/-- The comparison `ι_f` is an isomorphism as soon as the comparison for the open immersion
`i` of the chosen compactification is: the remaining two factors of `ι_f` are an isomorphism
and an `eqToHom` by construction, and whiskering preserves isomorphisms.

This step is purely formal; it uses nothing about `f`. -/
lemma Etale.isIso_lowerShriekToLowerStar_of_isIso
    (h : IsIso (Etale.openImmersionLowerShriekToLowerStar A
      (HasCompactification.compactification f).i)) :
    IsIso (Etale.lowerShriekToLowerStar A f) := by
  rw [Etale.lowerShriekToLowerStar]
  infer_instance

/-- For a **proper** morphism `f`, the canonical comparison `ι_f : f_! ⟶ f_*` is an
isomorphism.

Since `f` is proper and the structure morphism `g` of the compactification is separated, the
open immersion `i` is proper as well
(`AlgebraicGeometry.Compactification.isProper_openImmersion`), hence a closed immersion with
clopen range (`AlgebraicGeometry.Compactification.isClopen_range_openImmersion`). By
`AlgebraicGeometry.Etale.isIso_lowerShriekToLowerStar_of_isIso` the statement reduces to
`i_! ≅ i_*` for the open immersion `i` with clopen range; see the "Remaining `sorry`"
section of the module docstring for the status of that input. -/
theorem Etale.isIso_lowerShriekToLowerStar [IsProper f] :
    IsIso (Etale.lowerShriekToLowerStar A f) :=
  sorry

end Comparison

end AlgebraicGeometry
