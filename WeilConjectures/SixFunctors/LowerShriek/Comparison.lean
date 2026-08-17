/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.SixFunctors.LowerShriek.Etale
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.FullyFaithful
public import WeilConjectures.SixFunctors.UpperLowerStar.Etale

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
(`Etale.isIso_lowerShriekToLowerStar`): the open immersion `i` into a compactification of a
proper morphism is also proper, hence a closed immersion, so its range is clopen; and
extension by zero along an open immersion with clopen range agrees with the pushforward.

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriekToLowerStar`: the canonical map
  `i_! ⟶ i_*` for an open immersion `i`.
- `AlgebraicGeometry.Etale.lowerShriekToLowerStar`: the canonical comparison
  `ι_f : f_! ⟶ f_*` for `f` admitting a compactification.

## Main results

- `AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekToLowerStar`: for an open immersion
  with clopen range the comparison `i_! ⟶ i_*` is an isomorphism.
- `AlgebraicGeometry.Etale.isIso_openImmersionRestriction_map_lowerShriekToLowerStar`: the
  restriction `i^*` of the comparison is an isomorphism, for *any* open immersion `i`. This
  is one of the two halves of the statement above.
- `AlgebraicGeometry.Etale.isIso_lowerShriekToLowerStar_of_isIso`: the formal reduction of
  the comparison for `f` to the comparison for the open immersion of its compactification.
- `AlgebraicGeometry.Etale.isIso_lowerShriekToLowerStar`: for proper `f`, the comparison
  `ι_f` is an isomorphism.

## Remaining `sorry`

`Etale.isIso_openImmersionLowerShriekToLowerStar` — the clopen-immersion case — is the one
statement in this file that is still `sorry`ed; everything else, including the reduction of
the proper case to it and the geometric input that `i` has clopen range, is proved. Its
docstring records the intended argument and why `HasZeroObject A` is a necessary hypothesis.

Half of it is now proved. Writing `k` for the open immersion complementary to the clopen
`i`, the pair `{i, k}` is jointly surjective, so it suffices to prove that `i^*` and `k^*` of
the comparison are isomorphisms.

- `i^*` of the comparison is `Etale.isIso_openImmersionRestriction_map_lowerShriekToLowerStar`
  above, which needs no clopen hypothesis: it comes from `i_!` being fully faithful along an
  open immersion (`WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.FullyFaithful`).
- `k^*` of the comparison is what remains. There the source is initial and the target is
  terminal — `k^* i_* F` has sections `F(T ×_X U) = F(∅)`, terminal by the sheaf condition
  for the empty covering of the empty scheme, and `k^* i_! F` is initial because
  `Hom(k^* i_! F, H) ≅ Hom(i_! F, k_* H) ≅ Hom(F, i^* k_* H)` by the two adjunctions with
  `i^* k_* H` terminal for the same reason. This never computes sections of `i_! F`, which
  matters because `i_!` is a sheafification. With `HasZeroObject A` initial and terminal
  agree, which is exactly where that hypothesis is used.

-/

@[expose] public section

universe w v' u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{v'} A]

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

variable [HasInitial A] [HasWeakSheafify X.smallEtaleTopology A]

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

/-- For an open immersion `j` with **clopen** range — equivalently, an open immersion that
is also a closed immersion — the comparison `j_! ⟶ j_*` is an isomorphism.

Write `X = U ⊔ W` for the decomposition of `X` into the range of `j` and its complement.
Every `V : X.Etale` decomposes accordingly as `V = V_U ⊔ V_W` with `V_U = V ×_X U`, and this
is a covering of `V` in the small étale topology, so for a sheaf the sections over `V` are
the product of the sections over the two pieces. Now `(j_* F)(V) = F(V_U)`, while `j_! F` is
the sheafification of the presheaf that is `F` on the objects admitting a lift through `j`
and initial elsewhere; the two pieces of the decomposition of `V` give `F(V_U)` and the
sections of the initial sheaf over `V_W`, so `j_! F` and `j_* F` agree as soon as the
initial object of `A` is also terminal.

The hypothesis `HasZeroObject A` is genuinely needed, and not an artefact of the proof: for
`A = Type` and `j` a clopen immersion with nonempty complement `W`, `(j_* F)(W) = F(∅)` is a
singleton while `(j_! F)(W)` is empty, since every étale cover of the nonempty `W` has a
piece with no lift through `j`. So the comparison is not an isomorphism there. -/
theorem Etale.isIso_openImmersionLowerShriekToLowerStar [HasZeroObject A]
    (hj : IsClopen (Set.range j)) :
    IsIso (Etale.openImmersionLowerShriekToLowerStar A j) :=
  sorry

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
`j_!` is fully faithful along an open immersion.

This discharges the `j^*` half of
`Etale.isIso_openImmersionLowerShriekToLowerStar`; the remaining half is the restriction
along the complementary open immersion, which is where the clopen hypothesis and
`HasZeroObject A` are consumed. -/
instance Etale.isIso_openImmersionRestriction_map_lowerShriekToLowerStar
    (F : Sheaf U.smallEtaleTopology A) :
    IsIso ((Etale.openImmersionRestriction A j).map
      ((Etale.openImmersionLowerShriekToLowerStar A j).app F)) := by
  rw [Etale.openImmersionLowerShriekToLowerStar_app, Functor.map_comp]
  infer_instance

end OpenImmersion

section Comparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
variable [HasInitial A] [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology A]

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
clopen range (`AlgebraicGeometry.Compactification.isClopen_range_openImmersion`). An open
immersion with clopen range satisfies `i_! ≅ i_*`
(`AlgebraicGeometry.Etale.isIso_openImmersionLowerShriekToLowerStar`), and the induced
comparison of the composites is then an isomorphism by
`AlgebraicGeometry.Etale.isIso_lowerShriekToLowerStar_of_isIso`. -/
theorem Etale.isIso_lowerShriekToLowerStar [IsProper f] [HasZeroObject A] :
    IsIso (Etale.lowerShriekToLowerStar A f) :=
  Etale.isIso_lowerShriekToLowerStar_of_isIso A f
    (Etale.isIso_openImmersionLowerShriekToLowerStar A _
      ((HasCompactification.compactification f).isClopen_range_openImmersion ‹IsProper f›))

end Comparison

end AlgebraicGeometry
