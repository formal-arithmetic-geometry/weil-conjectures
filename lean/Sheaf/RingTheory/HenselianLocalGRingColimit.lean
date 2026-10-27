module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.RingTheory.GRing
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

import WeilConjectures.RingTheory.LocalRingColimitEssentiallyFiniteType
import Mathlib.RingTheory.EssentialFiniteness
import WeilConjectures.RingTheory.FiniteTypeIntGRing
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.RingTheory.AdicCompletionRingEquiv
import WeilConjectures.RingTheory.RegularRingEquiv
import WeilConjectures.RingTheory.GRingEquiv
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import WeilConjectures.RingTheory.PairHenselization
import WeilConjectures.RingTheory.HenselianFactorizationCriterion
import WeilConjectures.RingTheory.HenselizationPairGRing
import WeilConjectures.RingTheory.HenselizationColimit

/-!
# Henselian local rings as directed colimits of henselian local G-rings

Source: Stacks Project, More on Algebra, Tag 0A41,
`lemma-henselian-local-limit-G-rings`.
(blueprint: lem-sfb-henselian-local-g-ring-colimit)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CommRingCat

/-- Every commutative henselian local ring is a directed colimit of commutative henselian
local Noetherian G-rings, with local transition maps and local cocone maps. Here
`IsLocalHom` is equivalent to the inverse image of the target maximal ideal being the
source maximal ideal (`IsLocalRing.local_hom_TFAE`); injectivity is not asserted.

Source: Stacks Project, More on Algebra, Tag 0A41,
`lemma-henselian-local-limit-G-rings`.
(blueprint: lem-sfb-henselian-local-g-ring-colimit)

Proof:
1. Apply `lem-weil-pbc-local-ring-colimit-essentially-finite-type-over-z` to `C`.
   This gives a small nonempty directed system of local rings `R_i` essentially of finite
   type over the integers, local transition maps, and local cocone maps to `C`, which is
   their colimit (`def-weil-pbc-category-colimit`).
2. By `def-weil-pbc-essentially-finite-type-algebra`, write each `R_i` as a localization
   of a finite type integer algebra `B_i`. The latter is a Noetherian G-ring by
   `lem-weil-pbc-finite-type-z-g-ring` and `def-weil-pbc-g-ring`. Its localization is
   Noetherian by `lem-weil-pbc-localization-noetherian`.
3. For a prime `q` of that localization and its contracted prime `p` of `B_i`, the
   iterated localization is canonically `B_i` localized at `p`
   (`def-weil-pbc-localization-at-prime`). On fractions the mutually inverse maps are
   `(b/w)/(c/v) ↦ bv/(wc)` and `b/c ↦ (b/1)/(c/1)`. Their existence and uniqueness
   follow from `lem-weil-pbc-ring-localization-universal-property`. They identify
   maximal ideals because a fraction lies in `q` exactly when its numerator lies in `p`.
4. Use `lem-weil-pbc-adic-completion-ring-equiv` on these local isomorphisms, then
   `lem-weil-pbc-regular-ring-map-ring-equiv`, to transport regularity of the local
   completion maps. Thus each localization is a G-ring; transport back to `R_i` by
   `lem-weil-pbc-g-ring-ring-equiv`.
5. By `lem-pc-filtered-colimit-commrings-elementwise`, every element of `C` has a stage
   representative. Localness, or the unit criterion of
   `lem-weil-pbc-local-ring-unit-criterion`, shows that such an element is in the maximal
   ideal of `C` exactly when its representative is in the stage maximal ideal. Thus the
   maximal ideal of `C` is the colimit ideal of these maximal ideals.
6. Apply `lem-weil-pbc-pair-henselization` to each maximal-ideal pair. Its extended ideal
   has field quotient; `lem-weil-pbc-henselian-factorization-criterion` places it in the
   Jacobson radical, so it is the unique maximal ideal. The stages are henselian local
   (`def-weil-pbc-henselian-terminology`). By `lem-weil-pbc-henselization-pair-g-ring`
   they are G-rings, in particular Noetherian.
7. Apply `lem-weil-pbc-henselization-colimit`: the induced transition maps satisfy
   identity and composition, and its henselian specialization gives compatible maps
   to `C` exhibiting `C` as their colimit, since the colimit pair in step 5 is henselian.
8. These maps preserve maximal ideals. An element outside a source maximal ideal is
   a unit, whose image is a unit, by `lem-weil-pbc-local-ring-unit-criterion`.
   Hence each inverse image of a target maximal ideal is exactly the source maximal
   ideal. No injectivity of any henselized map is used. -/
theorem exists_henselianLocal_isGRing_colimit
    (C : Type u) [CommRing C] [HenselianLocalRing C] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (F : I ⥤ CommRingCat.{u}) (π : F ⟶ (Functor.const I).obj (CommRingCat.of C)),
      (∀ i : I, HenselianLocalRing (F.obj i)) ∧
      (∀ i : I, IsNoetherianRing (F.obj i)) ∧
      (∀ i : I, IsGRing (F.obj i)) ∧
      (∀ (i j : I) (f : i ⟶ j), IsLocalHom (F.map f).hom) ∧
      (∀ i : I, IsLocalHom (π.app i).hom) ∧
      Nonempty (IsColimit (Cocone.mk (CommRingCat.of C) π)) := by
  sorry

end CommRingCat
