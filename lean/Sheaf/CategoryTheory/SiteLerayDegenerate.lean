module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Sheaf.CategoryTheory.SiteCohomologyPullback
import Sheaf.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Degeneration of the Leray comparison for a morphism of sites

Source: Stacks Project, Cohomology on Sites, Lemma 0733
(blueprint: lem-weil-pbc-site-leray-degenerate).

The statement records the Leray comparison in the case where all positive right
derived direct images vanish.  The comparison is represented by a family of
objectwise cohomology morphisms.

The source proof proceeds by choosing an injective resolution of `F`.  The
pushforward of that resolution is an injective resolution because pushforward
is right adjoint to the exact inverse image.  Vanishing of the positive right
derived pushforwards makes this pushed-forward complex exact.  Computing both
cohomology groups from these resolutions, the pullback map followed by the
counit is identified with the identity by the triangle identity, hence is an
isomorphism in every degree (and is the identity in degree zero).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- If the positive right derived direct images of a sheaf vanish, the Leray
comparison from the cohomology of its direct image to the cohomology upstairs is
 an isomorphism in every degree.

Source: Stacks Project, Cohomology on Sites, Lemma 0733(1), using Lemmas
072Z and 0730 (blueprint: lem-weil-pbc-site-leray-degenerate).

(blueprint: lem-weil-pbc-site-leray-degenerate) -/
theorem siteLeray_degenerate
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (K : Precoverage D)
    [J.HasIsos] [J.IsStableUnderComposition] [J.IsStableUnderBaseChange] [J.HasPullbacks]
    [K.HasIsos] [K.IsStableUnderComposition] [K.IsStableUnderBaseChange] [K.HasPullbacks]
    (U : D ⥤ C)
    [U.IsContinuous K.toGrothendieck J.toGrothendieck]
    [PreservesFiniteLimits (Functor.sheafPullbackConstruction.sheafPullback U
      (Type u) K.toGrothendieck J.toGrothendieck)]
    [PreservesFiniteColimits (Functor.sheafPullbackConstruction.sheafPullback U
      (Type u) K.toGrothendieck J.toGrothendieck)]
    [(Functor.sheafPullbackConstruction.sheafPullback U AddCommGrpCat.{u}
      K.toGrothendieck J.toGrothendieck).Additive]
    [(Functor.sheafPushforwardContinuous U AddCommGrpCat.{u}
      K.toGrothendieck J.toGrothendieck).Additive]
    [HasExt (Sheaf K.toGrothendieck AddCommGrpCat.{u})]
    [HasExt (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf K.toGrothendieck AddCommGrpCat.{u})]
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{u})
    (he : ∀ (q : ℕ), 0 < q →
      IsZero (((Functor.sheafPushforwardContinuous U AddCommGrpCat.{u}
        K.toGrothendieck J.toGrothendieck).rightDerived q).obj F)) :
    ∃ e : ∀ (p : ℕ) (V : D),
      Sheaf.H' ((Functor.sheafPushforwardContinuous U AddCommGrpCat.{u}
        K.toGrothendieck J.toGrothendieck).obj F) p V ⟶
      Sheaf.H' F p (U.obj V),
      ∀ (p : ℕ) (V : D), IsIso (e p V) := by
  sorry

end CategoryTheory
