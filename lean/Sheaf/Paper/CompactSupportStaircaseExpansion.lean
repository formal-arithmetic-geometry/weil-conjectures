/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Sheaf.Paper.UnboundedProperOpenInterchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition

/-!
# Fixed-staircase expansion of compact-support comparisons

Source: Stacks Project, More on Étale Cohomology, Tag 0F7K, proof of
`lemma-pseudo-functor` (blueprint: lem-amb-compact-support-staircase-expansion).

## Main definitions and statement

* `compactSupportStaircaseInterchange`: the specified normalized interchange family.
* `compactSupportRawBinaryComparison`: the raw binary comparison on a proper/open tower.
* `compactSupportStaircaseTargetIso`: the common six-factor target identification.
* `compactSupportStaircaseExpansion`: the two fixed-staircase expansion identities.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The specified normalized interchange of Tags 0F7B--0F7F, used in Tag 0F7K
(blueprint: lem-amb-compact-support-staircase-expansion).
This selects the family supplied by `unboundedProperOpenInterchange`, with its complete
normalization. Its sheaf map is determined by its composite into the common direct image;
its derived map is determined on every K-injective representative and resolution. Thus this
choice determines the natural isomorphism up to equality, rather than choosing an arbitrary
isomorphism between the two functors. -/
noncomputable def compactSupportStaircaseInterchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U V W Z : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : CommSq k r p i) :
    R((r)_*[ModuleCat.{u + 1} A]) ⋙ D((i)_!open[ModuleCat.{u + 1} A]) ≅
      D((k)_!open[ModuleCat.{u + 1} A]) ⋙ R((p)_*[ModuleCat.{u + 1} A]) :=
  (Classical.choose (Classical.choose_spec (unboundedProperOpenInterchange A))) k r p i sq

/-- The raw binary comparison on a proper/open tower, before any compactification
independence. Source: Tag 0F7K, proof of `lemma-pseudo-functor`, using Tags 0F7C--0F7D
(blueprint: lem-amb-compact-support-staircase-expansion).
The four factors are the specified interchange, outer proper direct image, and the
canonical direct-image and open-extension composition isomorphisms. Associators only
parenthesize these functors. The candidates are exactly
`rightDerivedLowerShriekOfCompactification (ModuleCat A)` for the displayed factorizations. -/
noncomputable def compactSupportRawBinaryComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U V Y W Z : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian Y] [IsNoetherian W]
    (l : X ⟶ U) (a : U ⟶ V) (m : U ⟶ Y) (r : V ⟶ W) (d : Y ⟶ W) (q : W ⟶ Z)
    [IsOpenImmersion l] [IsOpenImmersion a] [IsOpenImmersion d]
    [IsProper m] [IsProper r] [IsProper q] (sq : CommSq a m r d) :
    (D((l)_!open[ModuleCat.{u + 1} A]) ⋙ R((m)_*[ModuleCat.{u + 1} A])) ⋙
        (D((d)_!open[ModuleCat.{u + 1} A]) ⋙ R((q)_*[ModuleCat.{u + 1} A])) ≅
      D((l ≫ a)_!open[ModuleCat.{u + 1} A]) ⋙ R((r ≫ q)_*[ModuleCat.{u + 1} A]) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight (compactSupportStaircaseInterchange A a m r d sq) _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) r q)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
          (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) l a) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).symm _

/-- The common target identification in Tag 0F7K, proof of `lemma-pseudo-functor`
(blueprint: lem-amb-compact-support-staircase-expansion).
It expands `R(tsp)_*D(bal)_!` into the six displayed factors. The proper factors are
expanded first and the open factors second. Both use the canonical composition maps,
with the left-associated scheme composites as the fixed parenthesization. -/
noncomputable def compactSupportStaircaseTargetIso
    (A : Type (u + 1)) [CommRing A]
    {X U V Xbar Ybar Zbar T : Scheme.{u}}
    (l : X ⟶ U) (a : U ⟶ V) (b : V ⟶ Xbar)
    (p : Xbar ⟶ Ybar) (s : Ybar ⟶ Zbar) (t : Zbar ⟶ T)
    [IsOpenImmersion l] [IsOpenImmersion a] [IsOpenImmersion b]
    (K : DerivedCategoryModule A X) :
    R(((p ≫ s) ≫ t)_*[ModuleCat.{u + 1} A]).obj
        (D(((l ≫ a) ≫ b)_!open[ModuleCat.{u + 1} A]).obj K) ≅
      R((t)_*[ModuleCat.{u + 1} A]).obj
        (R((s)_*[ModuleCat.{u + 1} A]).obj
          (R((p)_*[ModuleCat.{u + 1} A]).obj
            (D((b)_!open[ModuleCat.{u + 1} A]).obj
              (D((a)_!open[ModuleCat.{u + 1} A]).obj
                (D((l)_!open[ModuleCat.{u + 1} A]).obj K))))) :=
  (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) (p ≫ s) t).symm.app _ ≪≫
    R((t)_*[ModuleCat.{u + 1} A]).mapIso
      ((rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p s).symm.app _) ≪≫
    R((t)_*[ModuleCat.{u + 1} A]).mapIso
      (R((s)_*[ModuleCat.{u + 1} A]).mapIso
        (R((p)_*[ModuleCat.{u + 1} A]).mapIso
          ((Functor.mapDerivedCategoryNatIso
              (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) (l ≫ a) b) ≪≫
            Functor.mapDerivedCategoryCompIso _ _).app K ≪≫
            D((b)_!open[ModuleCat.{u + 1} A]).mapIso
              ((Functor.mapDerivedCategoryNatIso
                  (openImmersionLowerShriekComp (ModuleCat.{u + 1} A) l a) ≪≫
                Functor.mapDerivedCategoryCompIso _ _).app K))))

/-- Expansion of the two iterated raw comparisons on the fixed cartesian staircase.
Source: Stacks Project, Tag 0F7K, proof of `lemma-pseudo-functor`
(blueprint: lem-amb-compact-support-staircase-expansion).

The first conjunct is the route `(g,f)` then `(h,gf)`, expanded as A, C, B.
The second is `(h,g)` then `(hg,f)`, expanded as C, A, B. Equations hold at every
unbounded derived input, and so are identities of natural transformations.

Proof plan:
1. Unfold `compactSupportRawBinaryComparison`. The candidates are `Dl_!Rm_*`,
   `Dd_!Rq_*`, `Di_!Rt_*`, `D(al)_!R(qr)_*`, `D(kd)_!R(ts)_*`, and
   `D(bal)_!R(tsp)_*`, in Lean's left-to-right functor notation. The four binary
   comparisons use A, C, the vertical rectangle B+C, and the horizontal rectangle A+B.
   This uses def-amb-etale-compact-support and lem-amb-unbounded-proper-open-interchange.
2. Identify both targets with the six factors using `compactSupportStaircaseTargetIso`.
   Open-extension associativity is the three-fold clause of
   lem-cbc-extension-zero-composition, applied degreewise. Proper associativity follows
   from the K-injective normalization of
   lem-weil-pbc-ringed-topoi-derived-pushforward-composition: both routes are represented
   by `t_*` applied to `s_*p_*I → s_*J → K` for successive resolutions.
   The uniqueness of the representing homotopy classes is
   lem-weil-pbc-kinjective-hom-derived. The `eqToHom` in the second route only changes
   the parenthesization of the scheme composites.
3. Apply vertical pasting from lem-amb-unbounded-proper-open-interchange to B+C and
   horizontal pasting to A+B. Whisker by the remaining factors, then use naturality of
   the composition isomorphisms. The resulting three factors are exactly those on the
   two right-hand sides. This proves the two expansion identities separately; no
   equality between them or compactification independence is asserted. -/
theorem compactSupportStaircaseExpansion
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U V Xbar Y W Ybar Z Zbar T : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian U] [IsNoetherian V] [IsNoetherian Xbar]
    [IsNoetherian Y] [IsNoetherian W] [IsNoetherian Ybar] [IsNoetherian Z]
    [IsNoetherian Zbar] [IsNoetherian T]
    (l : X ⟶ U) (a : U ⟶ V) (b : V ⟶ Xbar)
    (d : Y ⟶ W) (k : W ⟶ Ybar) (i : Z ⟶ Zbar)
    (m : U ⟶ Y) (r : V ⟶ W) (p : Xbar ⟶ Ybar)
    (q : W ⟶ Z) (s : Ybar ⟶ Zbar) (t : Zbar ⟶ T)
    [IsOpenImmersion l] [IsOpenImmersion a] [IsOpenImmersion b]
    [IsOpenImmersion d] [IsOpenImmersion k] [IsOpenImmersion i]
    [IsProper m] [IsProper r] [IsProper p] [IsProper q] [IsProper s] [IsProper t]
    (QA : IsPullback a m r d) (QB : IsPullback b r p k) (QC : IsPullback k q s i)
    (K : DerivedCategoryModule A X) :
    (R((t)_*[ModuleCat.{u + 1} A]).map
        (D((i)_!open[ModuleCat.{u + 1} A]).map
          ((compactSupportRawBinaryComparison A l a m r d q QA.toCommSq).hom.app K)) ≫
      (compactSupportRawBinaryComparison A (l ≫ a) b (r ≫ q) (p ≫ s) i t
        (QB.toCommSq.vert_comp QC.toCommSq)).hom.app K ≫
      (compactSupportStaircaseTargetIso A l a b p s t K).hom =
      R((t)_*[ModuleCat.{u + 1} A]).map
        (D((i)_!open[ModuleCat.{u + 1} A]).map
          (R((q)_*[ModuleCat.{u + 1} A]).map
            ((compactSupportStaircaseInterchange A a m r d QA.toCommSq).hom.app
              (D((l)_!open[ModuleCat.{u + 1} A]).obj K)))) ≫
      R((t)_*[ModuleCat.{u + 1} A]).map
        ((compactSupportStaircaseInterchange A k q s i QC.toCommSq).hom.app
          (R((r)_*[ModuleCat.{u + 1} A]).obj
            (D((a)_!open[ModuleCat.{u + 1} A]).obj
              (D((l)_!open[ModuleCat.{u + 1} A]).obj K)))) ≫
      R((t)_*[ModuleCat.{u + 1} A]).map
        (R((s)_*[ModuleCat.{u + 1} A]).map
          ((compactSupportStaircaseInterchange A b r p k QB.toCommSq).hom.app
            (D((a)_!open[ModuleCat.{u + 1} A]).obj
              (D((l)_!open[ModuleCat.{u + 1} A]).obj K))))) ∧
    ((compactSupportRawBinaryComparison A d k q s i t QC.toCommSq).hom.app
        (R((m)_*[ModuleCat.{u + 1} A]).obj
          (D((l)_!open[ModuleCat.{u + 1} A]).obj K)) ≫
      (compactSupportRawBinaryComparison A l (a ≫ b) m p (d ≫ k) (s ≫ t)
        (QA.toCommSq.horiz_comp QB.toCommSq)).hom.app K ≫
      eqToHom (by simp only [Category.assoc, Functor.comp_obj]) ≫
      (compactSupportStaircaseTargetIso A l a b p s t K).hom =
      R((t)_*[ModuleCat.{u + 1} A]).map
        ((compactSupportStaircaseInterchange A k q s i QC.toCommSq).hom.app
          (D((d)_!open[ModuleCat.{u + 1} A]).obj
            (R((m)_*[ModuleCat.{u + 1} A]).obj
              (D((l)_!open[ModuleCat.{u + 1} A]).obj K)))) ≫
      R((t)_*[ModuleCat.{u + 1} A]).map
        (R((s)_*[ModuleCat.{u + 1} A]).map
          (D((k)_!open[ModuleCat.{u + 1} A]).map
            ((compactSupportStaircaseInterchange A a m r d QA.toCommSq).hom.app
              (D((l)_!open[ModuleCat.{u + 1} A]).obj K)))) ≫
      R((t)_*[ModuleCat.{u + 1} A]).map
        (R((s)_*[ModuleCat.{u + 1} A]).map
          ((compactSupportStaircaseInterchange A b r p k QB.toCommSq).hom.app
            (D((a)_!open[ModuleCat.{u + 1} A]).obj
              (D((l)_!open[ModuleCat.{u + 1} A]).obj K))))) := by
  sorry

end AlgebraicGeometry.Etale
