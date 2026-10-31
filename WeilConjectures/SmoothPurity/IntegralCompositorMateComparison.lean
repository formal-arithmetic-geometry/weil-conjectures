/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Logic.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharP.Defs
public import WeilConjectures.SixFunctors.CondensedCompactSupportCompositionData
public import WeilConjectures.AlgebraicGeometry.CompactificationCoherenceCocycle
public import WeilConjectures.AlgebraicGeometry.CompactificationRefinementLocalizing
public import WeilConjectures.SmoothPurity.IntegralOpenProperExchange

/-!
# Integral compact-support compositor and its mate comparison

Source: literature/stacks-project/more-etale.tex, Tags 0F7I and 0F7J
(blueprint: lem-pur-integral-compositor-mate-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CompactSupportComposition

/- The normalized equality is the mate characterization of the compositor on a
   compatible compactification triangle. -/
/--
The integral compact-support compositor is the mate-defined compositor.  The first
conjunct is the refinement comparison normalization, and the second is the
proper/open mate formula on every compactification triangle.  These are equalities
of arrows in the ambient derived categories.

Source: Stacks Project, more-etale.tex, Tags 0F7I and 0F7J; the refinement map is
the adjunction mate of `def-pur-integral-refinement-comparison`, and the tower map
is the normalized proper/open mate of `def-pur-integral-open-proper-exchange`
(blueprint: lem-pur-integral-compositor-mate-comparison).

Proof plan.  Use the common dense refinement and the cocycle for the first
equality.  On a compatible triangle use the injectivity of the open adjunction
Hom-bijection to identify the normalized interchange with the exchange mate;
then apply the derived direct-image compositor.  Transport to arbitrary
compactifications by the independence clause and the cocycle.  Identity cases
follow from the unit clauses, and all equalities are component equalities of
morphisms.
-/
theorem integralCompositorMateComparison
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] (hple : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (H : CompactSupportComposition.CoherentData
      (Profinite.padicIntegersRingObj ell E.val) k) :
    (∀ {X Y : SepFinType k} (f : X ⟶ Y)
        (c d : Compactification f.hom.left)
        (r : Compactification.DenseBoundaryCompactification f.hom.left)
        [QuasiCompact f.hom.left]
        (hc : r.obj ⟶ detSfBoundaryCompactification c)
        (hd : r.obj ⟶ detSfBoundaryCompactification d)
        (K : (localizingClosureProEtale
          (Profinite.padicIntegersRingObj ell E.val) X.obj.left).FullSubcategory),
      (H.comparison f c d).hom.app K ≫
          compactificationRefinementComponent
            (Profinite.padicIntegersRingObj ell E.val) hd K.obj =
        compactificationRefinementComponent
          (Profinite.padicIntegersRingObj ell E.val) hc K.obj) ∧
    (∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
        (T : Compactification.Triangle f.hom.left g.hom.left)
        [QuasiCompact (T.cf.g ≫ T.cg.i)]
        (K : (localizingClosureProEtale
          (Profinite.padicIntegersRingObj ell E.val) X.obj.left).FullSubcategory),
      ∃ m, compositionInterchangeIsNormalized
          (Profinite.padicIntegersRingObj ell E.val) T.cf.g T.cg.i
          (detSfBoundaryCompactification (middle T))
          (D((T.cf.i)_!open⟦Profinite.padicIntegersRingObj ell E.val⟧).obj K.obj) m ∧
        (H.comp f g T.cf T.cg T.cfg).hom.app K =
          R((T.cg.g)_*⟦Profinite.padicIntegersRingObj ell E.val⟧).map
            (m ≫ R((T.p)_*⟦Profinite.padicIntegersRingObj ell E.val⟧).map
              ((openFactor (Profinite.padicIntegersRingObj ell E.val)
                T.cf.i T.q T.cfg.i T.i_q).hom.app K.obj)) ≫
          (rightDerivedLowerStarComp
            (Profinite.padicIntegersRingObj ell E.val) T.p T.cg.g).hom.app
            (D((T.cfg.i)_!open⟦Profinite.padicIntegersRingObj ell E.val⟧).obj K.obj) ≫
          (Functor.rightDerivedFunctorNatIso
            (eqToIso (congrArg (lowerStar
              (Profinite.padicIntegersRingObj ell E.val)) T.p_g))).hom.app
              (D((T.cfg.i)_!open⟦Profinite.padicIntegersRingObj ell E.val⟧).obj K.obj)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
