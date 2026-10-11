/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.EdgeMap
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Low-degree Leray comparison for an open immersion

Source: literature/stacks-project/etale-cohomology.tex, discussion preceding Tag 03RM
(blueprint: lem-sc-open-curve-etale-leray-low-degree).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Low-degree Leray comparison for an open immersion.

Source: literature/stacks-project/etale-cohomology.tex, discussion preceding Tag 03RM
(blueprint: lem-sc-open-curve-etale-leray-low-degree).

The canonical edge map is pullback on cohomology followed by the counit, as in
`Etale.map_counit_cohomologyMap`. Here `Sheaf.H` is the existing Ext model of
abelian sheaf cohomology; bijectivity of this additive map says it is an isomorphism.

Proof: Geometric stalk conservativity turns the stalkwise vanishing of the first two
higher direct images into vanishing sheaves
(`lemma-weil-pbc-geometric-stalk-conservative`). Apply `thm-sp-grothendieck` to direct
image followed by global sections. Direct image preserves injectives
(`lem-weil-pbc-direct-image-preserves-injectives`), supplying acyclicity, and the
identity of global sections of the direct image identifies the abutment with
cohomology on `C` (`def-weil-pbc-direct-image`, `def-weil-pbc-etale-cohomology`).
The bottom edge is the natural Leray edge (`lem-sp-grothendieck-edge-maps`). In total
degrees n at most two, rows one and two vanish. Incoming differentials to (n,0)
come from row r-1: these vanish for r=2,3, and have negative first coordinate for
r at least four. Outgoing differentials have negative second coordinate. Thus
E_2^{n,0}=E_infty^{n,0}, and every other graded piece of the finite filtration
vanishes. The bottom edge is therefore an isomorphism for n=0,1,2.
-/
theorem openCurveEtaleLerayLowDegree
    {C Cbar : Scheme.{u}} (j : C ⟶ Cbar) [IsOpenImmersion j]
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hvanish : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (x : Spec (.of Ω) ⟶ Cbar) (q : ℤ),
      (q = 1 ∨ q = 2) →
        IsZero
          ((Scheme.pointSmallEtale x).sheafFiber.obj
            ((DerivedCategory.homologyFunctor
              (Sheaf Cbar.smallEtaleTopology AddCommGrpCat.{u + 1}) q).obj
              ((Etale.rightDerivedLowerStar AddCommGrpCat.{u + 1} j).obj
                ((DerivedCategory.singleFunctor
                  (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))))) :
    ∀ q : ℕ, (q = 0 ∨ q = 1 ∨ q = 2) →
      Function.Bijective fun x : Sheaf.H ((Etale.lowerStar AddCommGrpCat.{u + 1} j).obj F) q ↦
        Sheaf.H.map ((Etale.upperStarLowerStarAdjunction
          AddCommGrpCat.{u + 1} j).counit.app F) q
          (Etale.cohomologyMap j _ q x) := by
  sorry

end AlgebraicGeometry
