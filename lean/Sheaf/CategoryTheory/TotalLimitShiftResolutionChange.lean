/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.CategoryTheory.KInjectiveDerivedMapComputation

/-!
# Resolution independence of the total inverse-limit shift

Source: Stacks Project, Derived Categories, Tags 070I, 070K and 070Y;
Cohomology on Sites, Section 0940, and the explicit limit/shift refinement
(blueprint: lem-a1-total-limit-shift-resolution-change).

The ordinary limit is Mathlib's `lim`, applied degreewise. Positive tower index
`n + 1` is encoded by `n : ℕ`. The shift of this functor is Mathlib's canonical
`mapCochainComplexShiftIso`, whose degree components are identities.
The arbitrary universal pair `(L, η)` is retained, rather than choosing a new pair.
-/

@[expose] public section

set_option autoImplicit false

universe wA wT uC vC r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The inverse-limit functor on module-sheaf towers is additive.
Source: the compatible-tuple calculation in step 1, Stacks Section 0940
(blueprint: lem-a1-total-limit-shift-resolution-change).

Proof: compose the two candidate maps for the image of a sum with every limit
projection. Both composites are the sum of the two component maps followed by the
source projection. The projections are jointly monic, so the maps are equal.
Only additivity and the universal property of the ordinary limit are used; there
is no exactness assumption on products. -/
@[instance]
theorem ringedTowerLimit_additive
    {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] (R : Sheaf J RingCat.{r}) :
    (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{r, r, vC, uC} R) ⥤
      ringedSiteModules.{r, r, vC, uC} R).Additive := by
  sorry

/-- Every K-injective tower resolution computes the same coherent total-limit shift.
The three initial conjuncts specify limit homotopies, the tuple-identity shift and
its strict naturality. The family `d` consists of all normalized resolution
isomorphisms, with uniqueness, change of resolution, and stability under shifts.
The final `CommShift ℤ` gives naturality on ALL derived morphisms and zero/addition
coherence. Its displayed equation is exactly the formula for beta, after
multiplication by `d` for the shifted resolution and the canonical Q-shift map.

Source: Stacks Tags 070I, 070K and 070Y and the explicit seven-step refinement
(blueprint: lem-a1-total-limit-shift-resolution-change).

Proof plan:
1. Limits are compatible tuples and the projections are jointly monic. Additivity
   (ringedTowerLimit_additive) transports the homotopy equation degreewise;
   the limit of its homotopy maps is characterized by the projection equation.
2. The strict-tower total-derived theorem supplies K-injective computation without
   exact products. The universal property of def-sfb-right-derived-functor transfers
   it to the supplied pair. Thus eta is invertible on every K-injective. Set
   d_q = eta_I followed by the inverse of L(Qq). This proves normalization and
   uniqueness (def-weil-abstract-derived-category inverts quasi-isomorphisms).
3. The Hom bijection into a K-injective (Tag 070I,
   lem-weil-pbc-kinjective-hom-derived) represents Qq' times inverse Qq by v.
   Represent its inverse likewise. Injectivity of the Hom bijection gives vq
   homotopic to q' and the two inverse homotopies. Naturality of eta and
   cancellation give Q(limit v) followed by d_q' equals d_q for every such v.
   Step 1 removes dependence on a homotopy representative.
4. Shifts preserve quasi-isomorphisms and K-injectivity
   (lem-weil-pbc-kinjective-shift). Degree i on both sides of lambda is limit I^(i+r),
   with differential (-1)^r times limit d. Thus lambda has identity components,
   is natural in all tower chain maps, and obeys zero/addition coherence.
5. Define beta using d_q[r], lambda and inverse d_q[r]. Comparing resolutions by
   step 3 and using the naturality square of step 4 cancels the two comparison
   maps and proves resolution independence.
6. For any derived h choose resolutions q,p and represent Qp h inverse Qq by a
   chain map g between their K-injectives. The arbitrary-derived-map computation
   lem-sf-kinjective-derived-map-computation gives L(h)d_q = d_p Q(limit g).
   Apply it also to g[r]; step 4 and cancellation give naturality of beta for h.
7. For zero shift the formula is d_q times its inverse. For addition use q,
   q[r], q[r][s] simultaneously and cancel the middle d. The tuple shift coherence
   identifies the remaining lambdas. Naturality from step 6 for the canonical
   shift associators identifies the shifted resolution comparisons. This proves
   the CommShift laws also for negative integers. No degree-term injectivity
   was used anywhere. -/
theorem totalLimitShiftResolutionChange
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] (R : Sheaf J RingCat.{r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{wA} (ringedSiteModules.{r, r, vC, uC} R)]
    [HasDerivedCategory.{wT} (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R))]
    (L : DerivedCategory.{wT} (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ⥤
      DerivedCategory.{wA} (ringedSiteModules.{r, r, vC, uC} R))
    (η : (lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ⥤ (ringedSiteModules.{r, r, vC, uC}
      R)).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q.{wA} ⟶ DerivedCategory.Q.{wT} ⋙ L)
    (_hL : L.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) (.up ℤ))) :
    (∀ (X Y : CochainComplex (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ℤ) (f g : X ⟶ Y)
      (H : Homotopy f g) (i j : ℤ) (n : ℕ),
      ((lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ⥤ (ringedSiteModules.{r, r, vC, uC}
        R)).mapHomotopy H).hom i j ≫ limit.π (Y.X j) (op n) =
        limit.π (X.X i) (op n) ≫ (H.hom i j).app (op n)) ∧
    (∀ (I : CochainComplex (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ℤ) (s i : ℤ),
      ((((lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ⥤ (ringedSiteModules.{r, r, vC, uC}
        R)).mapHomologicalComplex (.up ℤ)).commShiftIso s).hom.app I).f i = 𝟙 _) ∧
    (∀ (I I' : CochainComplex (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ℤ) (v : I ⟶ I') (s : ℤ),
      ((lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ⥤ (ringedSiteModules.{r, r, vC, uC}
        R)).mapHomologicalComplex (.up ℤ)).map (v⟦s⟧') ≫ (((lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r,
          vC, uC} R)) ⥤ (ringedSiteModules.{r, r, vC, uC} R)).mapHomologicalComplex (.up
            ℤ)).commShiftIso s).hom.app I' =
        (((lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ⥤ (ringedSiteModules.{r, r, vC, uC}
          R)).mapHomologicalComplex (.up ℤ)).commShiftIso s).hom.app I ≫ (((lim : (ℕᵒᵖ ⥤
            (ringedSiteModules.{r, r, vC, uC} R)) ⥤ (ringedSiteModules.{r, r, vC, uC}
              R)).mapHomologicalComplex (.up ℤ)).map v)⟦s⟧') ∧
    ∃ d : ∀ (X I : CochainComplex (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ℤ) (q : X ⟶ I)
      [QuasiIso q] [I.IsKInjective],
      DerivedCategory.Q.{wA}.obj (((lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ⥤
        (ringedSiteModules.{r, r, vC, uC} R)).mapHomologicalComplex (.up ℤ)).obj I) ≅
        L.obj (DerivedCategory.Q.{wT}.obj X),
      (∀ (X I : CochainComplex (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ℤ) (q : X ⟶ I)
        [QuasiIso q] [I.IsKInjective],
        (d X I q).hom ≫ L.map (DerivedCategory.Q.{wT}.map q) = η.app I ∧
        ∀ e : DerivedCategory.Q.{wA}.obj (((lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ⥤
          (ringedSiteModules.{r, r, vC, uC} R)).mapHomologicalComplex (.up ℤ)).obj I) ≅
          L.obj (DerivedCategory.Q.{wT}.obj X),
          e.hom ≫ L.map (DerivedCategory.Q.{wT}.map q) = η.app I → e = d X I q) ∧
      (∀ (X I I' : CochainComplex (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ℤ) (q : X ⟶ I) (q'
        : X ⟶ I')
        [QuasiIso q] [QuasiIso q'] [I.IsKInjective] [I'.IsKInjective],
        (∃ v : HomotopyEquiv I I', Nonempty (Homotopy (q ≫ v.hom) q')) ∧
        ∀ (v : HomotopyEquiv I I'), Nonempty (Homotopy (q ≫ v.hom) q') →
          DerivedCategory.Q.{wA}.map (((lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ⥤
            (ringedSiteModules.{r, r, vC, uC} R)).mapHomologicalComplex (.up ℤ)).map v.hom) ≫ (d X
              I' q').hom =
            (d X I q).hom) ∧
      (∀ (X I : CochainComplex (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ℤ) (q : X ⟶ I)
        [QuasiIso q] [I.IsKInjective] (s : ℤ),
        QuasiIso (q⟦s⟧') ∧ (I⟦s⟧).IsKInjective) ∧
      ∃ c : L.CommShift ℤ,
        ∀ (X I : CochainComplex (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ℤ) (q : X ⟶ I)
          [QuasiIso q] [I.IsKInjective] (s : ℤ),
          (d (X⟦s⟧) (I⟦s⟧) (q⟦s⟧')).hom ≫
              L.map ((DerivedCategory.Q.{wT}.commShiftIso s).hom.app X) ≫
              (Functor.commShiftIso L (self := c) s).hom.app (DerivedCategory.Q.{wT}.obj X) =
            DerivedCategory.Q.{wA}.map ((((lim : (ℕᵒᵖ ⥤ (ringedSiteModules.{r, r, vC, uC} R)) ⥤
              (ringedSiteModules.{r, r, vC, uC} R)).mapHomologicalComplex (.up ℤ)).commShiftIso
                s).hom.app I) ≫
              (DerivedCategory.Q.{wA}.commShiftIso s).hom.app (((lim : (ℕᵒᵖ ⥤
                (ringedSiteModules.{r, r, vC, uC} R)) ⥤ (ringedSiteModules.{r, r, vC, uC}
                  R)).mapHomologicalComplex (.up ℤ)).obj I) ≫
              (d X I q).hom⟦s⟧' := by
  sorry

end CategoryTheory
