/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.AcyclicHeartEdge
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction

/-! # Cohomology of the derived unit and counit on acyclic hearts

Source: Stacks Project, sites-cohomology.tex, Tags 0D7S, 0D7T and 0D7U,
lemma-bounded-in-image-upstairs/downstairs and lemma-equivalence-bounded;
the canonical cohomology-map refinement of their truncation argument.
(blueprint: lem-fd-derived-unit-counit-cohomology-compatibility).
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ v₁ v₂ w₁ w₂

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  [IsGrothendieckAbelian.{v₁} C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [IsGrothendieckAbelian.{v₂} D] [HasDerivedCategory.{w₂} D]

/-- The uniquely normalized truncation edge, transported to the bounded-below
right derived functor by its canonical Kan-extension comparison. The choice is from
exists_acyclicHeartEdge, which determines the whole family uniquely.
Source: Stacks Tag 0D7U (blueprint: lem-fd-derived-unit-counit-cohomology-compatibility). -/
noncomputable def acyclicHeartEdgePlus (R : D ⥤ C) [R.Additive]
    [PreservesFiniteLimits R] (M : DerivedCategory.Plus D)
    (hM : ∀ (j : ℤ) (p : ℕ), 0 < p →
      IsZero ((R.rightDerived p).obj ((DerivedCategory.homologyFunctor D j).obj M.obj)))
    (q : ℤ) :
    (DerivedCategory.homologyFunctor C q).obj (R.rightDerivedFunctorPlus.obj M).obj ⟶
      R.obj ((DerivedCategory.homologyFunctor D q).obj M.obj) :=
  (DerivedCategory.homologyFunctor C q).map
      (R.rightDerivedFunctorPlusCompatibility.hom.app M) ≫
    (R.exists_acyclicHeartEdge.exists.choose) M hM q

end CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  [IsGrothendieckAbelian.{v₁} C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  [IsGrothendieckAbelian.{v₂} D] [HasDerivedCategory.{w₂} D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] [PreservesFiniteLimits R]

/-- The composite R(a_K) e_(L_D K) H^q(eta^D_K), with the canonical edge and exact
comparison. Composition in Lean is written from left to right.
Source: Stacks Tag 0D7T (blueprint: lem-fd-derived-unit-counit-cohomology-compatibility). -/
noncomputable def derivedPlusAcyclicUnit (adj : L ⊣ R) (K : DerivedCategory.Plus C)
    (hK : ∀ (j : ℤ) (p : ℕ), 0 < p →
      IsZero ((R.rightDerived p).obj
        (L.obj ((DerivedCategory.homologyFunctor C j).obj K.obj)))) (q : ℤ) :
    (DerivedCategory.homologyFunctor C q).obj K.obj ⟶
      R.obj (L.obj ((DerivedCategory.homologyFunctor C q).obj K.obj)) :=
  (DerivedCategory.homologyFunctor C q).map (adj.derivedPlus.unit.app K).hom ≫
    R.acyclicHeartEdgePlus (L.mapDerivedCategoryPlus.obj K)
      (fun j p hp => (hK j p hp).of_iso
        ((R.rightDerived p).mapIso
          ((L.mapDerivedCategoryPlusHomologyFunctorIso j).app K).symm)) q ≫
    R.map ((L.mapDerivedCategoryPlusHomologyFunctorIso q).inv.app K)

/-- The composite epsilon_(H^q M) L(e_M) a_(R^+ M), with both comparisons fixed
canonically by the dependency interfaces.
Source: Stacks Tag 0D7S (blueprint: lem-fd-derived-unit-counit-cohomology-compatibility). -/
noncomputable def derivedPlusAcyclicCounit (adj : L ⊣ R) (M : DerivedCategory.Plus D)
    (hM : ∀ (j : ℤ) (p : ℕ), 0 < p →
      IsZero ((R.rightDerived p).obj ((DerivedCategory.homologyFunctor D j).obj M.obj)))
    (q : ℤ) :
    (DerivedCategory.homologyFunctor D q).obj
        (L.mapDerivedCategoryPlus.obj (R.rightDerivedFunctorPlus.obj M)).obj ⟶
      (DerivedCategory.homologyFunctor D q).obj M.obj :=
  (L.mapDerivedCategoryPlusHomologyFunctorIso q).inv.app (R.rightDerivedFunctorPlus.obj M) ≫
    L.map (R.acyclicHeartEdgePlus M hM q) ≫
    adj.counit.app ((DerivedCategory.homologyFunctor D q).obj M.obj)

/-- Cohomology identifies the canonical derived unit and counit with the ordinary ones,
naturally on the respective acyclicity subcategories. The last clause computes the
ordinary counit on an object identified with L(Cq).
Source: Stacks Tags 0D7S/0D7T/0D7U, canonical-map refinement
(blueprint: lem-fd-derived-unit-counit-cohomology-compatibility).

Proof:
1. lem-fd-acyclic-edge-complex-comparison identifies e H(alpha) with the cycles/cokernel
   edge of def-weil-pbc-left-exact-homology-edge; its defining cycle equation is
   h_R pi_(RX) = R(pi_X) k_X.
2. Represent K by a bounded-below complex N using lem-sp-grothendieck-enough-injectives
   and lem-weil-pbc-dplus-injective-representative. Unit naturality at the cycle
   inclusion and quotient, and lem-weil-pbc-exact-functor-bounded-below, give
   R(a_N) h_R(LN) H(unit_N) pi_N = eta_(H(N)) pi_N. Cancel the epi pi_N.
3. Apply cohomology and the edge to derivedPlus_unit_app_fac from
   lem-trf-bounded-below-derived-adjunction. Edge naturality and the termwise exact
   comparison reduce to steps 1 and 2. Transport across QN isomorphic to K.
4. Represent M by a bounded-below injective complex I. Its comparison alpha_I is
   invertible by lem-weil-pbc-right-derived-plus-injective.
5. On I, compare H(counit_I) a_(RI)^(-1) and epsilon_(H(I)) L(h_R(I)) after the epi
   L(pi_(RI)). Counit naturality at cycles and their quotient identifies both with
   pi_I epsilon_(Z(I)) L(k_I). Cancel this epi, since L is exact.
6. Apply cohomology to derivedPlus_counit_app_fac. Substitute step 5 and then step 1;
   cancel H(L_D(alpha_I)), invertible by step 4, and transport to M. Naturality of
   eta, epsilon, a and e gives both asserted squares for every derived morphism.
7. The triangle identity gives epsilon_(L(Cq)) L(eta_Cq) = 1. Invert L(eta_Cq)
   and apply counit naturality at j to obtain the final formula in its displayed order.
-/
theorem derivedPlus_acyclic_cohomology (adj : L ⊣ R) :
    (∀ (K : DerivedCategory.Plus C)
      (hK : ∀ (j : ℤ) (p : ℕ), 0 < p →
        IsZero ((R.rightDerived p).obj
          (L.obj ((DerivedCategory.homologyFunctor C j).obj K.obj)))) (q : ℤ),
      adj.derivedPlusAcyclicUnit K hK q =
        adj.unit.app ((DerivedCategory.homologyFunctor C q).obj K.obj)) ∧
    (∀ (M : DerivedCategory.Plus D)
      (hM : ∀ (j : ℤ) (p : ℕ), 0 < p →
        IsZero ((R.rightDerived p).obj ((DerivedCategory.homologyFunctor D j).obj M.obj)))
      (q : ℤ),
      (DerivedCategory.homologyFunctor D q).map (adj.derivedPlus.counit.app M).hom =
        adj.derivedPlusAcyclicCounit M hM q) ∧
    (∀ (K K' : DerivedCategory.Plus C)
      (hK : ∀ (j : ℤ) (p : ℕ), 0 < p →
        IsZero ((R.rightDerived p).obj
          (L.obj ((DerivedCategory.homologyFunctor C j).obj K.obj))))
      (hK' : ∀ (j : ℤ) (p : ℕ), 0 < p →
        IsZero ((R.rightDerived p).obj
          (L.obj ((DerivedCategory.homologyFunctor C j).obj K'.obj))))
      (f : K ⟶ K') (q : ℤ),
      (DerivedCategory.homologyFunctor C q).map f.hom ≫
          adj.derivedPlusAcyclicUnit K' hK' q =
        adj.derivedPlusAcyclicUnit K hK q ≫
          R.map (L.map ((DerivedCategory.homologyFunctor C q).map f.hom))) ∧
    (∀ (M M' : DerivedCategory.Plus D)
      (hM : ∀ (j : ℤ) (p : ℕ), 0 < p →
        IsZero ((R.rightDerived p).obj ((DerivedCategory.homologyFunctor D j).obj M.obj)))
      (hM' : ∀ (j : ℤ) (p : ℕ), 0 < p →
        IsZero ((R.rightDerived p).obj ((DerivedCategory.homologyFunctor D j).obj M'.obj)))
      (f : M ⟶ M') (q : ℤ),
      (DerivedCategory.homologyFunctor D q).map
          (L.mapDerivedCategoryPlus.map (R.rightDerivedFunctorPlus.map f)).hom ≫
          adj.derivedPlusAcyclicCounit M' hM' q =
        adj.derivedPlusAcyclicCounit M hM q ≫
          (DerivedCategory.homologyFunctor D q).map f.hom) ∧
    (∀ (M : DerivedCategory.Plus D)
      (_hM : ∀ (j : ℤ) (p : ℕ), 0 < p →
        IsZero ((R.rightDerived p).obj ((DerivedCategory.homologyFunctor D j).obj M.obj)))
      (q : ℤ) (Cq : C)
      (j : L.obj Cq ≅ (DerivedCategory.homologyFunctor D q).obj M.obj)
      [IsIso (adj.unit.app Cq)],
      adj.counit.app ((DerivedCategory.homologyFunctor D q).obj M.obj) =
        L.map (R.map j.inv) ≫ inv (L.map (adj.unit.app Cq)) ≫ j.hom) := by
  sorry

end CategoryTheory.Adjunction
