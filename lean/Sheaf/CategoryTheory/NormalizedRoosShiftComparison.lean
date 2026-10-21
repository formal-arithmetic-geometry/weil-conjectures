/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.StrictRoosComparison
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Integer shifts of the normalized strict Roos comparison

Source: Stacks Project, Tag 0941, lemma-derived-limit-is-ok; Tag 014E,
definition-cone; Tag 011G, definition-shift-cochain, with the signed refinement
(blueprint: lem-a1-normalized-roos-shift-comparison).

The cone, inclusion and descent unit are the existing `roosF`, `roosι` and
`roosDerivedUnit`. The unit equation specifies precisely the normalized comparison
of `strictRoosComparison`. Natural index `n` denotes positive tower index `n+1`.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC t w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The normalized Roos comparison respects the signed, coherent integer shifts.
The first two component equations say `(y,x) ↦ ((-1)^r y,x)` after the canonical
termwise identifications. The descent equation identifies that chain shift with
`cD`; the next equation is the requested square for every derived tower object.
The limit projection equation fixes `cL` to the termwise inverse-limit shift.
The inclusion equation preserves `(0,z)`. The final clause computes `cR` using
EVERY K-injective resolution, including those without injective terms: `d` and `ds`
are fixed by the derived unit and the resolution maps, so the formula is independent
of all resolution choices. Each `CommShift ℤ` includes naturality and the zero and
addition coherence laws. In particular natural strict comparisons commuting with
termwise shifts can be composed with this square.

Source: Stacks Project, Tag 0941, lemma-derived-limit-is-ok, shifted K-injective
proof; Tags 014E and 011G, signed cone and shift conventions
(blueprint: lem-a1-normalized-roos-shift-comparison).

Proof plan, following the seven steps of the node:
1. Write h=1-s and a=(-1)^r. The two differentials are (-a dy-hx,a dx)
   and (-a dy-a hx,a dx). The diagonal map (ay,x) intertwines them since a²=1;
   its inverse has the same coordinate formula (def-weil-strict-roos-model).
2. Strict maps act diagonally, hence commute with this sign. Signs multiply under
   addition of shifts and the zero sign is 1 (def-weil-abstract-derived-category).
3. Choose an injective-term K-injective tower resolution using
   lem-pur-injective-tower-roos-shifts. Shifting preserves K-injectivity by
   lem-weil-pbc-kinjective-shift; limit shift is identity on compatible tuples.
4. The normalized inclusion is (0,z), so the signed map preserves it. Apply the
   resolution formula of lem-weil-strict-roos-comparison to the same shifted resolution.
5. Invert that inclusion identity, and use strict naturality for the resolution map.
   Substitution yields sigmaLim rhoShift = rhoShifted sigmaCone, with these exact maps.
6. Localization extends strict naturality to every derived morphism. For another
   K-injective resolution, lem-weil-pbc-kinjective-hom-derived represents its comparison
   by a homotopy equivalence. Limit preserves its homotopies and its termwise shift
   square, proving the same computation for every resolution, without injective terms.
7. Conjugate the coherent cone shifts by rho. Cancellation gives zero and addition
   coherence on derived limits. Naturality composes the square with any natural strict
   tower comparison commuting with termwise shifts. -/
theorem normalizedRoosShiftComparison
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC t}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC t}]
    (R : Sheaf J RingCat.{max uC vC t})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{max uC vC t} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC t} R)]
    (RF CF : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R) ⥤
      DerivedCategory.{w} (ringedSiteModules.{max uC vC t} R))
    (η : roosLimitFunctor (A := ringedSiteModules.{max uC vC t} R) ⋙
      DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF)
    (_hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R) (.up ℤ)))
    (κ : roosF (A := ringedSiteModules.{max uC vC t} R) ⋙
      DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ CF)
    (ρ : CF ≅ RF)
    (_hnorm : ∀ X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R) ℤ,
      DerivedCategory.Q.{w}.map (roosι X) ≫ κ.hom.app X ≫
        ρ.hom.app (DerivedCategory.Q.{w}.obj X) = η.app X) :
    ∃ (cC : (roosF (A := ringedSiteModules.{max uC vC t} R)).CommShift ℤ)
      (cD : CF.CommShift ℤ) (cR : RF.CommShift ℤ)
      (cL : (roosLimitFunctor (A := ringedSiteModules.{max uC vC t} R)).CommShift ℤ),
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R) ℤ)
        (r q : ℤ) (n : ℕ),
        (((Functor.commShiftIso roosF (self := cC) r).hom.app X).f q ≫
            (CochainComplex.shiftFunctorObjXIso (roosF.obj X) r q (q + r) rfl).hom ≫
            (roosProj X).f (q + r) ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (q + r) =
          (roosProj (X⟦r⟧)).f q ≫
            (Pi.π (fun k : ℕ ↦ (X⟦r⟧).asFunctor.obj (op k)) n).f q ≫
            ((CochainComplex.shiftFunctorObjXIso X r q (q + r) rfl).hom).app (op n)) ∧
        (((Functor.commShiftIso roosF (self := cC) r).hom.app X).f q ≫
            (CochainComplex.shiftFunctorObjXIso (roosF.obj X) r q (q + r) rfl).hom ≫
            (CochainComplex.mappingCocone.snd (roosU X)).v
              (q + r) ((q - 1) + r) (by omega) ≫
            (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f ((q - 1) + r) =
          r.negOnePow • ((CochainComplex.mappingCocone.snd (roosU (X⟦r⟧))).v
              q (q - 1) (by omega) ≫
            (Pi.π (fun k : ℕ ↦ (X⟦r⟧).asFunctor.obj (op k)) n).f (q - 1) ≫
            ((CochainComplex.shiftFunctorObjXIso X r (q - 1) ((q - 1) + r) rfl).hom).app
              (op n)))) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R) ℤ) (r : ℤ),
        DerivedCategory.Q.{w}.map ((Functor.commShiftIso roosF (self := cC) r).hom.app X) ≫
            (DerivedCategory.Q.{w}.commShiftIso r).hom.app (roosF.obj X) ≫
            (κ.hom.app X)⟦r⟧' =
          κ.hom.app (X⟦r⟧) ≫ CF.map ((DerivedCategory.Q.{w}.commShiftIso r).hom.app X) ≫
            (Functor.commShiftIso CF (self := cD) r).hom.app (DerivedCategory.Q.{w}.obj X)) ∧
      (∀ (N : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R)) (r : ℤ),
        ρ.hom.app (N⟦r⟧) ≫ (Functor.commShiftIso RF (self := cR) r).hom.app N =
          (Functor.commShiftIso CF (self := cD) r).hom.app N ≫ (ρ.hom.app N)⟦r⟧') ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R) ℤ)
        (r q : ℤ) (n : ℕ),
        ((Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I).f q ≫
            (CochainComplex.shiftFunctorObjXIso (limit I.asFunctor) r q (q + r) rfl).hom ≫
            (limit.π I.asFunctor (op n)).f (q + r) =
          (limit.π (I⟦r⟧).asFunctor (op n)).f q ≫
            ((CochainComplex.shiftFunctorObjXIso I r q (q + r) rfl).hom).app (op n)) ∧
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R) ℤ)
        [I.IsKInjective] (r : ℤ),
        roosι (I⟦r⟧) ≫ (Functor.commShiftIso roosF (self := cC) r).hom.app I =
          (Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I ≫ (roosι I)⟦r⟧') ∧
      (∀ (X I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC t} R) ℤ)
        (q : X ⟶ I) [QuasiIso q] [I.IsKInjective] (r : ℤ),
        ∃ (d : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
            RF.obj (DerivedCategory.Q.{w}.obj X))
          (ds : DerivedCategory.Q.{w}.obj (limit (I⟦r⟧).asFunctor) ≅
            RF.obj (DerivedCategory.Q.{w}.obj (X⟦r⟧))),
          d.hom ≫ RF.map (DerivedCategory.Q.{w}.map q) = η.app I ∧
          ds.hom ≫ RF.map (DerivedCategory.Q.{w}.map (q⟦r⟧')) = η.app (I⟦r⟧) ∧
          ds.hom ≫ RF.map ((DerivedCategory.Q.{w}.commShiftIso r).hom.app X) ≫
              (Functor.commShiftIso RF (self := cR) r).hom.app (DerivedCategory.Q.{w}.obj X) =
            DerivedCategory.Q.{w}.map
                ((Functor.commShiftIso roosLimitFunctor (self := cL) r).hom.app I) ≫
              (DerivedCategory.Q.{w}.commShiftIso r).hom.app (limit I.asFunctor) ≫ d.hom⟦r⟧') := by
  sorry

end CategoryTheory
