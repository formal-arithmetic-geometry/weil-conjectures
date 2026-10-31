/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSystemProjectionData
public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement

/-! # Presentation independence of normalized coefficient projection

Source: Zheng, Constructions 2.26 and 5.15, Lemma 5.16; Stacks Project, Tag 0GL6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

/-- The normalized coefficient projection has the same evaluation, composition and
unit formulas for every presentation of the actual system operations.
Source: Zheng, Constructions 2.26 and 5.15, Lemma 5.16; Stacks Project, Tag 0GL6
(blueprint: lem-pur-etale-system-projection-presentation-coherence).

Proof: Choose the normalized reference presentation and its laws from
etaleSystemCoefficientProjection. The structural direct-image maps of it and t agree
on constant generators, hence on all sections by sheafification. Thus their ordinary
pushforwards agree. Uniqueness of left adjoints compares the inverse images and open
extensions, compatibly with their units and counits. The prescribed ordinary restriction
and evaluation squares commute with these comparisons, since their section maps are
identities. Their inverse-image mates, exact localizations and derived geometric mates
therefore commute as well. Uniqueness of scalar left adjoints compares the normalized
scalar models. Paste these commuting squares to transport the reference evaluated
projection formula to the first equation for t.
For two coefficient maps, restriction composes by its identity-on-sections comparison.
Uniqueness of scalar left adjoints identifies the resulting extension comparison with
the displayed balanced associators. Mate pasting for the ordinary proper/open squares,
then exact localization and the derived-mate equations, conjugates the two projection
words to the reference words. Transport the reference composition law and cancel
consecutive inverse comparisons, obtaining the second equation on entire derived
categories. For identity coefficients the restriction unit has identity section maps;
the same comparisons preserve the scalar adjunction unit. Transporting the reference
projection unit law and cancelling the inverse comparisons gives the third equation.
These arguments do not infer equality of morphisms from equality after evaluation,
and do not cancel a nonzero scalar or assume a positive rank. -/
theorem etaleSystemProjectionPresentationCoherence
    (k : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) (hl : l.Prime) (hlp : l ≠ k.p)
    (X Y : Over (Spec (CommRingCat.of k.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (f : X ⟶ Y) [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (c : Compactification f.left) (t : Theory c l) :
      (∀ (B C : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (n : ℕ)
        (M : Derived X.left B.rings),
        (scalarExtension (a.app (op n)).hom Y.left).map
            ((t.supportEvaluation B n).iso.inv.app M) ≫
          (t.scalarEvaluationY a n).iso.inv.app ((t.support B).F.obj M) ≫
          (t.evaluationY C n).E.map ((t.q a).app M) ≫
          (t.supportEvaluation C n).iso.hom.app ((t.scalarX a).model.T.obj M) ≫
          (rightDerivedLowerShriekOfCompactification
            (ModuleCat.{u + 1} (C.rings.obj (op n))) c).map
              ((t.scalarEvaluationX a n).iso.hom.app M) =
          (compactScalarMap (a.app (op n)).hom c).app ((t.evaluationX B n).E.obj M)) ∧
      (∀ (B C D : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings),
        t.q (a ≫ b) = t.path a b) ∧
      (∀ (B : Coefficients.{u} l) (M : Derived X.left B.rings),
        (t.q (𝟙 B.rings)).app M ≫
          (t.support B).F.map ((unit X.left B.rings (t.scalarX (𝟙 B.rings))).hom.app M) =
        (unit Y.left B.rings (t.scalarY (𝟙 B.rings))).hom.app ((t.support B).F.obj M)) := by
  sorry

end AlgebraicGeometry.Etale.SystemProjection
