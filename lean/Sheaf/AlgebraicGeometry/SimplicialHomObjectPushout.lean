/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SimplicialHomObject
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

/-! # Hom objects and simplicial pushouts

Source: Stacks Project, Lemma 017N (blueprint: lem-weil-pbc-simplicial-hom-object-pushout).
-/

@[expose] public section

universe u₁ w₁ t₁

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace AlgebraicGeometry.Scheme

/-- Hom objects turn admissible simplicial pushouts into pullbacks.
The representing pairs are arbitrary fixed choices from def-weil-pbc-simplicial-hom-object;
the equations specify their unique induced morphisms, without another Hom-object definition.
Source: Stacks Project, Lemma 017N (blueprint: lem-weil-pbc-simplicial-hom-object-pushout).

Proof: (1) Form the fibre product of the two restriction morphisms using
lem-weil-pbc-semi-representable-finite-limits. (2) By the degreewise pushout of
 def-weil-pbc-simplicial-set, D-families over any W are exactly B- and C-families agreeing
on A; the operators preserve the glued family. (3) The representing bijections of
 def-weil-pbc-simplicial-hom-object and def-weil-pbc-representing-object identify this with
pairs of morphisms to HB and HC agreeing in HA. The fibre-product universal property
and Yoneda identify HD with that fibre product, with projections iStar and jStar. -/
theorem simplicialHomObject_pushout_isPullback {X : Scheme.{u₁}}
    {K : SimplicialObject (FormalCoproduct.{w₁} X.Etale)}
    {A B C D : SSet.{t₁}} [A.Finite] [B.Finite] [C.Finite] [D.Finite]
    (hAfin : ∀ n : ℕ, Finite (A.obj (op ⦋n⦌)))
    (hAne : ∀ n : ℕ, Nonempty (A.obj (op ⦋n⦌)))
    (hBfin : ∀ n : ℕ, Finite (B.obj (op ⦋n⦌)))
    (hBne : ∀ n : ℕ, Nonempty (B.obj (op ⦋n⦌)))
    (hCfin : ∀ n : ℕ, Finite (C.obj (op ⦋n⦌)))
    (hCne : ∀ n : ℕ, Nonempty (C.obj (op ⦋n⦌)))
    (hDfin : ∀ n : ℕ, Finite (D.obj (op ⦋n⦌)))
    (hDne : ∀ n : ℕ, Nonempty (D.obj (op ⦋n⦌)))
    (p : A ⟶ B) (q : A ⟶ C) (i : B ⟶ D) (j : C ⟶ D)
    (hpush : CategoryTheory.IsPushout p q i j)
    {HA : FormalCoproduct.{w₁} X.Etale}
    (uA : SimplicialHomFamily K A HA)
    (huA : (simplicialHomFamilyFunctor K A).IsRepresentedBy uA)
    {HB HC HD : FormalCoproduct.{w₁} X.Etale}
    (uB : SimplicialHomFamily K B HB) (uC : SimplicialHomFamily K C HC)
    (uD : SimplicialHomFamily K D HD)
    (huB : (simplicialHomFamilyFunctor K B).IsRepresentedBy uB)
    (huC : (simplicialHomFamilyFunctor K C).IsRepresentedBy uC)
    (huD : (simplicialHomFamilyFunctor K D).IsRepresentedBy uD)
    (iStar : HD ⟶ HB) (jStar : HD ⟶ HC)
    (hi : ∀ n s, iStar ≫ uB.val n s = uD.val n (i.app (op ⦋n⦌) s))
    (hj : ∀ n s, jStar ≫ uC.val n s = uD.val n (j.app (op ⦋n⦌) s))
    (pStar : HB ⟶ HA) (qStar : HC ⟶ HA)
    (hp : ∀ n s, pStar ≫ uA.val n s = uB.val n (p.app (op ⦋n⦌) s))
    (hq : ∀ n s, qStar ≫ uA.val n s = uC.val n (q.app (op ⦋n⦌) s)) :
    CategoryTheory.IsPullback iStar jStar pStar qStar := by sorry

/-- If the common simplicial set is empty, the Hom object of the pushout is a product.
The equations specify the unique induced morphisms of the fixed representing pairs.
Source: Stacks Project, Lemma 017N (blueprint: lem-weil-pbc-simplicial-hom-object-pushout).

Proof: (4) In the family bijection of Lemma 017N, agreement over the empty A is vacuous.
The degreewise pushout is the coproduct, so D-families are arbitrary pairs of B- and
C-families (def-weil-pbc-simplicial-set). Transport this through the representing
bijections (def-weil-pbc-simplicial-hom-object and def-weil-pbc-representing-object).
Finite limits give a product, equivalently a fibre product over the final object
(lem-weil-pbc-semi-representable-finite-limits). Its universal property identifies HD
with that product, with the specified projections iStar and jStar. -/
theorem simplicialHomObject_pushout_empty_isProduct {X : Scheme.{u₁}}
    {K : SimplicialObject (FormalCoproduct.{w₁} X.Etale)}
    {A B C D : SSet.{t₁}} [B.Finite] [C.Finite] [D.Finite]
    (hAempty : ∀ n : ℕ, IsEmpty (A.obj (op ⦋n⦌)))
    (hBfin : ∀ n : ℕ, Finite (B.obj (op ⦋n⦌)))
    (hBne : ∀ n : ℕ, Nonempty (B.obj (op ⦋n⦌)))
    (hCfin : ∀ n : ℕ, Finite (C.obj (op ⦋n⦌)))
    (hCne : ∀ n : ℕ, Nonempty (C.obj (op ⦋n⦌)))
    (hDfin : ∀ n : ℕ, Finite (D.obj (op ⦋n⦌)))
    (hDne : ∀ n : ℕ, Nonempty (D.obj (op ⦋n⦌)))
    (p : A ⟶ B) (q : A ⟶ C) (i : B ⟶ D) (j : C ⟶ D)
    (hpush : CategoryTheory.IsPushout p q i j)
    {HB HC HD : FormalCoproduct.{w₁} X.Etale}
    (uB : SimplicialHomFamily K B HB) (uC : SimplicialHomFamily K C HC)
    (uD : SimplicialHomFamily K D HD)
    (huB : (simplicialHomFamilyFunctor K B).IsRepresentedBy uB)
    (huC : (simplicialHomFamilyFunctor K C).IsRepresentedBy uC)
    (huD : (simplicialHomFamilyFunctor K D).IsRepresentedBy uD)
    (iStar : HD ⟶ HB) (jStar : HD ⟶ HC)
    (hi : ∀ n s, iStar ≫ uB.val n s = uD.val n (i.app (op ⦋n⦌) s))
    (hj : ∀ n s, jStar ≫ uC.val n s = uD.val n (j.app (op ⦋n⦌) s)) :
    Nonempty (IsLimit (BinaryFan.mk iStar jStar)) := by sorry

end AlgebraicGeometry.Scheme
