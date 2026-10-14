/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S2
-/
module

public import Sheaf.Paper.CechCupResolutionComparisonData
public import Sheaf.Paper.CechCupProduct

/-! # Signed total Cech pairing and its two axes

Source: Stacks Project, Tags 07MB and 0FKV.
(blueprint: lem-sc-cech-cup-signed-axis-pairing).
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The signed Alexander--Whitney pairing descends to total homology and
computes both axis products. Only the chain maps and their component formulas
are required; no comparison isomorphism or sheaf cohomology cup is used.
Source: Stacks Project, Tags 07MB and 0FKV, final comparison diagram.
(blueprint: lem-sc-cech-cup-signed-axis-pairing)

Proof: for summands of bidegrees (r,i) and (s,j), restrict the front and back
Cech sections to the common intersection, apply D.pair r s, and multiply by
(-1)^(i*s). Extend bilinearly over the finite sums in each total degree.
D.restriction identifies restrictions of products with products of restrictions.
The adjacent shared-face terms in the alternating Cech differential cancel;
the remaining faces give the two Cech Leibniz terms. D.leibniz gives the
resolution differential terms, and the sign (-1)^(i*s) matches the total
Leibniz sign (-1)^(r+i). Thus products of cycles are cycles and a product
with a boundary is a boundary, so the pairing descends through both homology
quotients. On alpha images the Cech degrees are zero and the summands are the
global resolution product. On beta images both resolution degrees are zero;
D.augmentation_pair identifies the product with the coefficient Cech product.
The six component equations therefore give the two displayed class formulas.
Empty families, zero complexes and zero inputs cause no exception: the finite
sum and quotient constructions still apply, with the corresponding maps zero. -/
theorem cupCech_signed_axis_pairing {X : Scheme.{v}} {ι : Type v}
    (U : ι → X.Opens) {F G : X.Modules} (D : CupResolutionPairing F G)
    (lalpha : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K ⟶
      (cupCechDouble U D.left.K).total (ComplexShape.up ℕ))
    (lbeta : (cechComplexFunctor U).obj F.presheafModuleCat ⟶
      (cupCechDouble U D.left.K).total (ComplexShape.up ℕ))
    (hlalpha : ∀ n : ℕ, lalpha.f n = moduleCechZero U (D.left.K.X n) ≫
      (cupCechDouble U D.left.K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp))
    (hlbeta : ∀ n : ℕ, lbeta.f n =
      ((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (D.left.augmentation.f 0).val)).f n ≫
        (cupCechDouble U D.left.K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp))
    (ralpha : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K ⟶
      (cupCechDouble U D.right.K).total (ComplexShape.up ℕ))
    (rbeta : (cechComplexFunctor U).obj G.presheafModuleCat ⟶
      (cupCechDouble U D.right.K).total (ComplexShape.up ℕ))
    (hralpha : ∀ n : ℕ, ralpha.f n = moduleCechZero U (D.right.K.X n) ≫
      (cupCechDouble U D.right.K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp))
    (hrbeta : ∀ n : ℕ, rbeta.f n =
      ((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (D.right.augmentation.f 0).val)).f n ≫
        (cupCechDouble U D.right.K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp))
    (talpha : ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K ⟶
      (cupCechDouble U D.target.K).total (ComplexShape.up ℕ))
    (tbeta : (cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat ⟶
      (cupCechDouble U D.target.K).total (ComplexShape.up ℕ))
    (htalpha : ∀ n : ℕ, talpha.f n = moduleCechZero U (D.target.K.X n) ≫
      (cupCechDouble U D.target.K).ιTotal (ComplexShape.up ℕ) n 0 n (by simp))
    (htbeta : ∀ n : ℕ, tbeta.f n =
      ((cechComplexFunctor U).map
        ((PresheafOfModules.forgetToPresheafModuleCat (op ⊤) isTerminalTop.op).map
          (D.target.augmentation.f 0).val)).f n ≫
        (cupCechDouble U D.target.K).ιTotal (ComplexShape.up ℕ) 0 n n (by simp))
    (p q : ℕ) :
    ∃ t : ((cupCechDouble U D.left.K).total (ComplexShape.up ℕ)).homology p →ₗ[Γ(X, ⊤)]
      ((cupCechDouble U D.right.K).total (ComplexShape.up ℕ)).homology q →ₗ[Γ(X, ⊤)]
        ((cupCechDouble U D.target.K).total (ComplexShape.up ℕ)).homology (p + q),
      (∀ (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          t (HomologicalComplex.homologyMap lalpha p (cupCycleClass _ p a))
              (HomologicalComplex.homologyMap ralpha q (cupCycleClass _ q b)) =
            HomologicalComplex.homologyMap talpha (p + q) (cupCycleClass _ (p + q) c)) ∧
      (∀ (a : (((cechComplexFunctor U).obj F.presheafModuleCat).sc
          p).moduleCatLeftHomologyData.K)
        (b : (((cechComplexFunctor U).obj G.presheafModuleCat).sc
          q).moduleCatLeftHomologyData.K)
        (c : (((cechComplexFunctor U).obj (F ⊗ G).presheafModuleCat).sc
          (p + q)).moduleCatLeftHomologyData.K),
        c.val = cechCupCochain U F G p q a.val b.val →
          t (HomologicalComplex.homologyMap lbeta p (cupCycleClass _ p a))
              (HomologicalComplex.homologyMap rbeta q (cupCycleClass _ q b)) =
            HomologicalComplex.homologyMap tbeta (p + q) (cupCycleClass _ (p + q) c)) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
