/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.Paper.SemilinearExchangeCubeData

/-! # Semilinear Frobenius exchange coherence

Assembly of the ordinary, compact-support and refinement cube equations into the
fixed-pair and representative-change laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w a b c d e f
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open CategoryTheory.SuppliedExchangeProjection
open WeilConjectures.PodConstructibleMate
namespace WeilConjectures.PodExchangeCube


/-- Support Frobenius cube equations before passage to fixed pairs.
Source: lem-fix-weil-operations.proof.md, composition and exchange paragraph;
parent proof steps 3--5.
(blueprint: lem-pod-semilinear-rational-support-cubes).
Proof: Base change the chosen model compactifications along Frobenius and relabel
the source structural maps. Apply proper/open horizontal pasting to the resulting cube
and vertical pasting to the composition rectangle, as in fix-lem-exchanges. Its
refinement clause transports both equations to the arbitrary geometric compactifications
in the statement. Insert the displayed normalization formulas for each model anchor
and cancel adjacent comparison inverses. Localize integrally and then pass to common
finite-field representatives; scalar comparisons cancel at intermediate objects.
No compactification is required to descend and no coefficient domain is enlarged. -/
theorem rational_support_cubes
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn)
    (L : Comparisons S.higher.rational
      (fun X : Models D ↦ sfWeilFrobeniusPullback D C.l C.different X.obj E))
    (hL : rationalNormalized D C E S.higher L) :
  (∀ (Q : ModelSquare D) [IsSeparated Q.f.hom.left] [IsSeparated Q.f'.hom.left]
      [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left]
      (c₀ : Compactification Q.f.hom.left) (c₀' : Compactification Q.f'.hom.left)
      (c : Compactification ((fiberModels D).map Q.f).hom.left)
      (c' : Compactification ((fiberModels D).map Q.f').hom.left),
    ∀ K,
      ((iterated (L.support Q.f c₀ c) (L.pull Q.g))).hom.app K ≫ ((changedExchange
        S.higher.rational (S.higher.rationalExchange Q.fiber) c c')).app ((sfWeilFrobeniusPullback
        D C.l C.different Q.X.obj E).obj K) =
        (sfWeilFrobeniusPullback D C.l C.different Q.Y'.obj E).map (((changedExchange
        S.higher.rational (S.higher.rationalExchange Q.fiber) c c')).app K) ≫ ((iterated (L.pull
        Q.g') (L.support Q.f' c₀' c'))).hom.app K) ∧
  (∀ {X Y Z : Models D} (f : X ⟶ Y) (h : Y ⟶ Z)
      [IsSeparated f.hom.left] [IsSeparated h.hom.left]
      (cf₀ : Compactification f.hom.left) (ch₀ : Compactification h.hom.left)
      (c₀ : Compactification (f ≫ h).hom.left)
      (cf : Compactification ((fiberModels D).map f).hom.left)
      (ch : Compactification ((fiberModels D).map h).hom.left)
      (c : Compactification ((fiberModels D).map (f ≫ h)).hom.left),
    ∀ K,
      ((iterated (L.support f cf₀ cf) (L.support h ch₀ ch))).hom.app K ≫ ((supportComposition
        S.higher.rational f h cf ch c).hom).app ((sfWeilFrobeniusPullback D C.l C.different X.obj
        E).obj K) =
        (sfWeilFrobeniusPullback D C.l C.different Z.obj E).map (((supportComposition
        S.higher.rational f h cf ch c).hom).app K) ≫ ((L.support (f ≫ h) c₀ c)).hom.app K) := by
        sorry

end WeilConjectures.PodExchangeCube
