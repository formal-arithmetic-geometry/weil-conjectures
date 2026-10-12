/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! The bounded below exchange comparison. -/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Etale

/-- The exchange comparison equation for a bounded below K-injective source complex.
Source: Stacks Project, sites-cohomology.tex, Lemma 0736 and Remark 07A7;
derived.tex, Lemmas 070I, 070K, 0DVC. The comparison is the agent-written
argument in step 6 of lem-weil-pbc-derived-exchange-termwise.

Proof: let N = g^* f_* I. It is bounded below because the termwise functors
preserve zero objects. Express the derived exchange as the adjoint of the
pullback of the derived counit. Naturality of the derived unit moves the source
comparison inside that adjoint. The counit on I is the localized termwise
counit conjugated by s, by uniqueness of the K-injective comparison. The derived
square isomorphism is the termwise square isomorphism conjugated by the exact
inverse-image comparison maps. Substitute both formulas: the adjoint is now
the localization of j composed with the termwise adjoint of the underived
exchange. Compute the derived unit on N by a bounded below injective resolution
of f'^* N. Uniqueness of maps into the K-injective J identifies the resulting
lift with j composed with that termwise adjoint. Apply f'_* to the equality of
homotopy classes and then localize. Naturality of the right-derived unit and
of the counit of injectiveObjectEquivalence identifies the target comparison
with the displayed χ'. This gives the stated equation.
(blueprint: lem-weil-pbc-derived-exchange-bounded-comparison). -/
lemma derivedExchangeBoundedComparison
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    [I.IsKInjective]
    (s : DerivedCategory.Plus.ι.obj K ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))
    (J : CochainComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    [J.IsKInjective]
    (j : (((g')^*[AddCommGrpCat.{u + 1}]).mapHomologicalComplex (.up ℤ)).obj I ⟶ J)
    [QuasiIso j]
    (n : ℤ) [I.IsStrictlyGE n] :
    let B := AddCommGrpCat.{u + 1}
    let C := Sheaf X.smallEtaleTopology B
    let C' := Sheaf X'.smallEtaleTopology B
    let q := HomotopyCategory.quotient C (.up ℤ)
    let q' := HomotopyCategory.quotient C' (.up ℤ)
    let qY := HomotopyCategory.quotient (Sheaf Y'.smallEtaleTopology B) (.up ℤ)
    let F := (f)_*[B]
    let F' := (f')_*[B]
    let G := (g)^*[B]
    let G' := (g')^*[B]
    let E := DerivedCategory.Plus.injectiveObjectEquivalence C
    let E' := DerivedCategory.Plus.injectiveObjectEquivalence C'
    let K' := G'.mapDerivedCategoryPlus.obj K
    let P := (InjectiveObject.ι C).mapHomotopyCategoryPlus.obj (E.inverse.obj K)
    let P' := (InjectiveObject.ι C').mapHomotopyCategoryPlus.obj (E'.inverse.obj K')
    let ρ := DerivedCategory.Plus.ι.map (E.counitIso.inv.app K)
    let ρ' := DerivedCategory.Plus.ι.map (E'.counitIso.inv.app K')
    let t := G'.mapDerivedCategory.map s.hom ≫
      G'.mapDerivedCategoryFactorsh.hom.app (q.obj I) ≫
      DerivedCategory.Qh.map (q'.map j)
    let ex₀ := (NatTrans.mapHomologicalComplex
      (Etale.baseChangeMap B sq.toCommSq) (.up ℤ)).app I
    let e := ex₀ ≫ (F'.mapHomologicalComplex (.up ℤ)).map j
    ∀ h : ((q.obj I ⟶ P.obj) × (q'.obj J ⟶ P'.obj)),
      s.hom ≫ DerivedCategory.Qh.map h.1 = ρ →
      t ≫ DerivedCategory.Qh.map h.2 = ρ' →
      let χ := DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map h.1) ≫
        DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app P ≫
          F.rightDerivedFunctorPlus.map (E.counitIso.hom.app K))
      let χ' := DerivedCategory.Qh.map ((F'.mapHomotopyCategory (.up ℤ)).map h.2) ≫
        DerivedCategory.Plus.ι.map (F'.rightDerivedFunctorPlusUnit.app P' ≫
          F'.rightDerivedFunctorPlus.map (E'.counitIso.hom.app K'))
      let σsrc := G.mapDerivedCategoryFactorsh.inv.app
        ((F.mapHomotopyCategory (.up ℤ)).obj (q.obj I)) ≫ G.mapDerivedCategory.map χ
      σsrc ≫ DerivedCategory.Plus.ι.map
          ((Etale.derivedBaseChangeMapPlus B sq.toCommSq).app K) =
        DerivedCategory.Qh.map (qY.map e) ≫ χ' := by sorry

end AlgebraicGeometry
