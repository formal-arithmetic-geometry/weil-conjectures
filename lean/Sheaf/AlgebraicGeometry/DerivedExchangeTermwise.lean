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
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Termwise construction of the derived exchange morphism

Source: Stacks Project, `sites-cohomology.tex`, Lemma 0736 and Remark 07A7;
`derived.tex`, Lemmas 070I, 070K and 0DVC. The comparison between these constructions
is the blueprint's agent-written argument (blueprint: lem-weil-pbc-derived-exchange-termwise).

## Main statements

* `AlgebraicGeometry.derivedExchangeTermwise`: computation on arbitrary K-injective
  resolutions, including resolutions that are not bounded below as complexes.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Etale

/-- The termwise underived exchange followed by a K-injective resolution computes the derived
exchange, using the canonical comparisons with the chosen injective representatives.
The localization is written as `Qh` after the homotopy quotient, canonically isomorphic to `Q`.
The chosen representatives `P` and `P'` and their resolutions `ρ` and `ρ'` are supplied by
`DerivedCategory.Plus.injectiveObjectEquivalence`; `h.1` and `h.2` are the unique homotopy
classes comparing `I` and `J` with them (their existence and uniqueness is the second clause;
the third states the node's claims for that pair). Thus `χ` and `χ'` are precisely the node's
`χ_(I,s)` and `χ_(J,t)`, followed by the existing comparison to the right-derived functor.

Proof (the seven steps of the node):
1. Lift `s⁻¹ ≫ ρ` to the unique comparison of K-injectives and lift its inverse
   (`lem-weil-pbc-kinjective-hom-derived`). Faithfulness makes these homotopy inverses;
   termwise pushforward preserves homotopies (`lem-weil-pbc-termwise-adjunction-homotopy`).
   The resulting `χ` is an isomorphism and is natural for maps of representatives
   (`def-weil-pbc-direct-image`, `lem-weil-pbc-derived-direct-image-triangulated`).
2. Naturality of the derived counit and the termwise comparison expresses the counit on
   `(I,s)` as `s⁻¹ Q(ε_I) φ` (`prop-weil-pbc-derived-inverse-image-adjunction`,
   `def-weil-pbc-derived-inverse-image`, `lem-weil-pbc-termwise-adjunction-homotopy`).
3. On a bounded below complex `N`, the derived unit is `χ Q(f'_*(r) η_N)` for a
   K-injective resolution `r` of `f'⁻¹N` (the same adjunction node and
   `lem-weil-pbc-kinjective-hom-derived`, `def-weil-abstract-derived-category`).
4. The derived square isomorphism on a complex is the localized termwise square
   isomorphism conjugated by the inverse-image comparisons
   (`def-weil-pbc-derived-square-iso`, `def-weil-pbc-derived-inverse-image`).
5. Naturality of the square isomorphism and counit makes the underived exchanges a
   morphism of complexes; the termwise unit gives its adjoint formula
   (`def-weil-pbc-underived-exchange`, `def-weil-pbc-inverse-image`,
   `def-weil-pbc-cartesian-square`, `lem-weil-pbc-termwise-adjunction-homotopy`).
6. For bounded below `I`, substitute steps 2--4 in the mate formula
   (`def-weil-pbc-derived-exchange`); use naturality of `χ` and uniqueness of lifts
   to identify the result with `Q(e)` followed by `χ'`.
7. For arbitrary `I`, compare it with the chosen bounded below injective representative
   by step 1. Transport `j` along the homotopy inverse; naturality of underived exchange
   (`lemma-weil-pbc-underived-exchange-naturality`) and the inverse-image comparisons
   identifies both source comparisons and the same target comparison, giving the equation.
Source: Stacks Project, Lemma 0736 and Remark 07A7; `derived.tex`, Lemmas 070I, 070K, 0DVC;
comparison written by an agent in the blueprint
(blueprint: lem-weil-pbc-derived-exchange-termwise). -/
lemma derivedExchangeTermwise
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
    [QuasiIso j] :
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
    (∀ n : ℤ, ex₀.f n = (Etale.baseChangeMap B sq.toCommSq).app (I.X n)) ∧
    (∃! h : ((q.obj I ⟶ P.obj) × (q'.obj J ⟶ P'.obj)),
      s.hom ≫ DerivedCategory.Qh.map h.1 = ρ ∧
      t ≫ DerivedCategory.Qh.map h.2 = ρ') ∧
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
      IsIso h.1 ∧ IsIso h.2 ∧ IsIso χ ∧ IsIso χ' ∧ IsIso σsrc ∧
      σsrc ≫ DerivedCategory.Plus.ι.map
          ((Etale.derivedBaseChangeMapPlus B sq.toCommSq).app K) =
        DerivedCategory.Qh.map (qY.map e) ≫ χ' := by
  sorry

end AlgebraicGeometry
