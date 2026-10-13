/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived

/-!
# The derived base change map on K-injective representatives

For a cartesian square `g' ≫ f = f' ≫ g` of schemes and a bounded below complex `K` of
sheaves on `X`, represented by a K-injective complex `I`, and a K-injective replacement `J` of
`g'^* I`, the derived base change map `g^* R f_* K ⟶ R f'_* g'^* K` is computed termwise by
the underived base change maps `g^* f_* I^n ⟶ f'_* g'^* I^n` followed by `f'_* (g'^* I ⟶ J)`
(blueprint: `lem-weil-pbc-derived-exchange-termwise`).
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry.Etale

/-- **The derived base change map is computed termwise on K-injective representatives.**
Let `s : K ≅ I` identify `K ∈ D⁺(X)` with a K-injective complex `I`, and let `j : g'^* I ⟶ J`
be a quasi-isomorphism to a K-injective complex `J`. There is a unique pair of homotopy
classes `I ⟶ P`, `J ⟶ P'` into the chosen injective models of `K` and `g'^* K` compatible with
`s` and `j`. For such a pair, these maps, the induced identifications `χ : f_* I ≅ R f_*⁺ K`,
`χ' : f'_* J ≅ R f'_*⁺ (g'^* K)` and `σsrc : g^* f_* I ≅ g^* R f_*⁺ K` are isomorphisms, and
under them the derived base change map is the termwise underived base change map
`g^* f_* I ⟶ f'_* g'^* I` followed by `f'_* j`.
(blueprint: `lem-weil-pbc-derived-exchange-termwise`) -/
lemma derivedBaseChangeMapPlus_eq_of_isKInjective
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

end AlgebraicGeometry.Etale
