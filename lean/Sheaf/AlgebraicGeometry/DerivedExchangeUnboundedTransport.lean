/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived

/-! Transport of the exchange formula to arbitrary K-injective representatives. -/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Etale

/-- The bounded comparison formula implies the formula for arbitrary K-injective
representatives of a bounded below derived object.
Source: Stacks Project, sites-cohomology.tex, Lemma 0736 and Remark 07A7;
derived.tex, Lemmas 070I and 070K; step 7 of the agent-written comparison
in lem-weil-pbc-derived-exchange-termwise.

Proof: choose P from injectiveObjectEquivalence, a bounded below complex of
injectives representing K. The comparison h from I to P is invertible in the
homotopy category: lift the inverse of its localized isomorphism by the
K-injective Hom bijection and use injectivity to verify the inverse identities.
Represent a homotopy inverse by a complex map v from P to I. Precompose j with
g'^* v to obtain j_P. This is a quasi-isomorphism since termwise inverse image
preserves homotopies and v is a homotopy equivalence. Apply the assumed bounded
formula to P, its canonical resolution isomorphism and j_P. Naturality of the
underived exchange shows e_P composed with g^* f_* h equals e in the homotopy
category, since v h is homotopic to the identity. Naturality of the exact
inverse-image comparison gives the same equality for source comparisons.
The target resolution isomorphism is unchanged: its expression for P becomes
t after cancelling h v under localization. Uniqueness of the K-injective
comparison to P' therefore gives the same target comparison. Precompose the
bounded equation with Q(g^* f_* h) and substitute these three equalities.
(blueprint: lem-weil-pbc-derived-exchange-unbounded-transport). -/
lemma derivedExchangeUnboundedTransport
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
    (bounded : ∀
    (I₀ : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    [I₀.IsKInjective]
    (s₀ : DerivedCategory.Plus.ι.obj K ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I₀))
    (j₀ : (((g')^*[AddCommGrpCat.{u + 1}]).mapHomologicalComplex (.up ℤ)).obj I₀ ⟶ J)
    [QuasiIso j₀]
    (n : ℤ) [I₀.IsStrictlyGE n],
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
    let t := G'.mapDerivedCategory.map s₀.hom ≫
      G'.mapDerivedCategoryFactorsh.hom.app (q.obj I₀) ≫
      DerivedCategory.Qh.map (q'.map j₀)
    let ex₀ := (NatTrans.mapHomologicalComplex
      (Etale.baseChangeMap B sq.toCommSq) (.up ℤ)).app I₀
    let e := ex₀ ≫ (F'.mapHomologicalComplex (.up ℤ)).map j₀
    ∀ h : ((q.obj I₀ ⟶ P.obj) × (q'.obj J ⟶ P'.obj)),
      s₀.hom ≫ DerivedCategory.Qh.map h.1 = ρ →
      t ≫ DerivedCategory.Qh.map h.2 = ρ' →
      let χ := DerivedCategory.Qh.map ((F.mapHomotopyCategory (.up ℤ)).map h.1) ≫
        DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app P ≫
          F.rightDerivedFunctorPlus.map (E.counitIso.hom.app K))
      let χ' := DerivedCategory.Qh.map ((F'.mapHomotopyCategory (.up ℤ)).map h.2) ≫
        DerivedCategory.Plus.ι.map (F'.rightDerivedFunctorPlusUnit.app P' ≫
          F'.rightDerivedFunctorPlus.map (E'.counitIso.hom.app K'))
      let σsrc := G.mapDerivedCategoryFactorsh.inv.app
        ((F.mapHomotopyCategory (.up ℤ)).obj (q.obj I₀)) ≫ G.mapDerivedCategory.map χ
      σsrc ≫ DerivedCategory.Plus.ι.map
          ((Etale.derivedBaseChangeMapPlus B sq.toCommSq).app K) =
        DerivedCategory.Qh.map (qY.map e) ≫ χ' ) :
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
