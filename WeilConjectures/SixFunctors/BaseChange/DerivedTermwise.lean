/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Derived

/-!
# The derived base change map on K-injective representatives

For a cartesian square of schemes `g' ≫ f = f' ≫ g` and a bounded below complex `K` of étale
sheaves of abelian groups on `X`, represented by a K-injective complex `I`, together with a
quasi-isomorphism `g'^* I ⟶ J` to a K-injective complex `J` on `X'`, the derived base change map
`g^* R f_* K ⟶ R f'_* g'^* K` is computed by the termwise base change map
`g^* f_* I ⟶ f'_* g'^* I ⟶ f'_* J`
(`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus_eq_termwise`).
(blueprint: `lem-weil-pbc-derived-exchange-termwise`)
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Etale

/-- A morphism in the homotopy category between K-injective complexes is an isomorphism as soon
as its image in the derived category is. -/
private lemma isIso_of_isIso_Qh_map {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {I L : CochainComplex C ℤ} [I.IsKInjective] [L.IsKInjective]
    (f : (HomotopyCategory.quotient C (.up ℤ)).obj I ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L)
    [IsIso (DerivedCategory.Qh.map f)] : IsIso f := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective _ I).2
    (inv (DerivedCategory.Qh.map f))
  refine ⟨g, (CochainComplex.IsKInjective.Qh_map_bijective _ I).1 ?_,
    (CochainComplex.IsKInjective.Qh_map_bijective _ L).1 ?_⟩ <;> simp [hg]

/-- **The derived base change map on K-injective representatives.** Let `K` be a bounded below
complex of étale sheaves on `X`, isomorphic in `D(X)` to a K-injective complex `I` via `s`, and
let `j : g'^* I ⟶ J` be a quasi-isomorphism to a K-injective complex `J` on `X'`. The
comparisons `h = (h₁, h₂)` of `I` and `J` with the chosen injective representatives `P` of `K`
and `P'` of `g'^* K` are unique, and they are isomorphisms in the homotopy categories. Through
the induced isomorphisms `χ : f_* I ≅ R f_* K` and `χ' : f'_* J ≅ R f'_* g'^* K`, the square
```
  g^* f_* I ------e------> f'_* J
      |                      |
      σsrc                   χ'
      ↓                      ↓
  g^* R f_* K --Ex_K--> R f'_* g'^* K
```
commutes, where `e` is the termwise base change map `g^* f_* I ⟶ f'_* g'^* I` followed by
`f'_* j`. (blueprint: `lem-weil-pbc-derived-exchange-termwise`) -/
lemma Etale.derivedBaseChangeMapPlus_eq_termwise
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
  intro B C C' q q' qY F F' G G' E E' K' P P' ρ ρ' t ex₀ e
  have hP : CochainComplex.IsKInjective P.obj.as := by dsimp only [P]; infer_instance
  have hP' : CochainComplex.IsKInjective P'.obj.as := by dsimp only [P']; infer_instance
  have bij₁ := CochainComplex.IsKInjective.Qh_map_bijective (q.obj I) P.obj.as
  have bij₂ := CochainComplex.IsKInjective.Qh_map_bijective (q'.obj J) P'.obj.as
  have : IsIso (DerivedCategory.Qh.map (q'.map j)) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C') j).2 inferInstance
  have : IsIso t := by dsimp only [t]; infer_instance
  refine ⟨?_, fun h h₁ h₂ ↦ ?_⟩
  · obtain ⟨a, ha⟩ := bij₁.2 (inv s.hom ≫ ρ)
    obtain ⟨b, hb⟩ := bij₂.2 (inv t ≫ ρ')
    refine ⟨(a, b), ⟨?_, ?_⟩, fun h ⟨h₁, h₂⟩ ↦
      Prod.ext (bij₁.1 ?_) (bij₂.1 ?_)⟩
    · simp [ha]
    · simp [hb]
    · rw [ha, ← h₁]; simp
    · rw [hb, ← h₂]; simp
  intro χ χ' σsrc
  have : IsIso ρ := by dsimp only [ρ]; infer_instance
  have : IsIso ρ' := by dsimp only [ρ']; infer_instance
  have : IsIso h.1 := by
    have : IsIso (DerivedCategory.Qh.map h.1) := by
      rw [show DerivedCategory.Qh.map h.1 = inv s.hom ≫ ρ by rw [← h₁]; simp]
      infer_instance
    exact isIso_of_isIso_Qh_map (I := I) (L := P.obj.as) h.1
  have : IsIso h.2 := by
    have : IsIso (DerivedCategory.Qh.map h.2) := by
      rw [show DerivedCategory.Qh.map h.2 = inv t ≫ ρ' by rw [← h₂]; simp]
      infer_instance
    exact isIso_of_isIso_Qh_map (I := J) (L := P'.obj.as) h.2
  have : IsIso χ := by
    have : IsIso (F.rightDerivedFunctorPlusUnit.app P) := by dsimp only [P]; infer_instance
    dsimp only [χ]; infer_instance
  have : IsIso χ' := by
    have : IsIso (F'.rightDerivedFunctorPlusUnit.app P') := by dsimp only [P']; infer_instance
    dsimp only [χ']; infer_instance
  have : IsIso σsrc := by dsimp only [σsrc]; infer_instance
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  -- the comparison `φ : g'^* P ⟶ P'` of the injective representatives of `g'^* K`
  let c := E.counitIso.hom.app K
  let c' := E'.counitIso.hom.app K'
  let ιK := HomotopyCategory.Plus.ι C'
  let bcK := NatTrans.mapHomotopyCategory (Etale.baseChangeMap B sq.toCommSq) (.up ℤ)
  obtain ⟨φ, hφ⟩ := (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective
      (G'.mapHomotopyCategoryPlus.obj P) P' hP').2
    (G'.mapDerivedCategoryPlusFactorsh.inv.app P ≫ G'.mapDerivedCategoryPlus.map c ≫
      E'.counitIso.inv.app K')
  have key : (G'.mapHomotopyCategory (.up ℤ)).map h.1 ≫ ιK.map φ = q'.map j ≫ h.2 := by
    refine (CochainComplex.IsKInjective.Qh_map_bijective _ P'.obj.as).1 ?_
    rw [← cancel_epi (G'.mapDerivedCategory.map s.hom ≫
      G'.mapDerivedCategoryFactorsh.hom.app (q.obj I))]
    have e₁ := G'.mapDerivedCategoryFactorsh.hom.naturality h.1
    have e₂ : G'.mapDerivedCategory.map ρ ≫ G'.mapDerivedCategoryFactorsh.hom.app P.obj ≫
        DerivedCategory.Qh.map (ιK.map φ) = ρ' := by
      have := congrArg DerivedCategory.Plus.ι.map (show G'.mapDerivedCategoryPlus.map
          (E.counitIso.inv.app K) ≫ G'.mapDerivedCategoryPlusFactorsh.hom.app P ≫
          DerivedCategory.Plus.Qh.map φ = E'.counitIso.inv.app K' by
        rw [hφ, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
          CategoryTheory.Functor.map_id, id_comp])
      rw [Functor.map_comp, Functor.map_comp,
        Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app] at this
      exact this
    have e₁' : G'.mapDerivedCategory.map (DerivedCategory.Qh.map h.1) ≫
        G'.mapDerivedCategoryFactorsh.hom.app P.obj =
        G'.mapDerivedCategoryFactorsh.hom.app (q.obj I) ≫
          DerivedCategory.Qh.map ((G'.mapHomotopyCategory (.up ℤ)).map h.1) := e₁
    have h₂' := h₂
    simp only [t, assoc] at h₂'
    trans ρ'
    · simp only [Functor.map_comp, assoc]
      rw [← reassoc_of% e₁', ← Functor.map_comp_assoc, h₁, e₂]
    · simp only [Functor.map_comp, assoc]
      exact h₂'.symm
  let Ex := Etale.derivedBaseChangeMapPlus B sq.toCommSq
  -- the square on the injective representative `P`, in `D⁺(Y')`
  have claim₁ : G.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnit.app P ≫
        F.rightDerivedFunctorPlus.map c) ≫ Ex.app K =
      G.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj P) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus
          (Etale.baseChangeMap B sq.toCommSq)).app P ≫ F'.mapHomotopyCategoryPlus.map φ) ≫
        F'.rightDerivedFunctorPlusUnit.app P' ≫ F'.rightDerivedFunctorPlus.map c' := by
    have n₁ : G.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlus.map c) ≫ Ex.app K =
        Ex.app (DerivedCategory.Plus.Qh.obj P) ≫
          F'.rightDerivedFunctorPlus.map (G'.mapDerivedCategoryPlus.map c) :=
      Ex.naturality c
    have n₂ : DerivedCategory.Plus.Qh.map (F'.mapHomotopyCategoryPlus.map φ) ≫
        F'.rightDerivedFunctorPlusUnit.app P' =
        F'.rightDerivedFunctorPlusUnit.app (G'.mapHomotopyCategoryPlus.obj P) ≫
          F'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map φ) :=
      F'.rightDerivedFunctorPlusUnit.naturality φ
    have hφ' : F'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map φ) ≫
        F'.rightDerivedFunctorPlus.map c' =
        F'.rightDerivedFunctorPlus.map (G'.mapDerivedCategoryPlusFactorsh.inv.app P) ≫
          F'.rightDerivedFunctorPlus.map (G'.mapDerivedCategoryPlus.map c) := by
      rw [hφ, ← Functor.map_comp, ← Functor.map_comp, assoc, assoc]
      dsimp only [c']
      rw [Iso.inv_hom_id_app]
      erw [comp_id]
    rw [Functor.map_comp DerivedCategory.Plus.Qh, assoc]
    erw [reassoc_of% n₂]
    rw [hφ', Functor.map_comp, assoc, n₁, Etale.derivedBaseChangeMapPlus_fac_app_assoc]
  -- the square in the homotopy category of `Y'`
  have sqK : (G.mapHomotopyCategory (.up ℤ)).map ((F.mapHomotopyCategory (.up ℤ)).map h.1) ≫
      bcK.app P.obj ≫ (F'.mapHomotopyCategory (.up ℤ)).map (ιK.map φ) =
      qY.map e ≫ (F'.mapHomotopyCategory (.up ℤ)).map h.2 := by
    obtain ⟨a, ha⟩ : ∃ a : I ⟶ P.obj.as, q.map a = h.1 := q.map_surjective _
    have n₅ : (G.mapHomotopyCategory (.up ℤ)).map ((F.mapHomotopyCategory (.up ℤ)).map
        (q.map a)) ≫ bcK.app P.obj =
        qY.map ex₀ ≫ (F'.mapHomotopyCategory (.up ℤ)).map
          ((G'.mapHomotopyCategory (.up ℤ)).map (q.map a)) :=
      bcK.naturality (q.map a)
    rw [← ha, reassoc_of% n₅, ← Functor.map_comp, ha, key]
    simp only [e, Functor.map_comp, assoc]
    rfl
  have n₃ : G.mapDerivedCategory.map (DerivedCategory.Qh.map
      ((F.mapHomotopyCategory (.up ℤ)).map h.1)) ≫
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj P.obj) =
      G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj (q.obj I)) ≫
        DerivedCategory.Qh.map ((G.mapHomotopyCategory (.up ℤ)).map
          ((F.mapHomotopyCategory (.up ℤ)).map h.1)) :=
    G.mapDerivedCategoryFactorsh.hom.naturality _
  have n₄ : DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map
      ((NatTrans.mapHomotopyCategoryPlus (Etale.baseChangeMap B sq.toCommSq)).app P ≫
        F'.mapHomotopyCategoryPlus.map φ)) =
      DerivedCategory.Qh.map (bcK.app P.obj ≫
        (F'.mapHomotopyCategory (.up ℤ)).map (ιK.map φ)) := by
    change DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι _).map _) = _
    rw [Functor.map_comp (HomotopyCategory.Plus.ι _), NatTrans.ι_map_mapHomotopyCategoryPlus_app]
    rfl
  have claim₂ : σsrc ≫ DerivedCategory.Plus.ι.map (Ex.app K) =
      G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj (q.obj I)) ≫
        G.mapDerivedCategory.map (DerivedCategory.Qh.map
          ((F.mapHomotopyCategory (.up ℤ)).map h.1)) ≫
        DerivedCategory.Plus.ι.map (G.mapDerivedCategoryPlus.map
          (F.rightDerivedFunctorPlusUnit.app P ≫ F.rightDerivedFunctorPlus.map c) ≫
            Ex.app K) := by
    dsimp only [σsrc, χ]
    rw [Functor.map_comp DerivedCategory.Plus.ι, Functor.map_comp, assoc, assoc]
    rfl
  rw [claim₂, claim₁, Functor.map_comp DerivedCategory.Plus.ι,
    Functor.map_comp DerivedCategory.Plus.ι, n₄,
    Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app]
  erw [reassoc_of% n₃]
  rw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc, sqK, Functor.map_comp, assoc]

end AlgebraicGeometry
