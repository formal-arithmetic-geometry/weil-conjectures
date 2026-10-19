/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionDefs
import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionComparison
import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionResolution
import Sheaf.CategoryTheory.StrictTowerArithmeticRestrictionModel

/-!
# Canonical arithmetic restriction of strict derived towers

Source: Stacks Project, More on Algebra, Tag 0H9K, the two product maps in the proof;
Cohomology on Sites, Tags 0940 and 0941
(blueprint: lem-sp-strict-tower-arithmetic-restriction).
-/

@[expose] public section

set_option autoImplicit false

universe a b w uC vC r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.StrictTowerArithmetic

/-- Canonical arithmetic restriction of the total right derived inverse limit.

Source: Stacks Project, More on Algebra, Tag 0H9K (the maps φ′ and φ″ in its proof),
and Cohomology on Sites, Tags 0940 and 0941
(blueprint: lem-sp-strict-tower-arithmetic-restriction).

The input `RF, η` is the total right derived functor supplied by
`ringedStrictTowerHomotopyLimitOfUniverses`; its two hypotheses just identify that input.
All universes are independent, with modules in a universe containing the small site.
Natural isomorphisms `ρ e he` include naturality for every derived tower morphism.
The first clause fixes the comparison on the ordinary limit units, including every strict
cone (a map to the termwise limit is exactly a strict cone). The second clause makes the
identity case explicit under the canonical identification of restriction by 1 with identity.
The last clause fixes both coordinates of the actual cochain cone map and its derived
identification, so it does not choose a triangulated completion. The localized product
cones are products in the derived category; no exactness of sheaf products is assumed.

Proof plan, following the ten steps of this node:
1. With c(i)=ceil(i/e), expand a tower T to (L_e T)_i=T_c(i). Levelwise exactness
   (`lem-weil-tower-category-levelwise-abelian`) makes L_e exact. Transition composites
   give the adjunction L_e ⊣ r_e, including the initial block before level e.
2. On the small ringed tower site apply `prop-pur-kinjective-resolutions-exist` to obtain
   functorial K-injective resolutions with injective terms. The adjunction and
   `lem-weil-pbc-right-adjoint-preserves-kinjective` make their restrictions K-injective.
   The recorded ringed strict-tower theorem computes both derived limits on these.
3. Ordinary restriction of compatible families has inverse x_i=s_(i,e c(i)) z_c(i).
   Check the transition identities and c(en)=n; these are natural chain isomorphisms.
4. Evaluation is K-injective by `lem-weil-tower-evaluation-kinjective`; apply
   `lem-pc-ringed-space-product-kinjective` to realize the derived products termwise.
5. Extend the finite-prefix tower T_n(J_n) along its monic inclusion into T_(n+1)(J_n).
   Injectivity (`def-sp-injective-resolutions`) gives degreewise sections σ_n of each
   transition of an injective tower, and hence sections of block transitions.
6. Solve x_1=0, x_(i+1)=σ_i(x_i-y_i), so 1-s and its block version are degreewise epi.
   Their kernels are the ordinary limits. Apply
   `lem-weil-degreewise-epi-kernel-cocone-qis` to the kernel maps (0,x), obtaining κ, κe.
7. Product universality gives selection a and finite-block sum b. Telescoping gives
   b(1-s)=(1-s_e)a. The cochain differential then gives the actual cone map (by,ax),
   uniquely determined by its two coordinates; no triangulated completion is used.
8. The strict equation cκ=κe α identifies this map with ordinary restriction α under
   the two quasi-isomorphisms. Thus its localization and the derived comparison are iso.
   Projection to the selected source coordinate gives the asserted projection identity.
9. Both product formulas commute with strict tower maps. By
   `lem-weil-pbc-kinjective-hom-derived`, all derived morphisms are homotopy classes of
   maps of K-injectives. Limits preserve homotopies, so the comparison descends naturally
   and is independent of resolution. For e=1 each block is one term, giving identity.
10. A strict cone gives a compatible family t, with Roos unit (0,t). The cone map sends
    it to (0,a t), the restricted cone unit. This proves the unit equation, and naturality
    gives compatibility of strict squares and their total-limit maps. Only the products
    of evaluated K-injectives and the degreewise splittings were used. -/
theorem strictTowerArithmeticRestriction
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤
      DerivedCategory.{w} (ringedSiteModules.{max uC vC r} R))
    (η : limitComplex (ringedSiteModules.{max uC vC r} R) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RF)
    (_hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)
        (ComplexShape.up ℤ)))
    (_hη : ∀ I, CochainComplex.IsKInjective I → IsIso (η.app I)) :
    ∃ (ρ : ∀ (e : ℕ), 1 ≤ e →
        (RF ≅ derivedRestriction (ringedSiteModules.{max uC vC r} R) e ⋙ RF)),
      (∀ (e : ℕ) (he : 1 ≤ e) X,
        η.app X ≫ (ρ e he).hom.app (DerivedCategory.Q.obj X) ≫
            RF.map ((restriction _ e).mapDerivedCategoryFactors.hom.app X) =
          DerivedCategory.Q.map (limitMap e X) ≫
            η.app ((complexRestriction _ e).obj X)) ∧
      (∀ (e : ℕ) (he : 1 ≤ e) X (K : CochainComplex
          (ringedSiteModules.{max uC vC r} R) ℤ)
          (a : K ⟶ (limitComplex _).obj X),
        (DerivedCategory.Q.map a ≫ η.app X) ≫
            (ρ e he).hom.app (DerivedCategory.Q.obj X) ≫
            RF.map ((restriction _ e).mapDerivedCategoryFactors.hom.app X) =
          DerivedCategory.Q.map (a ≫ limitMap e X) ≫
            η.app ((complexRestriction _ e).obj X)) ∧
      (∃ (ζ : complexRestriction (ringedSiteModules.{max uC vC r} R) 1 ≅ 𝟭 _)
          (ι : derivedRestriction (ringedSiteModules.{max uC vC r} R) 1 ≅ 𝟭 _),
        (∀ X (i : ℤ) (n : ℕ),
          ((ζ.hom.app X).f i).app (op n) =
            (X.X i).map (eqToHom (by simp [index]))) ∧
        (∀ X, ι.hom.app (DerivedCategory.Q.obj X) =
          (restriction _ 1).mapDerivedCategoryFactors.hom.app X ≫
            DerivedCategory.Q.map (ζ.hom.app X)) ∧
        (∀ Z, (ρ 1 (by decide)).hom.app Z ≫ RF.map (ι.hom.app Z) = 𝟙 (RF.obj Z))) ∧
      (∀ (e : ℕ) (_he : 1 ≤ e) X,
        ∃ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (j : X ⟶ I),
          QuasiIso j ∧ I.IsKInjective ∧ (∀ i : ℤ, Injective (I.X i)) ∧
            CochainComplex.IsKInjective ((complexRestriction _ e).obj I) ∧
            QuasiIso ((complexRestriction _ e).map j)) ∧
      (∀ (e : ℕ) (he : 1 ≤ e)
          (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ),
        I.IsKInjective → (∀ i : ℤ, Injective (I.X i)) →
        (∀ n : ℕ, CochainComplex.IsKInjective (I.asFunctor.obj (op n))) ∧
        CochainComplex.IsKInjective ((complexRestriction _ e).obj I) ∧
        Nonempty (IsLimit (DerivedCategory.Q.mapCone
          (limit.cone (Discrete.functor (fun n : ℕ ↦ I.asFunctor.obj (op n)))))) ∧
        Nonempty (IsLimit (DerivedCategory.Q.mapCone
          (limit.cone (Discrete.functor
            (fun n : ℕ ↦ I.asFunctor.obj ((index e).obj (op n))))))) ∧
        boundary I ≫ block e I.asFunctor =
          selection e I.asFunctor ≫ boundary ((complexRestriction _ e).obj I) ∧
        ∃ (κ : (limitComplex _).obj I ⟶ model I)
          (κe : (limitComplex _).obj ((complexRestriction _ e).obj I) ⟶
            model ((complexRestriction _ e).obj I))
          (c : model I ⟶ model ((complexRestriction _ e).obj I))
          (σ : RF.obj (DerivedCategory.Q.obj I) ≅ DerivedCategory.Q.obj (model I))
          (σe : RF.obj (DerivedCategory.Q.obj ((complexRestriction _ e).obj I)) ≅
            DerivedCategory.Q.obj (model ((complexRestriction _ e).obj I))),
          QuasiIso κ ∧ QuasiIso κe ∧ QuasiIso c ∧
          (∀ (i : ℤ) (n : ℕ),
            κ.f i ≫ (CochainComplex.mappingCocone.fst (boundary I)).f i ≫
                (Pi.π (fun n : ℕ ↦ I.asFunctor.obj (op n)) n).f i =
              limit.π (I.X i) (op n)) ∧
          (∀ (i j : ℤ) (h : i + -1 = j),
            κ.f i ≫ (CochainComplex.mappingCocone.snd (boundary I)).v i j h = 0) ∧
          (∀ (i : ℤ) (n : ℕ),
            κe.f i ≫ (CochainComplex.mappingCocone.fst
                (boundary ((complexRestriction _ e).obj I))).f i ≫
                (Pi.π (fun n : ℕ ↦ I.asFunctor.obj ((index e).obj (op n))) n).f i =
              limit.π (((complexRestriction _ e).obj I).X i) (op n)) ∧
          (∀ (i j : ℤ) (h : i + -1 = j),
            κe.f i ≫ (CochainComplex.mappingCocone.snd
              (boundary ((complexRestriction _ e).obj I))).v i j h = 0) ∧
          c ≫ CochainComplex.mappingCocone.fst (boundary ((complexRestriction _ e).obj I)) =
            CochainComplex.mappingCocone.fst (boundary I) ≫ selection e I.asFunctor ∧
          (∀ (i j : ℤ) (h : i + -1 = j),
            c.f i ≫ (CochainComplex.mappingCocone.snd
                (boundary ((complexRestriction _ e).obj I))).v i j h =
              (CochainComplex.mappingCocone.snd (boundary I)).v i j h ≫
                (block e I.asFunctor).f j) ∧
          κ ≫ c = limitMap e I ≫ κe ∧
          η.app I ≫ σ.hom = DerivedCategory.Q.map κ ∧
          η.app ((complexRestriction _ e).obj I) ≫ σe.hom = DerivedCategory.Q.map κe ∧
          (ρ e he).hom.app (DerivedCategory.Q.obj I) ≫
              RF.map ((restriction _ e).mapDerivedCategoryFactors.hom.app I) ≫ σe.hom =
            σ.hom ≫ DerivedCategory.Q.map c ∧
          (∀ n : ℕ,
            (ρ e he).hom.app (DerivedCategory.Q.obj I) ≫
                RF.map ((restriction _ e).mapDerivedCategoryFactors.hom.app I) ≫ σe.hom ≫
                DerivedCategory.Q.map
                  (CochainComplex.mappingCocone.fst
                    (boundary ((complexRestriction _ e).obj I)) ≫
                    Pi.π (fun n : ℕ ↦ I.asFunctor.obj ((index e).obj (op n))) n) =
              σ.hom ≫ DerivedCategory.Q.map
                (CochainComplex.mappingCocone.fst (boundary I) ≫
                  Pi.π (fun n : ℕ ↦ I.asFunctor.obj (op n)) (e * (n + 1) - 1))) ∧
          (∀ (K : CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ)
              (a : K ⟶ (limitComplex _).obj I),
            DerivedCategory.Q.map (a ≫ κ) ≫ DerivedCategory.Q.map c =
              DerivedCategory.Q.map (a ≫ limitMap e I ≫ κe))) := by
  obtain ⟨ρ, hρ, hρa, hρb⟩ := strictTowerArithmeticRestrictionComparison.{w, uC, vC, r}
    J R _hcomm RF η _hRF _hη
  have hres := strictTowerArithmeticRestrictionResolution.{w, uC, vC, r}
    J R _hcomm RF η _hRF _hη
  have hmodel := strictTowerArithmeticRestrictionModel.{w, uC, vC, r}
    J R _hcomm RF η _hRF _hη ρ hρ
  exact ⟨ρ, hρ, hρa, hρb, hres, hmodel⟩

end CategoryTheory.StrictTowerArithmetic
