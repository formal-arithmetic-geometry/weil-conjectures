/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.AlgebraicGeometry.OpenRestrictedComparisonTransport

/-! # Open transport before the coefficient morphism

## References

* [Stacks, Tag 0DJ8], [Stacks, Tag 0DJ9]
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

private theorem compose_comparison_square
    {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {R Q T V : C} {A B : D}
    (bR : A ⟶ H.obj R) (bQ : B ⟶ H.obj Q) (n : A ⟶ B)
    (d : R ⟶ Q) (r : R ⟶ T) (s : Q ⟶ T) (β : T ⟶ V)
    (hd : d ≫ s = r) (hn : bR ≫ H.map d = n ≫ bQ) :
    bR ≫ H.map (r ≫ β) = n ≫ bQ ≫ H.map (s ≫ β) := by
  rw [← hd, Category.assoc, H.map_comp, ← Category.assoc, hn, Category.assoc]

private theorem additive_comparisonIntoPullback_naturality
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (z : X')
    (P Q : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) (hQ : Q.IsKFlatTensor)
    (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (hcQ : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
    (d : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
    let H := comparisonStalkCohomology X' z i ⋙ F
    let a := F.map (comparisonIntoPullback f f' g g' sq z P hcP i)
    let b := F.map (comparisonIntoPullback f f' g g' sq z Q hcQ i)
    ∃ n : (Arrow.mk a).left ≅ (Arrow.mk b).left,
      a ≫ H.map ((derivedPullback g').map d.hom) = n.hom ≫ b := by
  classical
  let := leftAlgebra f g' z
  let := rightAlgebra f f' g g' sq z
  let := (tensorMap f f' g g' sq z).toAlgebra
  let := HasDerivedCategory.standard (ModuleCat.{u} (R f g' z))
  let := HasDerivedCategory.standard (ModuleCat.{u} (B f' z))
  obtain ⟨e, he, _⟩ := exists_comparisonSourceIso f f' g g' sq z P Q d i
  have hn := comparisonIntoPullback_naturality f f' g g' sq z P Q
    hP hQ hcP hcQ d i e he
  let E := ModuleCat.extendScalars.{u, u, u}
    (algebraMap (TensorProduct (R f g' z) (A g' z) (B f' z)) (C z))
  let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk z)) AddCommGrpCat.{u}
  refine ⟨F.mapIso (E.mapIso e), ?_⟩
  simpa only [Functor.map_comp, Functor.comp_map, Functor.mapIso_hom] using
    congrArg F.map hn

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option linter.unusedVariables false in
/-- Open restriction transports the comparison into derived pullback, before any
coefficient morphism or target representative is supplied. The right vertical map
is a natural isomorphism on the entire target derived category (Stacks, Tags 0DJ8, 0DJ9). -/
theorem exists_open_comparisonIntoPullback_transport
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (U : X.Opens)
    (sqU : IsPullback (pullback.snd g' U.ι) (pullback.fst g' U.ι ≫ f') (U.ι ≫ f) g)
    (z : (pullback g' U.ι : Scheme.{u})) (i : ℤ) :
    let F := forget₂ (ModuleCat.{u} (X'.presheaf.stalk (pullback.fst g' U.ι z)))
      AddCommGrpCat.{u}
    let FU := forget₂ (ModuleCat.{u} ((pullback g' U.ι).presheaf.stalk z))
      AddCommGrpCat.{u}
    let H := comparisonStalkCohomology X' (pullback.fst g' U.ι z) i ⋙ F
    let HU := comparisonStalkCohomology (pullback g' U.ι) z i ⋙ FU
    ∃ η : H ≅ derivedPullback (pullback.fst g' U.ι) ⋙ HU,
      ∀ (K : schemeDerivedCategory X)
        (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
        (Q : CochainComplex (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ)
        (hP : P.IsKFlatTensor) (hQ : Q.IsKFlatTensor)
        (hcP : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
        (hcQ : IsIso ((counit (pullback.snd g' U.ι)).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj Q)))
        (eP : DerivedCategory.Q.obj P ≅ K)
        (eQ : DerivedCategory.Q.obj Q ≅ (derivedPullback U.ι).obj K),
      let a := F.map (comparisonIntoPullback f f' g g' sq
        (pullback.fst g' U.ι z) P hcP i)
      let b := FU.map (comparisonIntoPullback (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
        g (pullback.snd g' U.ι) sqU z Q hcQ i)
      let β :=
        ((Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))))
          (pullback.snd g' U.ι) U.ι).hom.app K ≫
        eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
          (pullback.condition (f := g') (g := U.ι)).symm) ≫
        ((Classical.choose (Classical.choose_spec (Classical.choose_spec
          (Classical.choose_spec exists_derivedPullbackComposition))))
          (pullback.fst g' U.ι) g').inv.app K
      ∃ l : (Arrow.mk a).left ≅ (Arrow.mk b).left,
        a ≫ H.map ((derivedPullback g').map eP.hom) ≫
            η.hom.app ((derivedPullback g').obj K) =
          l.hom ≫ b ≫ HU.map ((derivedPullback (pullback.snd g' U.ι)).map eQ.hom ≫ β) := by
  classical
  let η := Classical.choose
    (exists_open_restricted_comparison_transport.{u, w} f f' g g' sq U sqU z i)
  refine ⟨η, ?_⟩
  intro K P Q hP hQ hcP hcQ eP eQ
  let RQ : CochainComplex
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ :=
    ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj P
  have hr := Classical.choose_spec
    (exists_open_restricted_comparison_transport.{u, w} f f' g g' sq U sqU z i)
    K P hP hcP eP
  have hR := Classical.choose hr
  have hr' := Classical.choose_spec hr
  have hcR := Classical.choose hr'
  have hr'' := Classical.choose_spec hr'
  let eR := Classical.choose hr''
  have hr''' := Classical.choose_spec hr''
  let l := Classical.choose hr'''
  have hl := Classical.choose_spec hr'''
  let FU := forget₂ (ModuleCat.{u} ((pullback g' U.ι).presheaf.stalk z))
    AddCommGrpCat.{u}
  let HU := comparisonStalkCohomology (pullback g' U.ι) z i ⋙ FU
  let q := pullback.snd g' U.ι
  let d : DerivedCategory.Q.obj RQ ≅ DerivedCategory.Q.obj Q := eR ≪≫ eQ.symm
  have hnat := additive_comparisonIntoPullback_naturality
    (U.ι ≫ f) (pullback.fst g' U.ι ≫ f') g q sqU z RQ Q hR hQ hcR hcQ d i
  let n := Classical.choose hnat
  have hn := Classical.choose_spec hnat
  refine ⟨l ≪≫ n, ?_⟩
  have hd : (derivedPullback q).map d.hom ≫ (derivedPullback q).map eQ.hom =
      (derivedPullback q).map eR.hom := by
    rw [← Functor.map_comp]
    simp only [d, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  let β :=
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) q U.ι).hom.app K ≫
    eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K)
      (pullback.condition (f := g') (g := U.ι)).symm) ≫
    ((Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))))
      (pullback.fst g' U.ι) g').inv.app K
  have hs := compose_comparison_square HU
    (FU.map (comparisonIntoPullback (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
      g q sqU z RQ hcR i))
    (FU.map (comparisonIntoPullback (U.ι ≫ f) (pullback.fst g' U.ι ≫ f')
      g q sqU z Q hcQ i))
    n.hom ((derivedPullback q).map d.hom) ((derivedPullback q).map eR.hom)
    ((derivedPullback q).map eQ.hom) β hd hn
  exact hl.trans (by
    simpa only [l, FU, HU, q, RQ, eR, β, openRestrictedCompositionMap,
      Category.assoc, Iso.trans_hom] using
      congrArg (fun t ↦ l.hom ≫ t) hs)

end AlgebraicGeometry.SingleComplexBaseChange
