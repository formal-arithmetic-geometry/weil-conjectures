/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D8
-/
module
public import Sheaf.Paper.WeilCompletedKoszulProductComparison
import Sheaf.CategoryTheory.StrictRoosDerivation
import Sheaf.AlgebraicGeometry.ProEtaleProductsExact
import Sheaf.CategoryTheory.RingedCechKoszulComparisonOnSite
/-!
# Transporting the explicit Koszul comparison between derived representatives

Source: Stacks Project, Tag 0A0E and sites-cohomology.tex Tag 0941;
the localization universal property for natural transformations.
(blueprint: lem-weil-pbc-completed-fiber-roos-representative-comparison).

The finite construction comparison is used only at the actual termwise transported
complex. All representative transport and its prescribed unit equation are proved here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory
variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
  (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)

private theorem unitComponent_natural {N M : ringedSiteComplex O} (f : N ⟶ M) (m : ℕᵒᵖ) :
    f ≫ ringedKoszulTensorUnitComponent O r b M m =
      ringedKoszulTensorUnitComponent O r b N m ≫
        ((ringedKoszulTensorTower O r b).map f).app m := by
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := Classical.choice (SheafOfModules.tensorClosed O).1
  let := Classical.choice (SheafOfModules.tensorClosed O).2.1
  change f ≫ (MonoidalCategory.rightUnitor M).inv ≫
      (M ◁ ringedKoszulDualUnit O r b m.unop) =
    (MonoidalCategory.rightUnitor N).inv ≫
      (N ◁ ringedKoszulDualUnit O r b m.unop) ≫
        (f ▷ (ringedKoszulDualTower O r b).obj m)
  rw [← Category.assoc, MonoidalCategory.rightUnitor_inv_naturality,
    Category.assoc, MonoidalCategory.whisker_exchange]

private theorem limitUnit_natural {N M : ringedSiteComplex O} (f : N ⟶ M) :
    f ≫ ringedKoszulLimitUnit O r b M =
      ringedKoszulLimitUnit O r b N ≫
        ((lim : (ℕᵒᵖ ⥤ _) ⥤ _).mapHomologicalComplex (.up ℤ)).map
          ((ringedKoszulTensorTowerFunctor O r b).map f) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply limit.hom_ext
  intro m
  simp only [HomologicalComplex.comp_f, Category.assoc,
    Functor.mapHomologicalComplex_map_f]
  change f.f n ≫ limit.lift ((ringedKoszulTensorTowerComplex O r b M).X n)
      (ringedKoszulTensorUnitCone O r b M n) ≫
        limit.π ((ringedKoszulTensorTowerComplex O r b M).X n) m =
    limit.lift ((ringedKoszulTensorTowerComplex O r b N).X n)
      (ringedKoszulTensorUnitCone O r b N n) ≫
        limMap (((ringedKoszulTensorTowerFunctor O r b).map f).f n) ≫
          limit.π ((ringedKoszulTensorTowerComplex O r b M).X n) m
  erw [limMap_π, ← Category.assoc]
  simp only [Category.assoc]
  simp only [limit.lift_π,
    ringedKoszulTensorUnitCone]
  erw [limit.lift_π_assoc]
  exact congrArg (fun g ↦ g.f n) (unitComponent_natural O r b f m)

private theorem representativeUnitTransport
    {C D : Type*} [Category C] [Category D]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    (G : D ⥤ D) (H : C ⥤ D) (e : L ⋙ G ≅ H) (u : L ⟶ H)
    {N P : C} (s : L.obj P ≅ L.obj N) :
    ∃ k : H.obj N ≅ H.obj P, u.app N ≫ k.hom = s.inv ≫ u.app P := by
  let : Localization.Lifting L W L (𝟭 D) := ⟨Functor.rightUnitor L⟩
  let : Localization.Lifting L W H G := ⟨e⟩
  let eta := Localization.liftNatTrans L W L H (𝟭 D) G u
  have heta (K : C) : eta.app (L.obj K) = u.app K ≫ e.inv.app K := by
    rw [Localization.liftNatTrans_app]
    change 𝟙 _ ≫ u.app K ≫ e.inv.app K = _
    simp only [Category.id_comp]
  refine ⟨(e.app N).symm ≪≫ G.mapIso s.symm ≪≫ e.app P, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  change u.app N ≫ e.inv.app N ≫ G.map s.inv ≫ e.hom.app P = _
  rw [← Category.assoc, ← heta]
  have hn := eta.naturality s.inv
  change s.inv ≫ eta.app (L.obj P) = eta.app (L.obj N) ≫ G.map s.inv at hn
  rw [← Category.assoc, ← hn, heta]
  simp [Category.assoc]

private def roosCompletionUnit : 𝟭 (ringedSiteComplex O) ⟶
    ringedKoszulTensorTowerFunctor O r b ⋙ roosF := by
  let eta : 𝟭 (ringedSiteComplex O) ⟶ ringedKoszulTensorTowerFunctor O r b ⋙
      (lim : (ℕᵒᵖ ⥤ _) ⥤ _).mapHomologicalComplex (.up ℤ) :=
    { app := ringedKoszulLimitUnit O r b
      naturality := fun _ _ f ↦ limitUnit_natural O r b f }
  exact eta ≫ Functor.whiskerLeft (ringedKoszulTensorTowerFunctor O r b)
    AlgebraicGeometry.Scheme.completedKoszulTermwiseLimitIso.inv ≫
      Functor.whiskerLeft (ringedKoszulTensorTowerFunctor O r b) roosInclusion

variable [HasDerivedCategory.{w} (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]

private theorem roosCompletion_changeRepresentative
    (D : RingedKoszulLimitPresentation O r b)
    (RF : DerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⥤ ringedSiteDerived O)
    (kappa : roosF ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ RF)
    {N P : ringedSiteComplex O} (s : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj N) :
    ∃ k : DerivedCategory.Q.obj (roosF.obj (ringedKoszulTensorTowerComplex O r b N)) ≅
        DerivedCategory.Q.obj (roosF.obj (ringedKoszulTensorTowerComplex O r b P)),
      DerivedCategory.Q.map ((roosCompletionUnit O r b).app N) ≫ k.hom =
        s.inv ≫ DerivedCategory.Q.map ((roosCompletionUnit O r b).app P) := by
  let T := ringedKoszulTensorTowerFunctor O r b
  let H := T ⋙ roosF ⋙ DerivedCategory.Q
  let G := D.tensorTower ⋙ RF
  let e : DerivedCategory.Q ⋙ G ≅ H :=
    Functor.isoWhiskerRight D.tensorFactors RF ≪≫ Functor.isoWhiskerLeft T kappa.symm
  let u : DerivedCategory.Q ⟶ H := Functor.whiskerRight (roosCompletionUnit O r b)
    DerivedCategory.Q
  exact representativeUnitTransport DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) G H e u s

end CategoryTheory

namespace AlgebraicGeometry.Scheme
universe v

set_option maxHeartbeats 600000 in
-- Checking the two presentations of the exact derived equivalence needs extra elaboration.
/-- The explicit Koszul fiber comparison for every specified derived representative.

Source: Stacks Project, Tag 0A0E and sites-cohomology.tex Tag 0941.
(blueprint: lem-weil-pbc-completed-fiber-roos-representative-comparison).

Proof: the right tensor unitor and tensor functoriality make the maps from a complex
into each Koszul level natural. Limit projections then prove naturality of the ordinary
limit unit. Compose with the inverse termwise-limit comparison and the natural Roos
inclusion to obtain the actual zero-homotopy unit as a natural transformation.

Exact countable products transfer along the module-sheaf equivalence. Strict Roos
derivation gives its descended functor and localization factorization. The existing
single-site Koszul theorem supplies the descended tensor tower. Combining these
factorizations descends the actual composite tensor/Roos functor. Full faithfulness of
precomposition by localization lifts its unit natural transformation. Naturality of
that lifted unit transports the comparison along any supplied representative isomorphism.

Apply the source chain isomorphism at the termwise transported input and localize it.
Naturality of the exact module functor's localization factorization identifies its unit.
Compose with the representative comparison. The inverse/hom identities of the same
factorization leave precisely realization.inv, proving the displayed equation. All these
arguments apply to empty generator lists, zero rings and zero complexes. -/
theorem completed_fiber_roos_comparison
    (X : Scheme.{v}) {A : Type (v + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
    let O := completedCechRing X d
    let F := completedCechDerivedEquiv X d
    let b := fun i ↦ completedCechScalar X d (a i)
    ∀ (P : ringedSiteComplex O)
      (realization : DerivedCategory.Q.obj P ≅ F.functor.obj (DerivedCategory.Q.obj C)),
      let T := ringedKoszulTensorTowerComplex O r b P
      ∃ e : F.functor.obj (DerivedCategory.Q.obj (intrinsicCompletionComplex X d r a C)) ≅
          DerivedCategory.Q.obj (roosF.obj T),
        F.functor.map (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d r a C)) ≫
            e.hom = realization.inv ≫
          DerivedCategory.Q.map (ringedKoszulLimitUnit O r b P ≫
            (completedKoszulTermwiseLimitIso.app T).inv ≫ roosι T) := by
  classical
  dsimp only
  intro P realization
  let O := completedCechRing X d
  let b := fun i ↦ completedCechScalar X d (a i)
  let F := completedCechDerivedEquiv X d
  let G := (completedCechModulesEquiv X d).functor
  let N := (G.mapHomologicalComplex (.up ℤ)).obj C
  let B := ringedSiteModules.{v + 1, v + 1, v + 1, v + 1}
    ((sheafCompose (completedCechTopology X) (forget₂ CommRingCat.{v + 1} RingCat.{v + 1})).obj O)
  let alpha := G.mapDerivedCategoryFactors
  obtain ⟨e, he⟩ := completed_fiber_roos_comparison_on_complex X d r a C
  have : HasExactLimitsOfShape (Discrete ℕ) (pbcModules X (pbcAdicCompletion X d)) :=
    ProEt.products_exact.{v, v + 1} X
      ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{v + 1} RingCat.{v + 1})).obj
        (pbcAdicCompletion X d)) ℕ
  have : HasExactLimitsOfShape (Discrete ℕ) B :=
    HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ) (completedCechModulesEquiv X d)
  obtain ⟨RF, kappa, _, _⟩ := strictRoosDerivation.{v + 1, v + 1, v + 1, v + 2}
    (completedCechTopology X)
    ((sheafCompose (completedCechTopology X) (forget₂ CommRingCat.{v + 1} RingCat.{v + 1})).obj O)
    (fun U x y ↦ @mul_comm (O.obj.obj U) inferInstance x y)
  obtain ⟨D, _, _⟩ := exists_ringed_cech_koszul_comparison_on_site O r b
  let s : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj N :=
    realization ≪≫ alpha.app C
  obtain ⟨k, hk⟩ := CategoryTheory.roosCompletion_changeRepresentative O r b D RF kappa s
  let ec : F.functor.obj (DerivedCategory.Q.obj (intrinsicCompletionComplex X d r a C)) ≅
      DerivedCategory.Q.obj (roosF.obj (ringedKoszulTensorTowerComplex O r b N)) :=
    alpha.app (intrinsicCompletionComplex X d r a C) ≪≫ DerivedCategory.Q.mapIso e
  refine ⟨ec ≪≫ k, ?_⟩
  have hnat := alpha.hom.naturality (intrinsicCompletionComplexUnit X d r a C)
  change F.functor.map (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d r a C)) ≫
      alpha.hom.app (intrinsicCompletionComplex X d r a C) =
    alpha.hom.app C ≫ DerivedCategory.Q.map
      ((G.mapHomologicalComplex (.up ℤ)).map (intrinsicCompletionComplexUnit X d r a C))
    at hnat
  dsimp only [ec, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Category.assoc]
  change F.functor.map (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d r a C)) ≫
    (alpha.hom.app (intrinsicCompletionComplex X d r a C) ≫
      DerivedCategory.Q.map e.hom ≫ k.hom) = _
  rw [← Category.assoc, hnat]
  rw [Category.assoc, ← DerivedCategory.Q.map_comp_assoc, he]
  change alpha.hom.app C ≫
    DerivedCategory.Q.map ((CategoryTheory.roosCompletionUnit O r b).app N) ≫ k.hom = _
  rw [hk]
  simp only [s, Iso.trans_inv, Iso.app_inv, Category.assoc, Iso.hom_inv_id_app_assoc]
  rfl

end AlgebraicGeometry.Scheme
