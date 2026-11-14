/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap
public import WeilConjectures.CategoryTheory.Adjunction.TensorInvertible

/-! Canonical exceptional tensor extraction and its projection/counit coherence. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace CategoryTheory.Adjunction
/-- The inverse of the comparison of two right adjoints is characterized by its transpose. -/
lemma rightAdjointUniq_inv_app_eq {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') {x : D} (u : G'.obj x ⟶ G.obj x)
    (h : F.map u ≫ adj1.counit.app x = adj2.counit.app x) :
    (rightAdjointUniq adj1 adj2).inv.app x = u := by
  refine ext_of_comp_counit (adj := adj1) ?_
  rw [rightAdjointUniq_inv_app, rightAdjointUniq_hom_app_counit, h]


/-- The counit of the equivalence `tensorRightEquivalenceOfTensorIso`. -/
lemma tensorRightEquivalenceOfTensorIso_counit_app {D : Type*} [Category* D] [MonoidalCategory D]
    {N N' : D} (e : N ⊗ N' ≅ 𝟙_ D) (e' : N' ⊗ N ≅ 𝟙_ D) (Z : D) :
    (tensorRightEquivalenceOfTensorIso e e').toAdjunction.counit.app Z =
      (α_ Z N' N).hom ≫ Z ◁ e'.hom ≫ (ρ_ Z).hom :=
  rfl

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) (P : D ⥤ C) [P.Monoidal] {L M : D}
  (π : ∀ (A : C) (N : D), F.obj A ⊗ N ⟶ F.obj (A ⊗ P.obj N)) [∀ A N, IsIso (π A N)]

/-- The inverse of the comparison `G (- ⊗ L) ≅ G (-) ⊗ P L` of
`CategoryTheory.Adjunction.tensorRightCompIsoOfTensorIso` is the tensor map
`CategoryTheory.Adjunction.projectionTensorMap`, provided the projection formula `pf` is given by
projection maps `π` which are natural in the second variable, associative and right unital. -/
lemma tensorRightCompIsoOfTensorIso_inv_app (e : M ⊗ L ≅ 𝟙_ D) (e' : L ⊗ M ≅ 𝟙_ D)
    (pf : F ⋙ tensorRight M ≅ tensorRight (P.obj M) ⋙ F) (hpf : ∀ A, pf.hom.app A = π A M)
    (hr : ∀ (A : C) {N N' : D} (φ : N ⟶ N'),
      F.obj A ◁ φ ≫ π A N' = π A N ≫ F.map (A ◁ P.map φ))
    (hassoc : ∀ (A : C) (N N' : D),
      π A N ▷ N' ≫ π (A ⊗ P.obj N) N' ≫ F.map (α_ _ _ _).hom =
        (α_ _ N N').hom ≫ π A (N ⊗ N') ≫ F.map (A ◁ Functor.OplaxMonoidal.δ P N N'))
    (hunit : ∀ A : C,
      π A (𝟙_ D) ≫ F.map (A ◁ Functor.OplaxMonoidal.η P ≫ (ρ_ A).hom) =
      (ρ_ (F.obj A)).hom)
    (K : D) :
    (adj.tensorRightCompIsoOfTensorIso P e e' pf).inv.app K = adj.projectionTensorMap π K L := by
  have key : π (G.obj K) L ▷ M ≫ π _ M ≫ F.map ((α_ _ _ _).hom ≫ G.obj K ◁
      (Functor.LaxMonoidal.μ P L M ≫ P.map e'.hom ≫ Functor.OplaxMonoidal.η P) ≫
        (ρ_ _).hom) =
      (α_ _ L M).hom ≫ F.obj (G.obj K) ◁ e'.hom ≫ (ρ_ _).hom := by
    rw [Functor.map_comp, reassoc_of% (hassoc (G.obj K) L M), ← Functor.map_comp,
      ← whiskerLeft_comp_assoc, Functor.Monoidal.δ_μ_assoc]
    simp only [whiskerLeft_comp, Functor.map_comp, Category.assoc]
    rw [reassoc_of% (hr (G.obj K) e'.hom).symm, ← Functor.map_comp, hunit]
  have hpf' (A : C) : pf.inv.app A = inv (π A M) := by
    refine IsIso.eq_inv_of_hom_inv_id ?_
    rw [← hpf, Iso.hom_inv_id_app]
  have hn : (tensorRight (P.obj M) ⋙ F).map (adj.projectionTensorMap π K L) ≫
      pf.inv.app (G.obj (K ⊗ L)) =
        inv (π _ M) ≫ F.map (adj.projectionTensorMap π K L) ▷ M := by
    rw [← hpf']
    exact pf.inv.naturality _
  have hA : ((adj.comp (tensorRightEquivalenceOfTensorIso e e').toAdjunction).ofNatIsoLeft
      pf).counit.app K = pf.inv.app (G.obj (K ⊗ L)) ≫ adj.counit.app (K ⊗ L) ▷ M ≫
        (α_ K L M).hom ≫ K ◁ e'.hom ≫ (ρ_ K).hom := by
    erw [ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app, comp_counit_app,
      tensorRightEquivalenceOfTensorIso_counit_app]
    rfl
  have hB : ((tensorRightEquivalenceOfTensorIso
      (Functor.Monoidal.μIso P M L ≪≫ P.mapIso e ≪≫ (Functor.Monoidal.εIso P).symm)
      (Functor.Monoidal.μIso P L M ≪≫ P.mapIso e' ≪≫
        (Functor.Monoidal.εIso P).symm)).toAdjunction.comp adj).counit.app K =
      F.map ((α_ _ _ _).hom ≫ G.obj K ◁
        (Functor.LaxMonoidal.μ P L M ≫ P.map e'.hom ≫ Functor.OplaxMonoidal.η P) ≫
          (ρ_ _).hom) ≫ adj.counit.app K := by
    erw [comp_counit_app, tensorRightEquivalenceOfTensorIso_counit_app]
    rfl
  refine rightAdjointUniq_inv_app_eq _ _ _ ?_
  rw [hA, hB, ← Category.assoc, hn, Category.assoc, ← comp_whiskerRight_assoc,
    map_projectionTensorMap_comp_counit,
    comp_whiskerRight_assoc]
  erw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality,
    ← reassoc_of% key]
  simp


end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Etale
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
/-- The co-projection comparison for the exceptional inverse image is the mate of the
lower-shriek right-adjoint tensor map. -/
theorem exceptionalCoprojectionMate
    (K L M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (e : ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj M).obj L ≅ constantComplex Λ Y)
    (e' : ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj L).obj M ≅ constantComplex Λ Y) :
    (derivedTensorRightCompRightDerivedUpperShriekIso Λ f L M e e').inv.app K =
      lowerShriekRightAdjointTensorMap (rightDerivedUpperShriekAdjunction Λ f) K L := by
  sorry
end AlgebraicGeometry.Etale
