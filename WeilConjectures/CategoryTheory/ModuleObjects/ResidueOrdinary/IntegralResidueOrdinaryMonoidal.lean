/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueComparisonInterface
public import WeilConjectures.CategoryTheory.Monoidal.Mod.MapIhom
public import WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryMonoidal

/-! # Strong monoidal ordinary pullback for condensed coefficient module objects

Balanced tensor coequalizers give the tensorator, with coherence checked on their
presentation epimorphisms. Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-ordinary-monoidal)
-/

@[expose] public section
universe v u v' u'
open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Bimod.monoidalCategory
namespace CategoryTheory.Mod.ResidueOrdinary
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  {R : C} [MonObj R] [IsCommMonObj R]
/-- The quotient map defining the relative tensor product is linear in its first factor. -/
noncomputable def relativeTensorπ (M N : Mod C R) :
    (Mod.tensorRight R N.X).obj M ⟶ M ⊗ N :=
  homMk (M := (Mod.tensorRight R N.X).obj M) (N := M ⊗ N) (tensorObjπ M N) (by
    change ((α_ R M.X N.X).inv ≫ γ[R,M.X] ▷ N.X) ≫ tensorObjπ M N =
      R ◁ tensorObjπ M N ≫ γ[R,(M ⊗ N).X]
    simpa only [Category.assoc] using (whiskerLeft_tensorπ_smul M N).symm)

/-- The relative tensor product is a cofork of the two action maps on module objects. -/
noncomputable def relativeTensorCofork (M N : Mod C R) :
    Cofork ((tensorRightMap R γ[R,N.X]).app M)
      ((tensorRightRightAct R N.X).app M) :=
  Cofork.ofπ (relativeTensorπ M N) (by
    apply Mod.hom_ext
    change M.X ◁ γ[R,N.X] ≫ tensorObjπ M N =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ tensorObjπ M N
    rw [Category.assoc, tensorObjπ_condition]
    simp only [Category.assoc, Iso.inv_hom_id_assoc])

/-- The tensor cofork is a coequalizer, as can be checked after forgetting the module action. -/
noncomputable def isColimitRelativeTensorCofork (M N : Mod C R) :
    IsColimit (relativeTensorCofork M N) := by
  apply isColimitOfIsColimitCoforkMap (forget R)
  change IsColimit (Cofork.ofπ (tensorObjπ M N) _ :
    Cofork (M.X ◁ γ[R,N.X]) ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X))
  refine Cofork.IsColimit.mk _
    (fun s ↦ coequalizer.desc (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X]) s.π ?_) ?_ ?_
  · have h := s.condition
    change M.X ◁ γ[R,N.X] ≫ s.π =
      ((α_ M.X R N.X).inv ≫ rightAct M ▷ N.X) ≫ s.π at h
    rw [← cancel_epi (α_ M.X R N.X).inv]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm
  · intro s
    exact coequalizer.π_desc _ _
  · intro s m hm
    apply coequalizer.hom_ext (f := rightAct M ▷ N.X)
      (g := (α_ M.X R N.X).hom ≫ M.X ◁ γ[R,N.X])
    exact hm.trans (coequalizer.π_desc _ _).symm

/-- The previously constructed coequalizer tensor functor agrees with the monoidal tensor. -/
noncomputable def relativeTensorRightIso (N : Mod C R) :
    Mod.tensorLeft N ≅ MonoidalCategory.tensorRight N :=
  NatIso.ofComponents
    (fun M ↦ by
      change colimit ((tensorLeftDiagram R N).flip.obj M) ≅ M ⊗ N
      exact HasColimit.isoOfNatIso
        (diagramIsoParallelPair ((tensorLeftDiagram R N).flip.obj M)) ≪≫
        (colimit.isColimit _).coconePointUniqueUpToIso (isColimitRelativeTensorCofork M N)) (by
    intro M M' f
    apply colimit.hom_ext
    intro j
    simp only [id_eq, Iso.trans_hom, tensorLeft, Functor.comp_map, colim_map, Category.assoc,
      ι_colimMap_assoc, HasColimit.isoOfNatIso_ι_hom_assoc]
    cases j <;> apply Mod.hom_ext <;>
      simp [relativeTensorCofork, relativeTensorπ, tensorObjπ_whiskerRight])

lemma tensorπ_leftUnitor (M : Mod C R) :
    tensorObjπ (regular R) M ≫ (λ_ M).hom.hom = γ[R,M.X] := by
  change tensorObjπ (regular R) M ≫
    (Bimod.whiskerRight (toBimodRegularIso (R := R)).hom ((toBimod R).obj M)).hom ≫
      (Bimod.LeftUnitorBimod.hom ((toBimod R).obj M)) = _
  dsimp only [tensorObjπ]
  rw [Bimod.whiskerRight_hom]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one]
  erw [toBimodRegularIso_hom_hom, id_whiskerRight, Category.id_comp]
  exact coequalizer.π_desc _ _

lemma tensorπ_rightUnitor (M : Mod C R) :
    tensorObjπ M (regular R) ≫ (ρ_ M).hom.hom = rightAct M := by
  change tensorObjπ M (regular R) ≫
    (Bimod.whiskerLeft ((toBimod R).obj M) (toBimodRegularIso (R := R)).hom).hom ≫
      (Bimod.RightUnitorBimod.hom ((toBimod R).obj M)) = _
  dsimp only [tensorObjπ]
  rw [Bimod.whiskerLeft_hom]
  erw [ι_colimMap_assoc]
  simp only [parallelPairHom_app_one]
  erw [toBimodRegularIso_hom_hom, whiskerLeft_id, Category.id_comp]
  exact coequalizer.π_desc _ _

lemma relativeTensorRightIso_π (M N : Mod C R) :
    tensorLeftπ N M ≫ (relativeTensorRightIso N).hom.app M = relativeTensorπ M N := by
  simp [relativeTensorRightIso, tensorLeftπ, relativeTensorCofork]

variable {D : Type u'} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]
  {S : D} [MonObj S] [IsCommMonObj S]
  {G : C ⥤ D} [G.Braided]
  (ρ : S ⟶ G.obj R) [IsMonHom ρ] [IsIso ρ]
  [PreservesColimitsOfShape WalkingParallelPair (mapModComap ρ)]

noncomputable def tensorComparison (M N : Mod C R) :
    (mapModComap ρ).obj (M ⊗ N) ≅
      (mapModComap ρ).obj M ⊗ (mapModComap ρ).obj N :=
  (mapModComap ρ).mapIso ((relativeTensorRightIso N).app M).symm ≪≫
    (tensorLeftCompMapModComapIso ρ (fun X Y ↦ Functor.LaxBraided.braided (F := G) X Y) N).app M ≪≫
      (relativeTensorRightIso ((mapModComap ρ).obj N)).app ((mapModComap ρ).obj M)

lemma tensorComparison_π (M N : Mod C R) :
    G.map (tensorObjπ M N) ≫ (tensorComparison ρ M N).hom.hom =
      inv (Functor.LaxMonoidal.μ G M.X N.X) ≫
        tensorObjπ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N) := by
  have h := map_tensorLeftπ_tensorLeftCompMapModComapIso_hom_app ρ
    (fun X Y ↦ Functor.LaxBraided.braided (F := G) X Y) N M
  have hπ := relativeTensorRightIso_π M N
  have hi : relativeTensorπ M N ≫ (relativeTensorRightIso N).inv.app M =
      tensorLeftπ N M := by rw [← hπ, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  dsimp [tensorComparison, Functor.mapIso]
  have hih := congrArg Hom.hom hi
  change tensorObjπ M N ≫ ((relativeTensorRightIso N).inv.app M).hom = _ at hih
  rw [← G.map_comp_assoc, hih]
  have hh := congrArg (fun z ↦ z ≫
    (relativeTensorRightIso ((mapModComap ρ).obj N)).hom.app ((mapModComap ρ).obj M)) h
  simp only [Category.assoc] at hh
  erw [relativeTensorRightIso_π] at hh
  exact congrArg Hom.hom hh

lemma tensorComparison_inv_π (M N : Mod C R) :
    tensorObjπ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N) ≫
        (tensorComparison ρ M N).inv.hom =
      Functor.LaxMonoidal.μ G M.X N.X ≫ G.map (tensorObjπ M N) := by
  rw [← cancel_mono (tensorComparison ρ M N).hom.hom]
  simp only [Category.assoc, ← Mod.comp_hom', Iso.inv_hom_id, Mod.id_hom', Category.comp_id]
  rw [tensorComparison_π, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

lemma tensorComparison_inv_natural_left {M M' : Mod C R} (f : M ⟶ M')
    (N : Mod C R) :
    ((mapModComap ρ).map f ▷ (mapModComap ρ).obj N) ≫ (tensorComparison ρ M' N).inv =
      (tensorComparison ρ M N).inv ≫ (mapModComap ρ).map (f ▷ N) := by
  apply Mod.hom_ext
  rw [← cancel_epi (tensorObjπ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N))]
  simp only [Mod.comp_hom']
  erw [tensorObjπ_whiskerRight_assoc, tensorComparison_inv_π,
    reassoc_of% tensorComparison_inv_π]
  change G.map f.hom ▷ G.obj N.X ≫ Functor.LaxMonoidal.μ G M'.X N.X ≫
      G.map (tensorObjπ M' N) =
    Functor.LaxMonoidal.μ G M.X N.X ≫ G.map (tensorObjπ M N) ≫ G.map (f ▷ N).hom
  rw [Functor.LaxMonoidal.μ_natural_left_assoc, ← G.map_comp, ← tensorObjπ_whiskerRight, G.map_comp]

lemma tensorComparison_inv_natural_right (M : Mod C R) {N N' : Mod C R}
    (f : N ⟶ N') :
    ((mapModComap ρ).obj M ◁ (mapModComap ρ).map f) ≫ (tensorComparison ρ M N').inv =
      (tensorComparison ρ M N).inv ≫ (mapModComap ρ).map (M ◁ f) := by
  apply Mod.hom_ext
  rw [← cancel_epi (tensorObjπ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N))]
  simp only [Mod.comp_hom']
  erw [tensorObjπ_whiskerLeft_assoc, tensorComparison_inv_π,
    reassoc_of% tensorComparison_inv_π]
  change G.obj M.X ◁ G.map f.hom ≫ Functor.LaxMonoidal.μ G M.X N'.X ≫
      G.map (tensorObjπ M N') =
    Functor.LaxMonoidal.μ G M.X N.X ≫ G.map (tensorObjπ M N) ≫ G.map (M ◁ f).hom
  rw [Functor.LaxMonoidal.μ_natural_right_assoc, ← G.map_comp, ← tensorObjπ_whiskerLeft, G.map_comp]

noncomputable def unitComparison :
    (mapModComap ρ).obj (regular R) ≅ regular S :=
  isoMk (asIso ρ).symm (by
    change (ρ ▷ G.obj R ≫ Functor.LaxMonoidal.μ G R R ≫ G.map μ[R]) ≫ inv ρ =
      S ◁ inv ρ ≫ μ[S]
    rw [← cancel_mono ρ, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [Category.assoc, IsMonHom.mul_hom]
    change ρ ▷ G.obj R ≫ Functor.LaxMonoidal.μ G R R ≫ G.map μ[R] =
      S ◁ inv ρ ≫ (ρ ⊗ₘ ρ) ≫ (Functor.LaxMonoidal.μ G R R ≫ G.map μ[R])
    rw [MonoidalCategory.tensorHom_def ρ ρ, Category.assoc]
    rw [whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, IsIso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp])

lemma tensorComparison_left_unitality (M : Mod C R) :
    (λ_ ((mapModComap ρ).obj M)).hom =
      (unitComparison ρ).inv ▷ (mapModComap ρ).obj M ≫
        (tensorComparison ρ (regular R) M).inv ≫ (mapModComap ρ).map (λ_ M).hom := by
  apply Mod.hom_ext
  rw [← cancel_epi (tensorObjπ (regular S) ((mapModComap ρ).obj M))]
  simp only [Mod.comp_hom']
  rw [tensorπ_leftUnitor, tensorObjπ_whiskerRight_assoc]
  erw [reassoc_of% tensorComparison_inv_π]
  change γ[S,((mapModComap ρ).obj M).X] =
    ρ ▷ G.obj M.X ≫ Functor.LaxMonoidal.μ G R M.X ≫ G.map (tensorObjπ (regular R) M) ≫
      G.map (λ_ M).hom.hom
  rw [← G.map_comp, tensorπ_leftUnitor]
  rfl

lemma tensorComparison_right_unitality (M : Mod C R) :
    (ρ_ ((mapModComap ρ).obj M)).hom =
      (mapModComap ρ).obj M ◁ (unitComparison ρ).inv ≫
        (tensorComparison ρ M (regular R)).inv ≫ (mapModComap ρ).map (ρ_ M).hom := by
  apply Mod.hom_ext
  rw [← cancel_epi (tensorObjπ ((mapModComap ρ).obj M) (regular S))]
  simp only [Mod.comp_hom']
  rw [tensorπ_rightUnitor, tensorObjπ_whiskerLeft_assoc]
  erw [reassoc_of% tensorComparison_inv_π]
  change (β_ (G.obj M.X) S).hom ≫
      ρ ▷ G.obj M.X ≫ Functor.LaxMonoidal.μ G R M.X ≫ G.map γ[R,M.X] =
    G.obj M.X ◁ ρ ≫ Functor.LaxMonoidal.μ G M.X R ≫ G.map (tensorObjπ M (regular R)) ≫
      G.map (ρ_ M).hom.hom
  rw [← G.map_comp, tensorπ_rightUnitor]
  change _ = G.obj M.X ◁ ρ ≫ Functor.LaxMonoidal.μ G M.X R ≫
    G.map ((β_ M.X R).hom ≫ γ[R,M.X])
  rw [G.map_comp, Functor.LaxBraided.braided_assoc,
    BraidedCategory.braiding_naturality_right_assoc]

lemma tensorComparison_associativity (M N P : Mod C R) :
    (tensorComparison ρ M N).inv ▷ (mapModComap ρ).obj P ≫
      (tensorComparison ρ (M ⊗ N) P).inv ≫ (mapModComap ρ).map (α_ M N P).hom =
    (α_ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N)
      ((mapModComap ρ).obj P)).hom ≫
      (mapModComap ρ).obj M ◁ (tensorComparison ρ N P).inv ≫
        (tensorComparison ρ M (N ⊗ P)).inv := by
  apply Mod.hom_ext
  rw [← cancel_epi (tensorObjπ
    ((mapModComap ρ).obj M ⊗ (mapModComap ρ).obj N) ((mapModComap ρ).obj P))]
  rw [← cancel_epi (tensorObjπ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N) ▷
    ((mapModComap ρ).obj P).X)]
  simp only [Mod.comp_hom']
  rw [tensorObjπ_whiskerRight_assoc]
  rw [← comp_whiskerRight_assoc]
  erw [tensorComparison_inv_π]
  rw [comp_whiskerRight_assoc]
  erw [reassoc_of% tensorComparison_inv_π]
  erw [Functor.LaxMonoidal.μ_natural_left_assoc]
  rw [show ((mapModComap ρ).map (α_ M N P).hom).hom =
    G.map (α_ M N P).hom.hom from rfl]
  rw [← G.map_comp_assoc, ← G.map_comp]
  rw [Category.assoc, tensorObjπ_associator_hom]
  rw [tensorObjπ_associator_hom_assoc, tensorObjπ_whiskerLeft_assoc]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  erw [tensorComparison_inv_π]
  rw [MonoidalCategory.whiskerLeft_comp_assoc]
  erw [tensorComparison_inv_π]
  erw [Functor.LaxMonoidal.μ_natural_right_assoc]
  simp only [G.map_comp]
  erw [Functor.LaxMonoidal.associativity_assoc]
  rfl

@[instance_reducible]
noncomputable def mapModComapMonoidal : (mapModComap ρ).Monoidal :=
  (Functor.CoreMonoidal.toMonoidal
    { εIso := (unitComparison ρ).symm
      μIso M N := (tensorComparison ρ M N).symm
      μIso_hom_natural_left := tensorComparison_inv_natural_left ρ
      μIso_hom_natural_right M f := tensorComparison_inv_natural_right ρ M f
      associativity := tensorComparison_associativity ρ
      left_unitality := tensorComparison_left_unitality ρ
      right_unitality := tensorComparison_right_unitality ρ })

end CategoryTheory.Mod.ResidueOrdinary

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Use the same ambient braiding as the tensor-presentation and tensor-model interfaces.
attribute [local instance 20000] sheafBraidedCategory

/-- Ordinary pullback for any condensed commutative coefficient ring is strong monoidal. -/
@[instance_reducible] noncomputable def residueOrdinaryUpperStarMonoidal
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (f)^*⟦Λ⟧.Monoidal := by
  let G := (f)^*[Ab.{u + 1}]
  letI : G.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := G) X Y }
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  letI : (Mod.mapModComap ρ).Monoidal := Mod.ResidueOrdinary.mapModComapMonoidal ρ
  exact Functor.Monoidal.transport
    (Functor.isoWhiskerLeft (G.mapMod (condensedRingObj Λ Y))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))).symm

/-- The ordinary integral pullback is strong monoidal, constructed from the ambient
inverse image and the coefficient-pullback isomorphism. -/
@[instance_reducible] noncomputable def residueExchangeOrdinaryPullMonoidal
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (f)^*⟦integralCoeff ℓ E⟧.Monoidal :=
  residueOrdinaryUpperStarMonoidal (integralCoeff ℓ E) f

end AlgebraicGeometry.ProEtale.CondensedRing

section OrdinaryBraiding
open MonObj
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace CategoryTheory.Mod.ResidueOrdinary
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]
  {R : C} [MonObj R] [IsCommMonObj R] {S : D} [MonObj S] [IsCommMonObj S]
  {G : C ⥤ D} [G.Braided] (ρ : S ⟶ G.obj R) [IsMonHom ρ] [IsIso ρ]
  [PreservesColimitsOfShape WalkingParallelPair (mapModComap ρ)]
set_option maxHeartbeats 600000 in
-- Allow elaboration of the explicitly constructed module tensor comparisons.
private theorem mapModComap_braided (M N : Mod C R) :
    let := mapModComapMonoidal ρ
    Functor.LaxMonoidal.μ (mapModComap ρ) M N ≫
        (mapModComap ρ).map (β_ M N).hom =
      (β_ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N)).hom ≫
        Functor.LaxMonoidal.μ (mapModComap ρ) N M := by
  let := mapModComapMonoidal ρ
  apply Mod.hom_ext
  rw [← cancel_epi (tensorObjπ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N))]
  change tensorObjπ _ _ ≫ (tensorComparison ρ M N).inv.hom ≫
      G.map (β_ M N).hom.hom =
    tensorObjπ _ _ ≫ (β_ ((mapModComap ρ).obj M) ((mapModComap ρ).obj N)).hom.hom ≫
      (tensorComparison ρ N M).inv.hom
  erw [reassoc_of% tensorComparison_inv_π, ← G.map_comp]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX, G.map_comp]
  rw [Functor.LaxBraided.braided_assoc]
  erw [Mod.braiding_hom_hom, Mod.tensorObjπ_braidingHomX_assoc, tensorComparison_inv_π]
  rfl
end CategoryTheory.Mod.ResidueOrdinary
attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory
namespace AlgebraicGeometry.ProEtale.CondensedRing
attribute [local instance 20000] sheafBraidedCategory
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
set_option maxHeartbeats 600000 in
-- Allow elaboration of the explicitly constructed module tensor comparisons.
@[instance_reducible] private noncomputable def ordinary_braided
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let := residueOrdinaryUpperStarMonoidal Λ f
    (f)^*⟦Λ⟧.LaxBraided := by
  let G := (f)^*[Ab.{u + 1}]
  let : G.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := G) X Y }
  let ρ := (asIso (condensedPullbackHom Λ f)).inv
  let : (Mod.mapModComap ρ).Monoidal := Mod.ResidueOrdinary.mapModComapMonoidal ρ
  let : (Mod.mapModComap ρ).LaxBraided :=
    { toLaxMonoidal := inferInstance
      braided := Mod.ResidueOrdinary.mapModComap_braided ρ }
  let i := Functor.isoWhiskerLeft (G.mapMod (condensedRingObj Λ Y))
    (Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f))
  let : (G.mapMod (condensedRingObj Λ Y) ⋙
      Mod.extendScalars (condensedPullbackHom Λ f)).Monoidal :=
    Functor.Monoidal.transport i.symm
  let : NatTrans.IsMonoidal i.symm.hom :=
    { unit := by simp [Functor.Monoidal.transport_ε]
      tensor M N := by
        simp [Functor.Monoidal.transport_μ] }
  let h := Functor.LaxBraided.ofNatIso
    (G := G.mapMod (condensedRingObj Λ Y) ⋙
      Mod.extendScalars (condensedPullbackHom Λ f)) i.symm
  exact
    { toLaxMonoidal := (residueOrdinaryUpperStarMonoidal Λ f).toLaxMonoidal
      braided := h.braided }
/-- Canonical ordinary module pullback commutes with the braiding.

The relative tensor coequalizer epimorphism reduces this to braiding compatibility
of ambient sheaf pullback. Transport along the coefficient pullback isomorphism
preserves that equation; invert the monoidal tensorator to obtain the oplax form.

Source: Bhatt--Scholze, Lemma 6.5.9(5); ordinary symmetric monoidal pullback.
(blueprint: new-integral-residue-ordinary-braiding) -/
theorem residueOrdinaryUpperStar_braiding
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)) :
    letI := residueOrdinaryUpperStarMonoidal Λ f
    (f)^*⟦Λ⟧.map (β_ M N).hom ≫ Functor.OplaxMonoidal.δ (f)^*⟦Λ⟧ N M =
      Functor.OplaxMonoidal.δ (f)^*⟦Λ⟧ M N ≫
        (β_ ((f)^*⟦Λ⟧.obj M) ((f)^*⟦Λ⟧.obj N)).hom := by
  let := residueOrdinaryUpperStarMonoidal Λ f
  have h := (ordinary_braided Λ f).braided M N
  rw [← cancel_epi (Functor.LaxMonoidal.μ (f)^*⟦Λ⟧ M N)]
  rw [← Category.assoc, h, Category.assoc, Functor.Monoidal.μ_δ,
    Category.comp_id, Functor.Monoidal.μ_δ_assoc]

end AlgebraicGeometry.ProEtale.CondensedRing

end OrdinaryBraiding
