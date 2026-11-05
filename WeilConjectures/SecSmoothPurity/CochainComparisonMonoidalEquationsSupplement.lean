/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.SecSmoothPurity.ModuleTensorMonoidalEquations
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators

/-! # Monoidal equations for the canonical cochain comparison

Source: Stacks Project, sites-modules.tex, Tag 03EL, and
sites-cohomology.tex, Tag 07A4.
(blueprint: lem-pur-cochain-comparison-monoidal-equations)
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe w uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.CochainPullback
set_option autoImplicit false
set_option Elab.async false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
attribute [local instance] HomologicalComplex.monoidalCategoryStruct

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}

section Generic
variable {A : Type uE} [Category.{vE} A] [MonoidalCategory A]
  {B : Type uD} [Category.{vD} B] [MonoidalCategory B]

private theorem oplax_equations (F : A ⥤ B) [F.OplaxMonoidal]
    (c : ∀ X Y : A, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (e : F.obj (𝟙_ A) ≅ 𝟙_ B)
    (hc : ∀ X Y, Functor.OplaxMonoidal.δ F X Y = (c X Y).hom)
    (he : Functor.OplaxMonoidal.η F = e.hom) :
    (∀ (X Y X' Y' : A) (a : X ⟶ X') (b : Y ⟶ Y'),
      F.map (a ⊗ₘ b) ≫ (c X' Y').hom = (c X Y).hom ≫ (F.map a ⊗ₘ F.map b)) ∧
    (∀ X Y Z : A,
      F.map (α_ X Y Z).hom ≫ (c X (Y ⊗ Z)).hom ≫ (𝟙 _ ⊗ₘ (c Y Z).hom) =
      (c (X ⊗ Y) Z).hom ≫ ((c X Y).hom ⊗ₘ 𝟙 _) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom) ∧
    (∀ X : A, F.map (λ_ X).hom =
      (c (𝟙_ A) X).hom ≫ (e.hom ⊗ₘ 𝟙 _) ≫ (λ_ (F.obj X)).hom) ∧
    (∀ X : A, F.map (ρ_ X).hom =
      (c X (𝟙_ A)).hom ≫ (𝟙 _ ⊗ₘ e.hom) ≫ (ρ_ (F.obj X)).hom) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X Y X' Y' a b
    rw [← hc, ← hc]
    exact (Functor.OplaxMonoidal.δ_natural F a b).symm
  · intro X Y Z
    rw [← hc, ← hc, ← hc, ← hc]
    simpa only [tensorHom_id, id_tensorHom] using
      (Functor.OplaxMonoidal.associativity F X Y Z).symm
  · intro X
    rw [← hc, ← he]
    simpa only [tensorHom_id] using (Functor.OplaxMonoidal.left_unitality_hom F X).symm
  · intro X
    rw [← hc, ← he]
    simpa only [id_tensorHom] using (Functor.OplaxMonoidal.right_unitality_hom F X).symm

end Generic

-- The graded tensor coproduct choices are shared throughout this module.
private theorem gradedTensorLeftR (X Y Z : GradedObject ℤ (Modules R)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := inferInstance
private theorem gradedTensorLeftS (X Y Z : GradedObject ℤ (Modules S)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := inferInstance
private theorem gradedTensorRightR (X Y Z : GradedObject ℤ (Modules R)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := inferInstance
private theorem gradedTensorRightS (X Y Z : GradedObject ℤ (Modules S)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := inferInstance
attribute [local instance] gradedTensorLeftR gradedTensorLeftS gradedTensorRightR
  gradedTensorRightS

set_option maxHeartbeats 80000 in
-- Normalize the uniquely determined module unit without unfolding the sheaf tensor.
private theorem module_right_unit (f : RingedPullback R S) (k : Comparison f)
    (M : Modules R) :
    (k.mu M (𝟙_ _)).hom ≫ (𝟙 _ ⊗ₘ (moduleUnit f k).hom) ≫
      (ρ_ (f.L.obj M)).hom = f.L.map (ρ_ M).hom :=
  (Classical.choose_spec
    (SheafOfModules.CochainTensorComparison.canonicalRingedTensorComparison_unit
      R S f.RI f.uInv f.I f.coefficient f.L f.hobj f.hmap k)).1 M

attribute [local irreducible] SheafOfModules.monoidalCategory

@[reassoc]
private theorem comparison_ι (f : RingedPullback R S) (k : Comparison f)
    (P Q : Complex R) (p q n : ℤ) (hpq : p + q = n) :
    f.L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n hpq) ≫
        (comparison f k P Q).hom.f n =
      (k.mu (P.X p) (Q.X q)).hom ≫ CochainComplex.ιMapBifunctor
        ((pull f).obj P) ((pull f).obj Q) (curriedTensor (Modules S)) p q n hpq := by
  apply (cancel_mono ((comparison f k P Q).inv.f n)).1
  simp only [Category.assoc, ← HomologicalComplex.comp_f,
    Iso.hom_inv_id, HomologicalComplex.id_f]
  change _ = (k.mu (P.X p) (Q.X q)).hom ≫ _ ≫
    (tensorPullbackTotal f.L k.mu k.naturality P Q).f n
  simp only [tensorPullbackTotal, tensorPullbackTotalComponent,
    HomologicalComplex.ι_mapBifunctorDesc, Iso.hom_inv_id_assoc]
  exact Category.comp_id _

-- Work only with the normalized total comparison, before introducing lifted instances.
-- Assemble the ordinary structure and identify its total comparison.

private theorem comparison_braiding (f : RingedPullback R S) (k : Comparison f)
    (P Q : Complex R) :
    (pull f).map (CochainComplex.Monoidal.braiding P Q).hom ≫ (comparison f k Q P).hom =
      (comparison f k P Q).hom ≫
        (CochainComplex.Monoidal.braiding ((pull f).obj P) ((pull f).obj Q)).hom := by
  let := f.moduleAdj.isLeftAdjoint
  have hb := cochainModuleTensorBraiding f k
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map f.L
  intro p q hpq
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  have h₁ := CochainComplex.Monoidal.ι_braiding_hom (K := P) (L := Q) p q n hpq
  have h₂ := CochainComplex.Monoidal.ι_braiding_hom
    (K := (pull f).obj P) (L := (pull f).obj Q) p q n hpq
  erw [← f.L.map_comp_assoc, h₁]
  rw [f.L.map_zsmul, Preadditive.zsmul_comp, f.L.map_comp, Category.assoc]
  erw [comparison_ι f k Q P q p n ((add_comm q p).trans hpq)]
  erw [comparison_ι_assoc f k P Q p q n hpq, h₂]
  simp only [Preadditive.comp_zsmul]
  change ((p * q).negOnePow : ℤ) •
    (f.L.map (β_ (P.X p) (Q.X q)).hom ≫ (k.mu (Q.X q) (P.X p)).hom ≫ _) = _
  rw [← Category.assoc, hb]
  simp only [Category.assoc]
  rfl

/-- The actual naturality, reassociation, Koszul-symmetry and action-unit equations.
Source: Stacks 03EL and 07A4 (blueprint: def-pur-cochain-tensor-coherence-data). -/
def IsCoherent (f : RingedPullback R S) (k : Comparison f) : Prop :=
  (∀ (P Q P' Q' : Complex R) (a : P ⟶ P') (b : Q ⟶ Q'),
    (pull f).map (a ⊗ₘ b) ≫ (comparison f k P' Q').hom =
      (comparison f k P Q).hom ≫ ((pull f).map a ⊗ₘ (pull f).map b)) ∧
  (∀ (P Q H : Complex R),
    (pull f).map (α_ P Q H).hom ≫ (comparison f k P (Q ⊗ H)).hom ≫
      (𝟙 _ ⊗ₘ (comparison f k Q H).hom) =
    (comparison f k (P ⊗ Q) H).hom ≫ ((comparison f k P Q).hom ⊗ₘ 𝟙 _) ≫
      (α_ ((pull f).obj P) ((pull f).obj Q) ((pull f).obj H)).hom) ∧
  (∀ (P Q : Complex R),
    (pull f).map (CochainComplex.Monoidal.braiding P Q).hom ≫
      (comparison f k Q P).hom = (comparison f k P Q).hom ≫
      (CochainComplex.Monoidal.braiding ((pull f).obj P) ((pull f).obj Q)).hom) ∧
  (∀ (P : Complex R), (pull f).map (λ_ P).hom =
    (comparison f k (𝟙_ _) P).hom ≫ ((unit f k).hom ⊗ₘ 𝟙 _) ≫
      (λ_ ((pull f).obj P)).hom) ∧
  (∀ (P : Complex R), (pull f).map (ρ_ P).hom =
    (comparison f k P (𝟙_ _)).hom ≫ (𝟙 _ ⊗ₘ (unit f k).hom) ≫
      (ρ_ ((pull f).obj P)).hom)

/-- Associativity, Koszul symmetry and both action units of the canonical cochain
comparison. Source: Stacks 03EL and 07A4, the ordinary comparison and its total.
(blueprint: lem-pur-cochain-comparison-monoidal-equations).

Proof: test associativity on every triple homogeneous tensor. Both routes take
s tensor ((x tensor y) tensor z) to (s tensor x) tensor
((1 tensor y) tensor (1 tensor z)). The ordinary tensor universal property and
scalar-extension balancing imply equality before taking totals. The total
associator has the ordinary associator on each triple summand; coproduct
extensionality gives equality in every degree. For the braiding, both routes
swap the two module factors and insert the same units; the two total maps have
the same sign (-1)^(p*q), preserved by the additive pullback functor. For the
unit equations, the canonical module unit is scalar multiplication, as fixed
by canonicalRingedTensorComparison_unit. Both ordinary routes send
s tensor (r tensor x), respectively s tensor (x tensor r), to the same
scalar multiple of 1 tensor x. In total degree n the unit is concentrated
in degree zero, so its only nonzero summand is (0,n), respectively (n,0).
The single-complex identification in unit is exactly this identification.
Coproduct extensionality proves both unit equations. No finite support or
flatness is used. Zero rings, zero complexes and zero summands obey the same
formulas. -/
theorem cochainComparison_monoidal (f : RingedPullback R S) (k : Comparison f) :
    IsCoherent f k := by
  have ha := cochainModuleTensorAssociativity f k
  have hb := cochainModuleTensorBraiding f k
  let := f.moduleAdj.isLeftAdjoint
  have hr (M : Modules R) :
      (k.mu M (𝟙_ _)).hom ≫ (𝟙 _ ⊗ₘ (moduleUnit f k).hom) ≫
        (ρ_ (f.L.obj M)).hom = f.L.map (ρ_ M).hom :=
    module_right_unit f k M
  have hl (M : Modules R) :
      f.L.map (λ_ M).hom = (k.mu (𝟙_ _) M).hom ≫
        ((moduleUnit f k).hom ⊗ₘ 𝟙 _) ≫ (λ_ (f.L.obj M)).hom := by
    calc
      _ = f.L.map (β_ (𝟙_ _) M).hom ≫ f.L.map (ρ_ M).hom := by
        rw [← f.L.map_comp, braiding_rightUnitor]
      _ = f.L.map (β_ (𝟙_ _) M).hom ≫ (k.mu M (𝟙_ _)).hom ≫
          (𝟙 _ ⊗ₘ (moduleUnit f k).hom) ≫ (ρ_ (f.L.obj M)).hom := by
        rw [hr]
      _ = (k.mu (𝟙_ _) M).hom ≫ (β_ (f.L.obj (𝟙_ _)) (f.L.obj M)).hom ≫
          (𝟙 _ ⊗ₘ (moduleUnit f k).hom) ≫ (ρ_ (f.L.obj M)).hom := by
        rw [← Category.assoc, ← Category.assoc, hb, Category.assoc, Category.assoc]
      _ = _ := by
        rw [← BraidedCategory.braiding_naturality_assoc,
          braiding_rightUnitor]
  let op : f.L.OplaxMonoidal :=
    { η := (moduleUnit f k).hom
      δ M N := (k.mu M N).hom
      δ_natural_left b N := by
        simpa only [Functor.map_id, tensorHom_id] using (k.naturality b (𝟙 N)).symm
      δ_natural_right M b := by
        simpa only [Functor.map_id, id_tensorHom] using (k.naturality (𝟙 M) b).symm
      oplax_associativity M N H := by simpa only [tensorHom_id, id_tensorHom] using ha M N H
      oplax_left_unitality M := by
        apply (cancel_epi (f.L.map (λ_ M).hom)).1
        simp only [← f.L.map_comp_assoc, Iso.hom_inv_id, f.L.map_id, Category.id_comp]
        rw [hl M, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        simp only [tensorHom_id]
      oplax_right_unitality M := by
        apply (cancel_epi (f.L.map (ρ_ M).hom)).1
        simp only [← f.L.map_comp_assoc, Iso.hom_inv_id, f.L.map_id, Category.id_comp]
        rw [← hr M, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
        simp only [id_tensorHom] }
  let core : f.L.CoreMonoidal :=
    Functor.CoreMonoidal.mk' (moduleUnit f k).symm (fun M N ↦ (k.mu M N).symm)
      (Functor.OplaxMonoidal.δ_natural_left f.L)
      (Functor.OplaxMonoidal.δ_natural_right f.L)
      (Functor.OplaxMonoidal.associativity f.L)
      (Functor.OplaxMonoidal.left_unitality f.L)
      (Functor.OplaxMonoidal.right_unitality f.L)
  let : f.L.Monoidal := core.toMonoidal
  let cop : (pull f).OplaxMonoidal := inferInstance
  have hd (P Q : Complex R) : Functor.OplaxMonoidal.δ (pull f) P Q =
      ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) f.L).app P).app Q := by
    rw [Functor.mapCochainComplex_δ]
  have hu : Functor.OplaxMonoidal.η (pull f) = (unit f k).hom := by
    rw [Functor.mapCochainComplex_η]
    rfl
  clear_value cop
  have hc (P Q : Complex R) :
      Functor.OplaxMonoidal.δ (pull f) P Q = (comparison f k P Q).hom := by
    apply (cancel_mono (comparison f k P Q).inv).1
    ext n : 1
    apply HomologicalComplex.mapBifunctor.hom_ext_of_map f.L
    intro p q hpq
    simp only [HomologicalComplex.comp_f]
    rw [hd]
    simp only [Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
      HomologicalComplex.mapBifunctorComparison_f]
    erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
    simp only [HomologicalComplex.mapBifunctorComparisonApp,
      Functor.OplaxMonoidal.δNatTrans_app_app]
    change (k.mu (P.X p) (Q.X q)).hom ≫ _ ≫
      (tensorPullbackTotal f.L k.mu k.naturality P Q).f n = _
    simp only [tensorPullbackTotal, tensorPullbackTotalComponent,
      HomologicalComplex.ι_mapBifunctorDesc, Iso.hom_inv_id_assoc]
    simp only [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
    exact (Category.comp_id _).symm
  obtain ⟨hn, ha, hl, hr⟩ := oplax_equations (pull f) (comparison f k) (unit f k) hc hu
  refine ⟨hn, ha, ?_, hl, hr⟩
  exact comparison_braiding f k

end CategoryTheory.CochainPullback
