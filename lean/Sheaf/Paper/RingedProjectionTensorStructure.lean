/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.Paper.RingedProjectionCoherenceData
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Paper.RingedProjectionPullbackComparisons
import Sheaf.Paper.RingedProjectionTensorCompatibility

/-! # Canonical tensor constraints and normalized pullback comparisons

Source: Stacks Project, Tags 06YS, 06YU, 07A4, 0D6D and 0FPI.
-/

@[expose] public noncomputable section

set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w u₁ v₁

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.ProjectionCoherence

private theorem complexSymmetry_involutive
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasZeroObject C]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C]
    [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C]
    (P Q : CochainComplex C ℤ) :
    (CochainComplex.Monoidal.braiding P Q).hom ≫
      (CochainComplex.Monoidal.braiding Q P).hom = 𝟙 _ := by
  ext n : 1
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
  rw [← Category.assoc, CochainComplex.Monoidal.ι_braiding_hom]
  simp only [Preadditive.zsmul_comp, Category.assoc]
  rw [CochainComplex.Monoidal.ι_braiding_hom]
  simp only [Preadditive.comp_zsmul, smul_smul]
  rw [mul_comm q p]
  simp only [curriedTensor_obj_obj, Int.units_coe_mul_self,
    SymmetricCategory.symmetry_assoc, one_smul]
  erw [Category.comp_id]

private theorem totalSymmetry_involutive (A : RingedTensorCorner.{u, w})
    (P Q : CochainComplex A.mateModules ℤ) :
    (totalSymmetry A P Q).hom ≫ (totalSymmetry A Q P).hom = 𝟙 _ := by
  let := monoidalCategory A.ring
  let := symmetricCategory A.ring
  let := ringedTensorPreadditive A.ring
  let : MonoidalClosed A.mateModules := Classical.choice (tensorClosed A.ring).2.1
  let : HasColimitsOfSize.{0, 0} A.mateModules := hasColimitsOfSizeShrink.{0, 0, u, u} _
  change (CochainComplex.Monoidal.braiding P Q).hom ≫
    (CochainComplex.Monoidal.braiding Q P).hom = 𝟙 _
  exact complexSymmetry_involutive P Q

private theorem square_involutive {C : Type*} [Category C]
    {A B E F : C} (r : A ≅ E) (s : B ≅ F)
    (x : A ⟶ B) (y : B ⟶ A) (e : E ⟶ F) (f : F ⟶ E)
    (hx : r.hom ≫ e = x ≫ s.hom) (hy : s.hom ≫ f = y ≫ r.hom)
    (hxy : x ≫ y = 𝟙 A) : e ≫ f = 𝟙 E := by
  apply (cancel_epi r.hom).1
  rw [← Category.assoc, hx, Category.assoc, hy, ← Category.assoc, hxy]
  simp

-- Representative tensor types need extra elaboration steps.
set_option maxHeartbeats 800000 in
-- Resolve both variables while keeping the tensor interfaces explicit.
/-- The representative-normalized symmetry is involutive.
Source: Stacks 06YS and 06YN, resolving both variables and cancelling two Koszul signs
(blueprint: lem-sfb-ringed-projection-tensor-structure). -/
theorem tensorConstraints_involutive (A : RingedTensorCorner.{u, w})
    (a : RingedTensorModel A) (tx : TensorConstraints A a) (E Q : A.mateDerived) :
    (tx.symmetry E Q).hom ≫ (tx.symmetry Q E).hom = 𝟙 _ := by
  have hrep (P Q : CochainComplex A.mateModules ℤ)
      (hp : A.mateFlat P) (hq : A.mateFlat Q) :
      (tx.symmetry (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫
        (tx.symmetry (DerivedCategory.Q.obj Q) (DerivedCategory.Q.obj P)).hom = 𝟙 _ := by
    let r : DerivedCategory.Q.obj (total A P Q) ≅
        A.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
      a.representative.app (⟨P, hp⟩, ⟨Q, hq⟩)
    let s : DerivedCategory.Q.obj (total A Q P) ≅
        A.tensor.obj (DerivedCategory.Q.obj Q, DerivedCategory.Q.obj P) :=
      a.representative.app (⟨Q, hq⟩, ⟨P, hp⟩)
    have h₁ : r.hom ≫ (tx.symmetry _ _).hom =
        DerivedCategory.Q.map (totalSymmetry A P Q).hom ≫ s.hom :=
      tx.symmetry_representative P Q hp hq
    have h₂ : s.hom ≫ (tx.symmetry _ _).hom =
        DerivedCategory.Q.map (totalSymmetry A Q P).hom ≫ r.hom :=
      tx.symmetry_representative Q P hq hp
    have hm : DerivedCategory.Q.map (totalSymmetry A P Q).hom ≫
        DerivedCategory.Q.map (totalSymmetry A Q P).hom = 𝟙 _ := by
      rw [← Functor.map_comp, totalSymmetry_involutive, CategoryTheory.Functor.map_id]
    exact square_involutive r s _ _ _ _ h₁ h₂ hm
  have hres (D : A.mateDerived) :
      ∃ (P : CochainComplex A.mateModules ℤ), A.mateFlat P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ D) := by
    obtain ⟨P, f, hk, hf, hq, _⟩ :=
      CochainComplex.exists_isKFlatResolution (DerivedCategory.Q.objPreimage D)
    let := hq
    exact ⟨P, ⟨hk, hf⟩,
      ⟨asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso D⟩⟩
  obtain ⟨P, hp, ⟨e⟩⟩ := hres E
  obtain ⟨R, hr, ⟨q⟩⟩ := hres Q
  let j := A.tensor.mapIso (Iso.prod e q)
  apply (cancel_epi j.hom).1
  change A.tensor.map (Prod.mkHom e.hom q.hom) ≫ _ = _
  rw [← Category.assoc, tx.symmetry_naturality e.hom q.hom, Category.assoc,
    tx.symmetry_naturality q.hom e.hom, ← Category.assoc, hrep P R hp hr,
    Category.id_comp, Category.comp_id]
  rfl



set_option linter.checkUnivs false in
/-- Tensor structure and pullback comparisons, before taking any adjunction mates.
Source: Stacks 06YS, 06YU, 07A4, 0D6D and 0FPI.
(blueprint: lem-sfb-ringed-projection-tensor-structure). -/
structure TensorStructure where
  constraints : ∀ (X : RingedTensorCorner.{u, w}) (a : RingedTensorModel X),
    TensorConstraints X a
  associativity : ∀ {X Y : RingedTensorCorner.{u, w}} (f : RingedTensorEdge Y X)
    (a : RingedTensorModel X) (b : RingedTensorModel Y) (E Q N : Y.mateDerived),
    f.left.map ((constraints Y b).associator E Q N).inv ≫
        (f.tensorComparison b a).hom.app (Y.tensor.obj (E, Q), N) ≫
        X.tensor.map (Prod.mkHom ((f.tensorComparison b a).hom.app (E, Q))
          (𝟙 (f.left.obj N))) =
      (f.tensorComparison b a).hom.app (E, Y.tensor.obj (Q, N)) ≫
        X.tensor.map (Prod.mkHom (𝟙 (f.left.obj E))
          ((f.tensorComparison b a).hom.app (Q, N))) ≫
        ((constraints X a).associator (f.left.obj E) (f.left.obj Q) (f.left.obj N)).inv
  identity : ∀ {X : RingedTensorCorner.{u, w}} (h : RingedTensorEdge X X)
    (a : RingedTensorModel X) (s : Identity h),
    ∃ l : h.left ≅ 𝟭 X.mateDerived, s.Normalized l ∧
      ∀ E Q : X.mateDerived,
        (h.tensorComparison a a).hom.app (E, Q) ≫
          X.tensor.map (Prod.mkHom (l.hom.app E) (l.hom.app Q)) =
        l.hom.app (X.tensor.obj (E, Q))
  composition : ∀ {X Y Z : RingedTensorCorner.{u, w}}
    (f : RingedTensorEdge Y X) (g : RingedTensorEdge Z Y) (h : RingedTensorEdge Z X)
    (a : RingedTensorModel X) (b : RingedTensorModel Y) (c : RingedTensorModel Z)
    (s : Composition f g h),
    ∃ l : h.left ≅ g.left ⋙ f.left, s.Normalized l ∧
      ∀ E Q : Z.mateDerived,
        l.hom.app (Z.tensor.obj (E, Q)) ≫
            f.left.map ((g.tensorComparison c b).hom.app (E, Q)) ≫
            (f.tensorComparison b a).hom.app (g.left.obj E, g.left.obj Q) =
          (h.tensorComparison c a).hom.app (E, Q) ≫
            X.tensor.map (Prod.mkHom (l.hom.app E) (l.hom.app Q))
  sectionComparison : ∀ {X W : RingedTensorCorner.{u, w}}
    (i : RingedTensorEdge W X) (p : RingedTensorEdge X W)
    (a : RingedTensorModel X) (b : RingedTensorModel W) (s : Section i p),
    ∃ l : p.left ⋙ i.left ≅ 𝟭 X.mateDerived, s.Normalized l ∧
      ∀ E Q : X.mateDerived,
        i.left.map ((p.tensorComparison a b).hom.app (E, Q)) ≫
            (i.tensorComparison b a).hom.app (p.left.obj E, p.left.obj Q) ≫
            X.tensor.map (Prod.mkHom (l.hom.app E) (l.hom.app Q)) =
          l.hom.app (X.tensor.obj (E, Q))

set_option linter.checkUnivs false in
/-- Canonical tensor coherence extends to every recorded tensor presentation.
Source: Stacks 06YS, 06YU, 07A4, 0D6D and 0FPI.
(blueprint: lem-sfb-ringed-projection-tensor-structure).

The normalized pullback comparisons are constructed independently by localization;
tensor compatibility supplies their coherence. Combining these two conclusions
adds no condition to a recorded presentation.
-/
theorem ringedProjectionTensorStructure : Nonempty (TensorStructure.{u, w}) := by
  obtain ⟨T⟩ := ringedProjectionTensorCompatibility.{u, w}
  obtain ⟨P⟩ := ringedProjectionPullbackComparisons.{u, w}
  refine ⟨{
    constraints := T.constraints
    associativity := T.associativity
    identity := ?_
    composition := ?_
    sectionComparison := ?_ }⟩
  · intro X h a s
    obtain ⟨l, hl⟩ := P.identity h s
    exact ⟨l, hl, T.identity h a s l hl⟩
  · intro X Y Z f g h a b c s
    obtain ⟨l, hl⟩ := P.composition f g h s
    exact ⟨l, hl, T.composition f g h a b c s l hl⟩
  · intro X W i p a b s
    obtain ⟨l, hl⟩ := P.sectionComparison i p s
    exact ⟨l, hl, T.sectionComparison i p a b s l hl⟩

end SheafOfModules.ProjectionCoherence
