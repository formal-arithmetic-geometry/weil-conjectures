/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.DerivedHom
public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedForgetful
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.K.KFlatBifunctorTensorHom
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Operations on the native derived Weil category

This file defines the tensor operations on the native derived Weil category.

The ordinary tensor and internal Hom are the existing relative module-sheaf
constructions with diagonal and conjugation actions. The total tensor below
orders the left degree first. Derived Hom is exactly `ProEtaleWeilSheaf.derivedHom`,
including its product-total sign convention. The Verdier-dependent declarations remain in
`DerivedWeilOperations`, which re-exports this module.

## Implementation details

The tensor map `nativeTensorMap` is obtained from `tensorIhomAdjunction` by transposing
precomposition of the internal Hom; its functoriality follows from the identity and composition
laws for `conjugateEquiv`. Additivity of the tensor in each variable comes from the left adjoint
of the additive internal Hom, and, in the right variable, from the inverse-mates formula.

## References

* [Stacks, Tags 03EK, 012Z, 06YL]
-/

/-! Factored construction. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace DerivedNativeTensorProof

universe v w

open WeilConjectures

variable {D : Type v} [Category.{w} D]

private noncomputable def isoOfHomEquiv {A B : D}
    (e : ∀ Z : D, (B ⟶ Z) ≃ (A ⟶ Z))
    (hn : ∀ (Z Z' : D) (a : B ⟶ Z) (b : Z ⟶ Z'),
      e Z' (a ≫ b) = e Z a ≫ b) : A ≅ B where
  hom := e B (𝟙 B)
  inv := (e A).symm (𝟙 A)
  hom_inv_id := by
    rw [← hn B A (𝟙 B) ((e A).symm (𝟙 A)), Category.id_comp,
      Equiv.apply_symm_apply]
  inv_hom_id := by
    apply (e B).injective
    rw [hn A B, Equiv.apply_symm_apply, Category.id_comp]

private theorem tensor_right_map {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) {K K' : D} (f : K ⟶ K') (L : D) :
    (@MonoidalCategory.tensorRight D _ S.monoidal L).map f =
      S.tensor.map (Prod.mkHom f (𝟙 L)) := by
  let := S.monoidal
  exact (MonoidalCategory.tensorHom_id f L).symm

private theorem tensor_left_map {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (K : D) {L L' : D} (f : L ⟶ L') :
    (@MonoidalCategory.tensorLeft D _ S.monoidal K).map f =
      S.tensor.map (Prod.mkHom (𝟙 K) f) := by
  let := S.monoidal
  exact (MonoidalCategory.id_tensorHom K f).symm

private theorem uncurry_formula {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (K L M : D) (a : K ⟶ H.obj (op L, M)) :
    (S.transpose K L M).symm a =
      S.tensor.map (Prod.mkHom a (𝟙 L)) ≫ S.evaluation L M := by
  let := S.monoidal
  simp only [CoefficientClosedStructure.transpose,
    CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
    MonoidalCategory.tensorHom_id]
  rfl

private theorem uncurry_parameter {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (K L L' M : D) (g : L' ⟶ L)
    (a : K ⟶ H.obj (op L, M)) :
    (S.transpose K L' M).symm (a ≫ H.map (Prod.mkHom g.op (𝟙 M))) =
      S.tensor.map (Prod.mkHom (𝟙 K) g) ≫ (S.transpose K L M).symm a := by
  rw [uncurry_formula, uncurry_formula]
  have h := S.evaluation_naturality L L' M g
  rw [tensor_right_map, tensor_left_map] at h
  change S.tensor.map (Prod.mkHom (H.map (Prod.mkHom g.op (𝟙 M))) (𝟙 L')) ≫
      S.evaluation L' M =
    S.tensor.map (Prod.mkHom (𝟙 (H.obj (op L, M))) g) ≫ S.evaluation L M at h
  change S.tensor.map (Prod.mkHom (a ≫ H.map (Prod.mkHom g.op (𝟙 M))) (𝟙 L')) ≫
    S.evaluation L' M = _
  have hc : Prod.mkHom (a ≫ H.map (Prod.mkHom g.op (𝟙 M))) (𝟙 L') =
      Prod.mkHom a (𝟙 L') ≫ Prod.mkHom (H.map (Prod.mkHom g.op (𝟙 M))) (𝟙 L') := by
    ext <;> simp
  rw [hc, S.tensor.map_comp, Category.assoc, h, ← Category.assoc,
    ← S.tensor.map_comp]
  have hc' : Prod.mkHom a (𝟙 L') ≫ Prod.mkHom (𝟙 (H.obj (op L, M))) g =
      Prod.mkHom (𝟙 K) g ≫ Prod.mkHom a (𝟙 L) := by
    ext <;> simp
  rw [hc', S.tensor.map_comp, Category.assoc]

private theorem uncurry_both {H : Dᵒᵖ × D ⥤ D}
    (S : CoefficientClosedStructure H) (K K' L L' M : D)
    (f : K ⟶ K') (g : L ⟶ L') (a : K' ⟶ H.obj (op L', M)) :
    (S.transpose K L M).symm
        (f ≫ a ≫ H.map (Prod.mkHom g.op (𝟙 M))) =
      S.tensor.map (Prod.mkHom f g) ≫ (S.transpose K' L' M).symm a := by
  change ((S.adjunction L).homEquiv K M).symm
    (f ≫ (a ≫ H.map (Prod.mkHom g.op (𝟙 M)))) = _
  rw [Adjunction.homEquiv_naturality_left_symm, tensor_right_map]
  change S.tensor.map (Prod.mkHom f (𝟙 L)) ≫
    (S.transpose K' L M).symm (a ≫ H.map (Prod.mkHom g.op (𝟙 M))) = _
  rw [uncurry_parameter, ← Category.assoc, ← S.tensor.map_comp]
  congr 2
  ext <;> simp

end DerivedNativeTensorProof

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Tensoring a map in the fixed right factor, obtained by transposing
precomposition of the existing sheaf internal Hom. This is the module tensor map. -/
noncomputable def nativeTensorMap {A B : ProEtaleWeilSheaf k₀ l X} (f : A ⟶ B) :
    tensorFunctor k₀ l X A ⟶ tensorFunctor k₀ l X B :=
  (conjugateEquiv (tensorIhomAdjunction k₀ l X B)
    (tensorIhomAdjunction k₀ l X A)).symm ((ihomBifunctor k₀ l X).map f.op)

/-- The tensor map respects identity maps. -/
theorem nativeTensorMap_id (A : ProEtaleWeilSheaf k₀ l X) :
    nativeTensorMap k₀ l X (𝟙 A) = 𝟙 (tensorFunctor k₀ l X A) := by
  unfold nativeTensorMap
  change (conjugateEquiv (tensorIhomAdjunction k₀ l X A)
    (tensorIhomAdjunction k₀ l X A)).symm
      ((ihomBifunctor k₀ l X).map (𝟙 (op A))) = _
  rw [(ihomBifunctor k₀ l X).map_id]
  exact conjugateEquiv_symm_id (tensorIhomAdjunction k₀ l X A)

/-- Tensor maps respect composition. -/
theorem nativeTensorMap_comp {A B C : ProEtaleWeilSheaf k₀ l X}
    (f : A ⟶ B) (g : B ⟶ C) :
    nativeTensorMap k₀ l X (f ≫ g) =
      nativeTensorMap k₀ l X f ≫ nativeTensorMap k₀ l X g := by
  unfold nativeTensorMap
  rw [op_comp, Functor.map_comp]
  exact (conjugateEquiv_symm_comp (tensorIhomAdjunction k₀ l X C)
    (tensorIhomAdjunction k₀ l X B) (tensorIhomAdjunction k₀ l X A) _ _).symm

/-- The existing relative tensor, curried with its right argument first. -/
noncomputable def nativeTensorBifunctor :
    ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l X where
  obj := tensorFunctor k₀ l X
  map := nativeTensorMap k₀ l X
  map_id := nativeTensorMap_id k₀ l X
  map_comp := nativeTensorMap_comp k₀ l X

/-- The flipped tensor is additive in its left argument. -/
@[instance] theorem nativeTensorBifunctor_flip_additive :
    (nativeTensorBifunctor k₀ l X).flip.Additive := by
  constructor
  intro A B f g
  apply NatTrans.ext
  funext T
  have : (tensorFunctor k₀ l X T).Additive :=
    (tensorIhomAdjunction k₀ l X T).left_adjoint_additive
  exact (tensorFunctor k₀ l X T).map_add

/-- The flipped tensor is additive in its right argument. -/
@[instance] theorem nativeTensorBifunctor_flip_obj_additive
    (A : ProEtaleWeilSheaf k₀ l X) :
    ((nativeTensorBifunctor k₀ l X).flip.obj A).Additive := by
  constructor
  intro B C f g
  have : (tensorFunctor k₀ l X B).Additive :=
    (tensorIhomAdjunction k₀ l X B).left_adjoint_additive
  change ((nativeTensorMap k₀ l X (f + g)).app A) =
    (nativeTensorMap k₀ l X f).app A + (nativeTensorMap k₀ l X g).app A
  simp [nativeTensorMap, conjugateEquiv, mateEquiv, Functor.map_add,
    Preadditive.add_comp, Preadditive.comp_add]

/-- Direct-sum total tensor with left degree first and differential
`d_P tensor 1 + (-1)^p 1 tensor d_T` on the (p,q) summand. -/
noncomputable def nativeTensorTotal :
    CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ ⥤
      CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ ⥤
        CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ :=
  (nativeTensorBifunctor k₀ l X).flip.map₂CochainComplex

/-- The two-sided total-tensor preservation test defining K-flatness, specialized
to the native Weil tensor: tensoring with `P` on either side preserves quasi-isomorphisms. -/
def NativeIsKFlat (P : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) : Prop :=
  (∀ {Q Q' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (s : Q ⟶ Q'),
    QuasiIso s → QuasiIso (((nativeTensorTotal k₀ l X).obj P).map s)) ∧
  (∀ {Q Q' : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ} (s : Q ⟶ Q'),
    QuasiIso s → QuasiIso (((nativeTensorTotal k₀ l X).flip.obj P).map s))

variable [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]

/-- The native closed derived tensor structure: its tensor is determined, up to the
adjunction-compatible unique isomorphism, by the specified internal Hom, with the K-flat
normalization. -/
noncomputable def nativeDerivedClosedComparison : NativeClosedComparison k₀ l X :=
  (native_closed_forgetful k₀ l X).2.2.2.2.choose

/-- Derived relative tensor on the ambient native category, supplied by the
closed structure constructed by localization of total K-flat tensors. -/
noncomputable def nativeDerivedTensor :
    DerivedCategory (ProEtaleWeilSheaf k₀ l X) ×
      DerivedCategory (ProEtaleWeilSheaf k₀ l X) ⥤
        DerivedCategory (ProEtaleWeilSheaf k₀ l X) :=
  (nativeDerivedClosedComparison k₀ l X).weilClosed.tensor

private noncomputable def nativeTensorParametrizedAdjunction :
    nativeTensorBifunctor k₀ l X ⊣₂ ihomBifunctor k₀ l X :=
  { adj := tensorIhomAdjunction k₀ l X
    unit_whiskerRight_map := by
      intro A B f
      apply NatTrans.ext
      funext P
      exact (unit_conjugateEquiv_symm
        (tensorIhomAdjunction k₀ l X B)
        (tensorIhomAdjunction k₀ l X A) ((ihomBifunctor k₀ l X).map f.op) P).symm }

attribute [local irreducible] nativeDerivedClosedComparison nativeTensorBifunctor ihomBifunctor

set_option backward.isDefEq.respectTransparency.types false

end AlgebraicGeometry.ProEtaleWeilSheaf
