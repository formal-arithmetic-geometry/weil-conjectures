/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits

/-! # Comparing a tensor total with extension by zero
Source: Stacks Project, Section 12.18, Tag 012Z, total differential formula;
Varieties, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-tensor-total-extension-coordinates).
-/

@[expose] public section
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace HomologicalComplex
noncomputable section

section
variable {k : Type w} [Field k] (A B : CochainComplex (ModuleCat.{w} k) ℕ)

private abbrev T := mapBifunctor A B (curriedTensor (ModuleCat.{w} k)) (ComplexShape.up ℕ)
private abbrev E := mapBifunctor (A.extend ComplexShape.embeddingUpNat)
  (B.extend ComplexShape.embeddingUpNat) (curriedTensor (ModuleCat.{w} k))
    (ComplexShape.up ℤ)

private noncomputable def termIso (p q : ℕ) :
    (A.extend ComplexShape.embeddingUpNat).X (p : ℤ) ⊗
      (B.extend ComplexShape.embeddingUpNat).X (q : ℤ) ≅ A.X p ⊗ B.X q :=
  tensorIso (A.extendXIso ComplexShape.embeddingUpNat rfl)
    (B.extendXIso ComplexShape.embeddingUpNat rfl)

private noncomputable def descNat (n : ℕ) : (E A B).X (n : ℤ) ⟶ (T A B).X n :=
  mapBifunctorDesc (fun p q ↦ match p, q with
    | .ofNat a, .ofNat b => fun h ↦ (termIso A B a b).hom ≫
        ιMapBifunctor A B (curriedTensor _) (ComplexShape.up ℕ) a b n (by
          change (a : ℤ) + (b : ℤ) = (n : ℤ) at h
          change a + b = n
          omega)
    | _, _ => fun _ ↦ 0)

private noncomputable def mapX : ∀ n : ℤ,
    (E A B).X n ⟶ ((T A B).extend ComplexShape.embeddingUpNat).X n
  | .ofNat n => descNat A B n ≫
      ((T A B).extendXIso ComplexShape.embeddingUpNat rfl).inv
  | .negSucc _ => 0

private theorem inclusion_descNat (a b n : ℕ) (h : a + b = n) :
    ιMapBifunctor (A.extend ComplexShape.embeddingUpNat)
      (B.extend ComplexShape.embeddingUpNat) (curriedTensor _) (ComplexShape.up ℤ)
        (a : ℤ) (b : ℤ) (n : ℤ) (by change (a : ℤ) + (b : ℤ) = (n : ℤ); omega) ≫
      descNat A B n = (termIso A B a b).hom ≫
        ιMapBifunctor A B (curriedTensor _) (ComplexShape.up ℕ) a b n h := by
  unfold descNat
  rw [ι_mapBifunctorDesc]

set_option backward.isDefEq.respectTransparency false in
private theorem horizontal (a a' b : ℕ) :
    (A.extend ComplexShape.embeddingUpNat).d (a : ℤ) (a' : ℤ) ▷
        (B.extend ComplexShape.embeddingUpNat).X (b : ℤ) ≫ (termIso A B a' b).hom =
      (termIso A B a b).hom ≫ A.d a a' ▷ B.X b := by
  simp only [termIso, tensorIso_hom, whiskerRight_comp_tensorHom,
    tensorHom_comp_whiskerRight]
  congr 1
  erw [HomologicalComplex.extend_d_eq _ ComplexShape.embeddingUpNat
    (i := a) (j := a') rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem vertical (a b b' : ℕ) :
    (A.extend ComplexShape.embeddingUpNat).X (a : ℤ) ◁
        (B.extend ComplexShape.embeddingUpNat).d (b : ℤ) (b' : ℤ) ≫
          (termIso A B a b').hom =
      (termIso A B a b).hom ≫ A.X a ◁ B.d b b' := by
  simp only [termIso, tensorIso_hom, whiskerLeft_comp_tensorHom,
    tensorHom_comp_whiskerLeft]
  congr 1
  erw [HomologicalComplex.extend_d_eq _ ComplexShape.embeddingUpNat
    (i := b) (j := b') rfl rfl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem descNat_comm (n : ℕ) :
    descNat A B n ≫ (T A B).d n (n + 1) =
      (E A B).d (n : ℤ) ((n + 1 : ℕ) : ℤ) ≫ descNat A B (n + 1) := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  cases p with
  | negSucc p =>
      have hz := A.isZero_extend_X ComplexShape.embeddingUpNat (Int.negSucc p)
        (by intro j; change (j : ℤ) ≠ Int.negSucc p; omega)
      exact ((tensorRight _).map_isZero hz).eq_of_src _ _
  | ofNat a =>
      cases q with
      | negSucc q =>
          have hz := B.isZero_extend_X ComplexShape.embeddingUpNat (Int.negSucc q)
            (by intro j; change (j : ℤ) ≠ Int.negSucc q; omega)
          exact ((tensorLeft _).map_isZero hz).eq_of_src _ _
      | ofNat b =>
          have hab : a + b = n := by change (a : ℤ) + (b : ℤ) = (n : ℤ) at hpq; omega
          erw [← Category.assoc, inclusion_descNat A B a b n hab]
          have h₁ : a + 1 + b = n + 1 := by omega
          have h₂ : a + (b + 1) = n + 1 := by omega
          have h₁' : ((a + 1 : ℕ) : ℤ) + (b : ℤ) = ((n + 1 : ℕ) : ℤ) := by omega
          have h₂' : (a : ℤ) + ((b + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) := by omega
          have ha : (ComplexShape.up ℤ).Rel (a : ℤ) ((a + 1 : ℕ) : ℤ) := by
            change (a : ℤ) + 1 = ((a + 1 : ℕ) : ℤ)
            omega
          have hb : (ComplexShape.up ℤ).Rel (b : ℤ) ((b + 1 : ℕ) : ℤ) := by
            change (b : ℤ) + 1 = ((b + 1 : ℕ) : ℤ)
            omega
          simp only [T, E, mapBifunctor.d_eq, Preadditive.comp_add,
            Preadditive.add_comp, Category.assoc, mapBifunctor.ι_D₁_assoc,
            mapBifunctor.ι_D₂_assoc, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
          rw [mapBifunctor.d₁_eq A B (curriedTensor _) (ComplexShape.up ℕ)
              (i₁ := a) (i₁' := a + 1) rfl b (n + 1) h₁,
            mapBifunctor.d₂_eq A B (curriedTensor _) (ComplexShape.up ℕ)
              a (i₂ := b) (i₂' := b + 1) rfl (n + 1) h₂]
          erw [mapBifunctor.d₁_eq (A.extend ComplexShape.embeddingUpNat)
              (B.extend ComplexShape.embeddingUpNat) (curriedTensor _) (ComplexShape.up ℤ)
                ha (b : ℤ) ((n + 1 : ℕ) : ℤ) h₁',
            mapBifunctor.d₂_eq (A.extend ComplexShape.embeddingUpNat)
              (B.extend ComplexShape.embeddingUpNat) (curriedTensor _) (ComplexShape.up ℤ)
                (a : ℤ) hb ((n + 1 : ℕ) : ℤ) h₂']
          have hs : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              (ComplexShape.up ℤ) ((a : ℤ), (b : ℤ)) =
              ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
                (ComplexShape.up ℕ) (a, b) := by
            change (a : ℤ).negOnePow = (-1 : ℤˣ) ^ a
            simp [Int.negOnePow]
          simp only [Linear.comp_units_smul, Linear.units_smul_comp,
            Category.assoc, curriedTensor_map_app, curriedTensor_obj_map, hs]
          erw [inclusion_descNat A B (a + 1) b (n + 1) h₁,
            inclusion_descNat A B a (b + 1) (n + 1) h₂]
          have hs₁ : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              (ComplexShape.up ℤ) ((a : ℤ), (b : ℤ)) =
              ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ)
                (ComplexShape.up ℕ) (a, b) := rfl
          rw [hs₁]
          erw [reassoc_of% horizontal A B a (a + 1) b,
            reassoc_of% vertical A B a b (b + 1)]

private theorem mapX_comm (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    mapX A B i ≫ ((T A B).extend ComplexShape.embeddingUpNat).d i j =
      (E A B).d i j ≫ mapX A B j := by
  cases i with
  | ofNat n =>
      have hj : j = ((n + 1 : ℕ) : ℤ) := by
        change (n : ℤ) + 1 = j at hij
        omega
      subst j
      simp only [mapX]
      erw [HomologicalComplex.extend_d_eq _ ComplexShape.embeddingUpNat
        (i := n) (j := n + 1) rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, descNat_comm]
      rfl
  | negSucc n =>
      apply mapBifunctor.hom_ext
      intro p q hpq
      by_cases hp : ∃ a : ℕ, (a : ℤ) = p
      · obtain ⟨a, rfl⟩ := hp
        have hq : ∀ b : ℕ, ComplexShape.embeddingUpNat.f b ≠ q := by
          intro b hb
          change (b : ℤ) = q at hb
          change (a : ℤ) + q = Int.negSucc n at hpq
          omega
        exact ((tensorLeft _).map_isZero
          (B.isZero_extend_X ComplexShape.embeddingUpNat q hq)).eq_of_src _ _
      · exact ((tensorRight _).map_isZero
          (A.isZero_extend_X ComplexShape.embeddingUpNat p
            (fun a ha ↦ hp ⟨a, ha⟩))).eq_of_src _ _

end

/-- Extension of the tensor total agrees with the tensor total of the extensions
on every nonnegative pure tensor summand.
Source: Stacks Project, Section 12.18, Tag 012Z, total differential formula;
Varieties, Tag 0BED, equation-kunneth-on-cech.
(blueprint: lem-sc-tensor-total-extension-coordinates).

Proof: In degree n use the coproduct universal property on integer bidegrees
p+q=n. If p and q are nonnegative, identify both extended terms with the
original terms by extendXIso, include their tensor in the natural-index total,
and apply the inverse of that total's extension isomorphism. If either index
is negative, the corresponding extended term is zero, and tensoring with it
is zero; use the unique zero map. These maps commute with the differential:
for nonnegative indices both factor differentials are the original ones and
the sign (-1)^p agrees with the natural-index sign; for a negative index the
source is zero. This includes the boundary from degree -1 to 0. The summand
inclusion equations of the coproduct descent give the displayed identity.
Empty and zero complexes satisfy the same construction; degree zero has only
the surviving summand (0,0). This comparison is entirely independent of schemes,
Cech cochains, coefficient morphisms and cup products. -/
theorem tensorTotalExtend_coordinates
    {k : Type w} [Field k] (A B : CochainComplex (ModuleCat.{w} k) ℕ) :
    ∃ e : mapBifunctor (A.extend ComplexShape.embeddingUpNat)
        (B.extend ComplexShape.embeddingUpNat) (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℤ) ⟶
      (mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
        (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat,
      ∀ (p q : ℕ) (x : A.X p) (y : B.X q),
        ((mapBifunctor A B (curriedTensor (ModuleCat.{w} k))
          (ComplexShape.up ℕ)).extendXIso ComplexShape.embeddingUpNat
            (show ((p + q : ℕ) : ℤ) = ((p + q : ℕ) : ℤ) from rfl)).hom
          (e.f ((p + q : ℕ) : ℤ)
            (ιMapBifunctor (A.extend ComplexShape.embeddingUpNat)
              (B.extend ComplexShape.embeddingUpNat) (curriedTensor (ModuleCat.{w} k))
                (ComplexShape.up ℤ) (p : ℤ) (q : ℤ) ((p + q : ℕ) : ℤ) (by
                  change (p : ℤ) + (q : ℤ) = ((p + q : ℕ) : ℤ)
                  omega)
                (((A.extendXIso ComplexShape.embeddingUpNat
                  (show (p : ℤ) = (p : ℤ) from rfl)).inv x) ⊗ₜ[k]
                  ((B.extendXIso ComplexShape.embeddingUpNat
                    (show (q : ℤ) = (q : ℤ) from rfl)).inv y)))) =
          ιMapBifunctor A B (curriedTensor (ModuleCat.{w} k))
            (ComplexShape.up ℕ) p q (p + q) rfl (x ⊗ₜ[k] y)  := by
  let e : E A B ⟶ (T A B).extend ComplexShape.embeddingUpNat :=
    { f := mapX A B
      comm' := mapX_comm A B }
  refine ⟨e, ?_⟩
  intro p q x y
  dsimp only [e, mapX]
  simp only [ConcreteCategory.comp_apply]
  erw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  have h := ConcreteCategory.congr_hom
    (inclusion_descNat A B p q (p + q) rfl)
      (((A.extendXIso ComplexShape.embeddingUpNat rfl).inv x) ⊗ₜ[k]
        ((B.extendXIso ComplexShape.embeddingUpNat rfl).inv y))
  simp only [ConcreteCategory.comp_apply] at h
  erw [h]
  simp only [termIso, tensorIso_hom, ModuleCat.hom_tensorHom]
  erw [TensorProduct.map_tmul]
  have hx := ConcreteCategory.congr_hom
    (A.extendXIso ComplexShape.embeddingUpNat
      (show (p : ℤ) = (p : ℤ) from rfl)).inv_hom_id x
  have hy := ConcreteCategory.congr_hom
    (B.extendXIso ComplexShape.embeddingUpNat
      (show (q : ℤ) = (q : ℤ) from rfl)).inv_hom_id y
  dsimp at hx hy
  erw [hx, hy]
  rfl

end
end HomologicalComplex
