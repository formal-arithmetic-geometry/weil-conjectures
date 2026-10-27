/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Q61
-/
module

public import Sheaf.CategoryTheory.FiniteFreeRepresentables
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.CategoryTheory.Yoneda

/-!
# Contravariant finite representable evaluation and signed total homotopies

Source: the agent-formulated finite matrix algebra supporting paragraph (3) of the
blueprint direct-images proof (blueprint: lem-sfb-finite-representable-matrix-totalization).
The current blueprint supplies the application, rather than a proof of this algebraic lemma.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The finite biproducts of complexes used for evaluation; no infinite sums are assumed.
Source: finite matrix algebra, blueprint direct-images paragraph (3)
(blueprint: lem-sfb-finite-representable-matrix-totalization). -/
instance finiteRepresentableEvaluationBiproducts
    (C : Type v) [Category.{w} C] [Abelian C] :
    HasFiniteBiproducts (CochainComplex C ℕ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Contravariant matrix evaluation, its first-quadrant total complex, and the explicit
signed homotopy, all natural in the diagram. The isomorphisms `e` identify evaluation with
finite sums. The maps `ι` exhibit the total terms as finite antidiagonal coproducts.

Source: agent-formulated finite matrix algebra supporting paragraph (3) of the current
blueprint direct-images proof (blueprint: lem-sfb-finite-representable-matrix-totalization).

Proof: (1) Yoneda (lem-galois-yoneda-hom-bijection) and the free abelian extension identify
each singleton transformation with its value on the identity generator. Its finite sum
of arrows uniquely determines the transformation; the empty matrix is zero.
(2) Evaluate this finite sum by the corresponding integral sum of diagram maps.
Bilinearity proves identity, addition, and reversed composition.
(3) Transpose the finite matrices using biproduct inclusions and projections. Their
relations give functoriality; diagram naturality gives naturality in X.
(4) The evaluated chain differentials square to zero and commute with the internal
differentials. Totalize using def-sp-double-complex-total: in degree m only m+1
summands occur. The cross terms cancel because the vertical sign is (-1)^n.
(5) Evaluate chain maps on each summand to obtain contravariant total cochain maps.
(6) Evaluate h_n from horizontal degree n+1 to n. The horizontal terms give u-v;
the internal terms have signs (-1)^n and (-1)^(n+1) and cancel by internal
commutation. At horizontal degree zero the homotopy is zero, and only h_0 after
the horizontal differential contributes. All these formulas are natural in X.
(7) Apply this to both inverse homotopies. The resulting total homotopy equivalence
induces a quasi-isomorphism by lem-weil-pbc-homotopic-maps-equal-cohomology, hence
an isomorphism under the localization def-weil-abstract-derived-category.
With internal degree zero only the horizontal summands survive. -/
theorem finite_representable_matrix_totalization
    (I : Type u) [SmallCategory I] (C : Type v) [Category.{w} C] [Abelian C]
    [HasDerivedCategory.{z} C] :
    ∃ (E : (I ⥤ CochainComplex C ℕ) ⥤
        (FiniteFreeRepresentables I)ᵒᵖ ⥤ CochainComplex C ℕ)
      (e : ∀ (X : I ⥤ CochainComplex C ℕ) (A : FiniteFreeRepresentables I),
        (E.obj X).obj (op A) ≅ ⨁ (fun a : Fin A.1 ↦ X.obj (A.2 a)))
      (T : (I ⥤ CochainComplex C ℕ) ⥤
        (ChainComplex (FiniteFreeRepresentables I) ℕ)ᵒᵖ ⥤ CochainComplex C ℕ)
      (ι : ∀ (X : I ⥤ CochainComplex C ℕ)
        (P : ChainComplex (FiniteFreeRepresentables I) ℕ) (n r m : ℕ), n + r = m →
        (((E.obj X).obj (op (P.X n))).X r ⟶ ((T.obj X).obj (op P)).X m)),
      (∀ X, (E.obj X).Additive) ∧
      (∀ (X : I ⥤ CochainComplex C ℕ) (A B : FiniteFreeRepresentables I)
        (M : A ⟶ B) (b : Fin B.1) (a : Fin A.1),
        biproduct.ι (fun b : Fin B.1 ↦ X.obj (B.2 b)) b ≫ (e X B).inv ≫
          (E.obj X).map M.op ≫ (e X A).hom ≫
          biproduct.π (fun a : Fin A.1 ↦ X.obj (A.2 a)) a =
          FreeAbelianGroup.lift (fun α : B.2 b ⟶ A.2 a ↦ X.map α)
            (finiteRepresentableCoefficient I M b a)) ∧
      (∀ (X Y : I ⥤ CochainComplex C ℕ) (τ : X ⟶ Y) (A : FiniteFreeRepresentables I),
        (e X A).inv ≫ (E.map τ).app (op A) ≫ (e Y A).hom =
          biproduct.map (fun a : Fin A.1 ↦ τ.app (A.2 a))) ∧
      (∀ (X : I ⥤ CochainComplex C ℕ)
        (P : ChainComplex (FiniteFreeRepresentables I) ℕ) (m : ℕ),
        Nonempty (IsColimit (Cofan.mk (((T.obj X).obj (op P)).X m)
          (fun a : ↥(Finset.antidiagonal m) ↦
            ι X P a.val.1 a.val.2 m (Finset.mem_antidiagonal.mp a.property))))) ∧
      (∀ (X : I ⥤ CochainComplex C ℕ)
        (P : ChainComplex (FiniteFreeRepresentables I) ℕ) (n r : ℕ),
        ι X P n r (n + r) rfl ≫ ((T.obj X).obj (op P)).d (n + r) (n + r + 1) =
          ((E.obj X).map (P.d (n + 1) n).op).f r ≫
            ι X P (n + 1) r (n + r + 1) (by omega) +
          (-1 : ℤ) ^ n • (((E.obj X).obj (op (P.X n))).d r (r + 1) ≫
            ι X P n (r + 1) (n + r + 1) (by omega))) ∧
      (∀ (X : I ⥤ CochainComplex C ℕ)
        (P Q : ChainComplex (FiniteFreeRepresentables I) ℕ) (f : P ⟶ Q) (n r : ℕ),
        ι X Q n r (n + r) rfl ≫ ((T.obj X).map f.op).f (n + r) =
          ((E.obj X).map (f.f n).op).f r ≫ ι X P n r (n + r) rfl) ∧
      (∀ (X Y : I ⥤ CochainComplex C ℕ) (τ : X ⟶ Y)
        (P : ChainComplex (FiniteFreeRepresentables I) ℕ) (n r : ℕ),
        ι X P n r (n + r) rfl ≫ ((T.map τ).app (op P)).f (n + r) =
          ((E.map τ).app (op (P.X n))).f r ≫ ι Y P n r (n + r) rfl) ∧
      (∀ (P Q : ChainComplex (FiniteFreeRepresentables I) ℕ) (f g : P ⟶ Q)
        (h : Homotopy f g),
        ∃ H : ∀ X : I ⥤ CochainComplex C ℕ,
          Homotopy ((T.obj X).map f.op) ((T.obj X).map g.op),
          (∀ (X : I ⥤ CochainComplex C ℕ) (n r : ℕ),
            ι X Q (n + 1) r (n + 1 + r) rfl ≫ (H X).hom (n + 1 + r) (n + r) =
              ((E.obj X).map (h.hom n (n + 1)).op).f r ≫
                ι X P n r (n + r) rfl) ∧
          (∀ (X : I ⥤ CochainComplex C ℕ) (r m : ℕ),
            ι X Q 0 r r (by omega) ≫ (H X).hom r m = 0) ∧
          (∀ (X Y : I ⥤ CochainComplex C ℕ) (τ : X ⟶ Y) (m k : ℕ),
            ((T.map τ).app (op Q)).f m ≫ (H Y).hom m k =
              (H X).hom m k ≫ ((T.map τ).app (op P)).f k)) ∧
      (∀ (X : I ⥤ CochainComplex C ℕ)
        (P Q : ChainComplex (FiniteFreeRepresentables I) ℕ) (f g : P ⟶ Q)
        (h : Homotopy f g) (n r : ℕ),
        (-1 : ℤ) ^ n • (((E.obj X).map (h.hom n (n + 1)).op).f r ≫
          ((E.obj X).obj (op (P.X n))).d r (r + 1)) +
        (-1 : ℤ) ^ (n + 1) • (((E.obj X).obj (op (Q.X (n + 1)))).d r (r + 1) ≫
          ((E.obj X).map (h.hom n (n + 1)).op).f (r + 1)) = 0) ∧
      (∀ (X : I ⥤ CochainComplex C ℕ),
        (∀ (i : I) (r : ℕ), 0 < r → IsZero ((X.obj i).X r)) →
        ∀ (P : ChainComplex (FiniteFreeRepresentables I) ℕ) (m : ℕ),
          IsIso (ι X P m 0 m (by omega))) ∧
      (∃ (L : (I ⥤ CochainComplex C ℕ) →
          ChainComplex (FiniteFreeRepresentables I) ℕ →
          HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
        (hL : ∀ (X : I ⥤ CochainComplex C ℕ)
          (P : ChainComplex (FiniteFreeRepresentables I) ℕ) (p q : ℤ),
          p < 0 ∨ q < 0 → IsZero (((L X P).X p).X q))
        (ℓ : ∀ (X : I ⥤ CochainComplex C ℕ)
          (P : ChainComplex (FiniteFreeRepresentables I) ℕ) (n : ℕ),
          (L X P).X (n : ℤ) ≅
            ((E.obj X).obj (op (P.X n))).extend ComplexShape.embeddingUpNat),
        (∀ (X : I ⥤ CochainComplex C ℕ)
          (P : ChainComplex (FiniteFreeRepresentables I) ℕ) (n : ℕ),
          (ℓ X P n).inv ≫ (L X P).d (n : ℤ) ((n : ℤ) + 1) ≫
            (ℓ X P (n + 1)).hom =
            (ComplexShape.embeddingUpNat.extendFunctor C).map
              ((E.obj X).map (P.d (n + 1) n).op)) ∧
        (∀ (X : I ⥤ CochainComplex C ℕ)
          (P : ChainComplex (FiniteFreeRepresentables I) ℕ),
          Nonempty ((((T.obj X).obj (op P)).extend ComplexShape.embeddingUpNat) ≅
            @HomologicalComplex₂.total C _ _ ℤ ℤ ℤ
              (ComplexShape.up ℤ) (ComplexShape.up ℤ) (L X P) (ComplexShape.up ℤ)
              _ _ ((L X P).hasTotal_of_firstQuadrant (hL X P))))) ∧
      (∀ (P Q : ChainComplex (FiniteFreeRepresentables I) ℕ) (f : HomotopyEquiv P Q),
        ∃ F : ∀ X : I ⥤ CochainComplex C ℕ,
          HomotopyEquiv ((T.obj X).obj (op Q)) ((T.obj X).obj (op P)),
          ∀ X : I ⥤ CochainComplex C ℕ,
            (F X).hom = (T.obj X).map f.hom.op ∧
            (F X).inv = (T.obj X).map f.inv.op ∧
            ∃ D : DerivedCategory.Q.obj
                (((T.obj X).obj (op Q)).extend ComplexShape.embeddingUpNat) ≅
              DerivedCategory.Q.obj
                (((T.obj X).obj (op P)).extend ComplexShape.embeddingUpNat),
              D.hom = DerivedCategory.Q.map
                ((ComplexShape.embeddingUpNat.extendFunctor C).map (F X).hom)) := by
  sorry

end CategoryTheory
