import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Single
import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# Distinguished triangle for canonical truncations

Source: literature/stacks-project/derived.tex, Remark 08J5 (line 4076)
(blueprint: lem-weil-pbc-truncation-triangle).
-/

universe w v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- The canonical truncation triangle
tau_{<=q-1}K -> tau_{<=q}K -> H^q(K)[-q] -> (tau_{<=q-1}K)[1] of D(A).
The first two arrows are the canonical maps of complexes: the inclusion i_q
(characterized by its composite with the inclusion into K) and the map j_q whose
degree-q component is the quotient Ker d^q -> H^q(K). The connecting arrow k_q
exists and is unique; the triangle is functorial for every morphism of D(A), the
three truncation functors acting on D(A) through their descent along Q (the
localization lift; lem-weil-pbc-truncation-descends); and the three terms are
bounded below when K is (strictly, or in cohomology).
Source: Stacks Project, Remark 08J5; BBD, Proposition 1.1.9 and Corollaire 1.1.10 (ii)
(blueprint: lem-weil-pbc-truncation-triangle).

Proof:
1. The short exact sequence 0 -> tau_{<=q-1}K -> tau_{<=q}K -> M_q(K) -> 0, with
   j_q factoring through a quasi-isomorphism M_q(K) -> H^q(K)[-q]
   (lem-weil-pbc-truncation-step-ses).
2. Its distinguished triangle in D(A) (lem-weil-pbc-complex-ses-triangle).
3. Transport along the quasi-isomorphism gives k_q (TR1).
4. Hom((tau_{<=q-1}K)[1], H^q(L)[-q]) = 0 (standard t-structure).
5. Uniqueness of k_q and 6. functoriality by lem-weil-pbc-triangle-morphism-extension.
7. Bounded below: cohomology of the canonical truncations. -/
theorem truncation_triangle (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (q : ℤ) :
    (∀ K : CochainComplex A ℤ,
      ∃ (i : K.truncLE (q - 1) ⟶ K.truncLE q)
        (j : K.truncLE q ⟶ (CochainComplex.singleFunctor A q).obj (K.homology q)),
        i ≫ K.ιTruncLE q = K.ιTruncLE (q - 1) ∧
        j.f q ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)).hom =
          (K.truncLEXIsoCycles q).hom ≫ K.homologyπ q ∧
        ∃! k : Q.obj ((CochainComplex.singleFunctor A q).obj (K.homology q)) ⟶
            (Q.obj (K.truncLE (q - 1)))⟦(1 : ℤ)⟧,
          Triangle.mk (Q.map i) (Q.map j) k ∈ distTriang (DerivedCategory A)) ∧
    (∃ (h₀ : (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).IsInvertedBy
          ((ComplexShape.embeddingUpIntLE (q - 1)).truncLEFunctor A ⋙ Q))
        (h₁ : (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).IsInvertedBy
          ((ComplexShape.embeddingUpIntLE q).truncLEFunctor A ⋙ Q))
        (hH : (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)).IsInvertedBy
          ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙
            CochainComplex.singleFunctor A q) ⋙ Q)),
      ∀ (K L : CochainComplex A ℤ)
        (iK : K.truncLE (q - 1) ⟶ K.truncLE q)
        (jK : K.truncLE q ⟶ (CochainComplex.singleFunctor A q).obj (K.homology q))
        (iL : L.truncLE (q - 1) ⟶ L.truncLE q)
        (jL : L.truncLE q ⟶ (CochainComplex.singleFunctor A q).obj (L.homology q)),
        iK ≫ K.ιTruncLE q = K.ιTruncLE (q - 1) →
        jK.f q ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)).hom =
          (K.truncLEXIsoCycles q).hom ≫ K.homologyπ q →
        iL ≫ L.ιTruncLE q = L.ιTruncLE (q - 1) →
        jL.f q ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (L.homology q)).hom =
          (L.truncLEXIsoCycles q).hom ≫ L.homologyπ q →
        ∀ (kK : Q.obj ((CochainComplex.singleFunctor A q).obj (K.homology q)) ⟶
              (Q.obj (K.truncLE (q - 1)))⟦(1 : ℤ)⟧)
          (kL : Q.obj ((CochainComplex.singleFunctor A q).obj (L.homology q)) ⟶
              (Q.obj (L.truncLE (q - 1)))⟦(1 : ℤ)⟧),
          Triangle.mk (Q.map iK) (Q.map jK) kK ∈ distTriang (DerivedCategory A) →
          Triangle.mk (Q.map iL) (Q.map jL) kL ∈ distTriang (DerivedCategory A) →
          ∀ f : Q.obj K ⟶ Q.obj L,
            Q.map iK ≫
                ((Localization.fac _ h₁ Q).inv.app K ≫ (Localization.lift _ h₁ Q).map f ≫
                  (Localization.fac _ h₁ Q).hom.app L) =
              ((Localization.fac _ h₀ Q).inv.app K ≫ (Localization.lift _ h₀ Q).map f ≫
                  (Localization.fac _ h₀ Q).hom.app L) ≫ Q.map iL ∧
            Q.map jK ≫
                ((Localization.fac _ hH Q).inv.app K ≫ (Localization.lift _ hH Q).map f ≫
                  (Localization.fac _ hH Q).hom.app L) =
              ((Localization.fac _ h₁ Q).inv.app K ≫ (Localization.lift _ h₁ Q).map f ≫
                  (Localization.fac _ h₁ Q).hom.app L) ≫ Q.map jL ∧
            kK ≫ ((Localization.fac _ h₀ Q).inv.app K ≫ (Localization.lift _ h₀ Q).map f ≫
                  (Localization.fac _ h₀ Q).hom.app L)⟦(1 : ℤ)⟧' =
              ((Localization.fac _ hH Q).inv.app K ≫ (Localization.lift _ hH Q).map f ≫
                  (Localization.fac _ hH Q).hom.app L) ≫ kL) ∧
    (∀ (K : CochainComplex A ℤ) (n : ℤ),
      (K.IsStrictlyGE n →
        (K.truncLE (q - 1)).IsStrictlyGE n ∧ (K.truncLE q).IsStrictlyGE n ∧
          ((CochainComplex.singleFunctor A q).obj (K.homology q)).IsStrictlyGE (min n q)) ∧
      (K.IsGE n →
        (K.truncLE (q - 1)).IsGE n ∧ (K.truncLE q).IsGE n ∧
          ((CochainComplex.singleFunctor A q).obj (K.homology q)).IsGE (min n q))) := by
  sorry

end DerivedCategory
