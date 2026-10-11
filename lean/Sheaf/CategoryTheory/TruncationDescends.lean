/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Single

/-!
# Descent of canonical truncations to the derived category

Source: Stacks Project, Tags 08J5, 0118, 05RU and 04VG
(blueprint: lem-weil-pbc-truncation-descends).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace DerivedCategory

/-- Canonical truncation and the single-cohomology functor preserve quasi-isomorphisms
and descend, together with their canonical inclusion and projection, to the derived category.
Source: Stacks Project, Remark 08J5, Section 0118, Definition 05RU and Lemma 04VG
(blueprint: lem-weil-pbc-truncation-descends).

Proof:
1. The truncation inclusion induces cohomology isomorphisms in degrees at most q and
   its source has zero cohomology above q (lem-weil-pbc-truncation-cohomology).
   Naturality then shows truncation preserves quasi-isomorphisms, also at q-1.
2. A quasi-isomorphism induces an isomorphism on H^q. Its single-complex map is an
   isomorphism degreewise and hence a quasi-isomorphism.
3. The inclusions commute with complex maps; the cycles-to-cohomology quotient commutes
   with them as well (lem-weil-pbc-truncation-step-ses). These characterize i and j below.
4. After composition with Q, the three functors invert quasi-isomorphisms. The localization
   universal property produces their descents and comparison isomorphisms, uniquely up to
   unique compatible isomorphism (lem-weil-pbc-localization-universal-property).
5. The fully faithful restriction of natural transformations along the localization gives
   the unique descended i and j with the displayed compatibility equations.
6. Naturality of these transformations gives the two equations at every derived morphism;
   naturality of the comparison isomorphisms gives the three equations at Q.map φ. -/
theorem truncation_descends (A : Type u) [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (q : ℤ) :
    (∀ (K L : CochainComplex A ℤ) (s : K ⟶ L), QuasiIso s →
      QuasiIso (CochainComplex.truncLEMap s q) ∧
      QuasiIso (CochainComplex.truncLEMap s (q - 1)) ∧
      QuasiIso ((CochainComplex.singleFunctor A q).map
        ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q).map s))) ∧
    (∀ (K : CochainComplex A ℤ) (r : ℤ),
      (r ≤ q → QuasiIsoAt (K.ιTruncLE q) r) ∧
      (q < r → IsZero ((K.truncLE q).homology r))) ∧
    ∃ (i : (ComplexShape.embeddingUpIntLE (q - 1)).truncLEFunctor A ⟶
            (ComplexShape.embeddingUpIntLE q).truncLEFunctor A)
      (j : (ComplexShape.embeddingUpIntLE q).truncLEFunctor A ⟶
            HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙
              CochainComplex.singleFunctor A q),
      (∀ K : CochainComplex A ℤ,
        i.app K ≫ K.ιTruncLE q = K.ιTruncLE (q - 1)) ∧
      (∀ K : CochainComplex A ℤ,
        (j.app K).f q ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q (K.homology q)).hom =
          (K.truncLEXIsoCycles q).hom ≫ K.homologyπ q) ∧
      ∃ (T₀ T₁ H : DerivedCategory A ⥤ DerivedCategory A)
        (e₀ : Q ⋙ T₀ ≅ (ComplexShape.embeddingUpIntLE (q - 1)).truncLEFunctor A ⋙ Q)
        (e₁ : Q ⋙ T₁ ≅ (ComplexShape.embeddingUpIntLE q).truncLEFunctor A ⋙ Q)
        (eH : Q ⋙ H ≅ (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙
          CochainComplex.singleFunctor A q) ⋙ Q),
        (∀ (G : DerivedCategory A ⥤ DerivedCategory A)
          (e : Q ⋙ G ≅ (ComplexShape.embeddingUpIntLE (q - 1)).truncLEFunctor A ⋙ Q),
          ∃! a : T₀ ≅ G, whiskerLeft Q a.hom ≫ e.hom = e₀.hom) ∧
        (∀ (G : DerivedCategory A ⥤ DerivedCategory A)
          (e : Q ⋙ G ≅ (ComplexShape.embeddingUpIntLE q).truncLEFunctor A ⋙ Q),
          ∃! a : T₁ ≅ G, whiskerLeft Q a.hom ≫ e.hom = e₁.hom) ∧
        (∀ (G : DerivedCategory A ⥤ DerivedCategory A)
          (e : Q ⋙ G ≅ (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙
            CochainComplex.singleFunctor A q) ⋙ Q),
          ∃! a : H ≅ G, whiskerLeft Q a.hom ≫ e.hom = eH.hom) ∧
        (∃! iD : T₀ ⟶ T₁,
          whiskerLeft Q iD ≫ e₁.hom = e₀.hom ≫ whiskerRight i Q) ∧
        (∃! jD : T₁ ⟶ H,
          whiskerLeft Q jD ≫ eH.hom = e₁.hom ≫ whiskerRight j Q) ∧
        ∃ (iD : T₀ ⟶ T₁) (jD : T₁ ⟶ H),
          (whiskerLeft Q iD ≫ e₁.hom = e₀.hom ≫ whiskerRight i Q) ∧
          (whiskerLeft Q jD ≫ eH.hom = e₁.hom ≫ whiskerRight j Q) ∧
          (∀ (K L : DerivedCategory A) (f : K ⟶ L),
            iD.app K ≫ T₁.map f = T₀.map f ≫ iD.app L ∧
            jD.app K ≫ H.map f = T₁.map f ≫ jD.app L) ∧
          (∀ (K L : CochainComplex A ℤ) (φ : K ⟶ L),
            T₀.map (Q.map φ) ≫ e₀.hom.app L =
              e₀.hom.app K ≫ Q.map (CochainComplex.truncLEMap φ (q - 1)) ∧
            T₁.map (Q.map φ) ≫ e₁.hom.app L =
              e₁.hom.app K ≫ Q.map (CochainComplex.truncLEMap φ q) ∧
            H.map (Q.map φ) ≫ eH.hom.app L = eH.hom.app K ≫
              Q.map ((CochainComplex.singleFunctor A q).map
                ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q).map φ))) := by
  sorry

end DerivedCategory
