/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Single
import WeilConjectures.Algebra.Homology.UpperTruncationStepSES

/-!
# Descent of canonical truncations to the derived category

Source: Stacks Project, Tags 08J5, 0118, 05RU and 04VG
(blueprint: lem-weil-pbc-truncation-descends).
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace DerivedCategory

private theorem descent_iso_unique
    {C D E : Type*} [Category C] [Category D] [Category E]
    (W : MorphismProperty C) (L : C ⥤ D) [L.IsLocalization W]
    {F : C ⥤ E} {T G : D ⥤ E} (eT : L ⋙ T ≅ F) (eG : L ⋙ G ≅ F) :
    ∃! a : T ≅ G, whiskerLeft L a.hom ≫ eG.hom = eT.hom := by
  let ff := Localization.fullyFaithfulWhiskeringLeft L W E
  let a : T ≅ G := ff.preimageIso (eT ≪≫ eG.symm)
  have ha : whiskerLeft L a.hom ≫ eG.hom = eT.hom := by
    change ((whiskeringLeft C D E).obj L).map
      (ff.preimage (eT.hom ≫ eG.inv)) ≫ eG.hom = eT.hom
    rw [ff.map_preimage]
    simp [Category.assoc]
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply Iso.ext
  apply ff.map_injective
  exact (cancel_mono eG.hom).1 (hb.trans ha.symm)

private theorem descent_trans_unique
    {C D E : Type*} [Category C] [Category D] [Category E]
    (W : MorphismProperty C) (L : C ⥤ D) [L.IsLocalization W]
    {F₀ F₁ : C ⥤ E} {T₀ T₁ : D ⥤ E}
    (e₀ : L ⋙ T₀ ≅ F₀) (e₁ : L ⋙ T₁ ≅ F₁) (τ : F₀ ⟶ F₁) :
    ∃! a : T₀ ⟶ T₁, whiskerLeft L a ≫ e₁.hom = e₀.hom ≫ τ := by
  let ff := Localization.fullyFaithfulWhiskeringLeft L W E
  let a : T₀ ⟶ T₁ := ff.preimage (e₀.hom ≫ τ ≫ e₁.inv)
  have ha : whiskerLeft L a ≫ e₁.hom = e₀.hom ≫ τ := by
    change ((whiskeringLeft C D E).obj L).map
      (ff.preimage (e₀.hom ≫ τ ≫ e₁.inv)) ≫ e₁.hom = e₀.hom ≫ τ
    rw [ff.map_preimage]
    simp [Category.assoc]
  refine ⟨a, ha, ?_⟩
  intro b hb
  apply ff.map_injective
  exact (cancel_mono e₁.hom).1 (hb.trans ha.symm)

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
  have htrunc (K L : CochainComplex A ℤ) (s : K ⟶ L) (hs : QuasiIso s) (n : ℤ) :
      QuasiIso (CochainComplex.truncLEMap s n) := by
    have := hs
    exact (CochainComplex.quasiIso_truncLEMap_iff s n).2 (fun _ _ ↦ inferInstance)
  have hsingle (K L : CochainComplex A ℤ) (s : K ⟶ L) (hs : QuasiIso s) :
      QuasiIso ((CochainComplex.singleFunctor A q).map
        ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q).map s)) := by
    have := hs
    change QuasiIso ((CochainComplex.singleFunctor A q).map
      (HomologicalComplex.homologyMap s q))
    infer_instance
  refine ⟨fun K L s hs ↦ ⟨htrunc K L s hs q, htrunc K L s hs (q - 1),
    hsingle K L s hs⟩, ?_, ?_⟩
  · intro K r
    exact ⟨fun hr ↦ K.quasiIsoAt_ιTruncLE q r hr,
      fun hr ↦ (K.truncLE q).isZero_of_isLE q r hr⟩
  · obtain ⟨i, j, barj, hi, _, _, _, hj, hnat⟩ :=
      CochainComplex.exists_upperTruncationStepSES (C := A)
    let iNat : (ComplexShape.embeddingUpIntLE (q - 1)).truncLEFunctor A ⟶
        (ComplexShape.embeddingUpIntLE q).truncLEFunctor A :=
      { app := fun K ↦ i K q
        naturality := fun _ _ f ↦ (hnat f q).1 }
    let jNat : (ComplexShape.embeddingUpIntLE q).truncLEFunctor A ⟶
        HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙
          CochainComplex.singleFunctor A q :=
      { app := fun K ↦ j K q
        naturality := by
          intro K L f
          obtain ⟨g, hg, hb⟩ := (hnat f q).2
          change CochainComplex.truncLEMap f q ≫ j L q =
            j K q ≫ (CochainComplex.singleFunctor A q).map
              (HomologicalComplex.homologyMap f q)
          rw [(hj L q).2.2.1, (hj K q).2.2.1, ← Category.assoc, hg,
            Category.assoc, ← hb, Category.assoc] }
    refine ⟨iNat, jNat, fun K ↦ hi K q, fun K ↦ (hj K q).1, ?_⟩
    let F₀ := (ComplexShape.embeddingUpIntLE (q - 1)).truncLEFunctor A ⋙ Q
    let F₁ := (ComplexShape.embeddingUpIntLE q).truncLEFunctor A ⋙ Q
    let FH := (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q ⋙
      CochainComplex.singleFunctor A q) ⋙ Q
    let W := HomologicalComplex.quasiIso A (ComplexShape.up ℤ)
    have h₀ : W.IsInvertedBy F₀ := by
      intro K L s hs
      have := htrunc K L s hs (q - 1)
      exact inferInstanceAs (IsIso (Q.map (CochainComplex.truncLEMap s (q - 1))))
    have h₁ : W.IsInvertedBy F₁ := by
      intro K L s hs
      have := htrunc K L s hs q
      exact inferInstanceAs (IsIso (Q.map (CochainComplex.truncLEMap s q)))
    have hH : W.IsInvertedBy FH := by
      intro K L s hs
      have := hsingle K L s hs
      exact inferInstanceAs (IsIso (Q.map ((CochainComplex.singleFunctor A q).map
        ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) q).map s))))
    let T₀ := Localization.lift F₀ h₀ Q
    let T₁ := Localization.lift F₁ h₁ Q
    let H := Localization.lift FH hH Q
    let e₀ := Localization.fac F₀ h₀ Q
    let e₁ := Localization.fac F₁ h₁ Q
    let eH := Localization.fac FH hH Q
    have hiD := descent_trans_unique W Q e₀ e₁ (whiskerRight iNat Q)
    have hjD := descent_trans_unique W Q e₁ eH (whiskerRight jNat Q)
    obtain ⟨iD, hiD'⟩ := hiD.exists
    obtain ⟨jD, hjD'⟩ := hjD.exists
    refine ⟨T₀, T₁, H, e₀, e₁, eH,
      fun _ e ↦ descent_iso_unique W Q e₀ e,
      fun _ e ↦ descent_iso_unique W Q e₁ e,
      fun _ e ↦ descent_iso_unique W Q eH e,
      hiD, hjD, iD, jD, hiD', hjD', ?_, ?_⟩
    · intro K L f
      exact ⟨(iD.naturality f).symm, (jD.naturality f).symm⟩
    · intro K L φ
      exact ⟨e₀.hom.naturality φ, e₁.hom.naturality φ, eH.hom.naturality φ⟩

end DerivedCategory
