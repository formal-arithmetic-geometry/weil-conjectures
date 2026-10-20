/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q1, SHEAF group T3
-/
module

public import Sheaf.Algebra.Homology.RingHomExtensionDefs
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.HomComplex

/-! # Differential compatibility for normalized Hom degree maps

Source: Stacks Project, more-algebra.tex, equation-base-change-RHom;
sites-cohomology.tex, section-hom-complexes (Tag 0A8X).
(blueprint: lem-pc-ring-hom-extension-differential)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

open scoped ChangeOfRings

namespace CategoryTheory

/-- Adjacent-degree differential compatibility for normalized maps.
This is the pure-tensor calculation from the Hom-complex differential formula.
Source: Stacks Project, more-algebra.tex, equation-base-change-RHom;
sites-cohomology.tex, section-hom-complexes (Tag 0A8X).
(blueprint: lem-pc-ring-hom-extension-differential-adjacent).
Proof: compose with each target product projection, then use the supplied evaluation
formula on pure tensors in both arguments. The two terms are respectively the
postcomposition by `d_Q` and the signed precomposition by `d_P`; naturality of the
extension unit and additivity of `F` identify the corresponding extended terms.
Tensor-product induction and internal-Hom extensionality finish the equality. -/
theorem ringHomExtension_differential_adjacent
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (_hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom (ringSiteMap φ) M f ≫ eqToHom (h N).symm)
    (hF : F.Additive) (P Q : CochainComplex (RingSiteModules A) ℤ)
    (t : ∀ n : ℤ,
      F.obj ((homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n) ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf B)
          ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj Q)).X n)
    (n : ℤ) (ht : ∀ (n p : ℤ) (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
      (f : (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n |>.val.obj U)
      (x : (P.X p).val.obj U),
      ringHomEvaluate ((ringExtensionComplex F hF).obj P)
        ((ringExtensionComplex F hF).obj Q) n p U
        ((t n).val.app U (ringExtensionPure φ F h _ U b f))
        (ringExtensionPure φ F h (P.X p) U c x) =
      ringExtensionPure φ F h (Q.X (p + n)) U (b * c)
        (ringHomEvaluate P Q n p U f x)) :
    t n ≫ (homComplex (R := CochainComplex.onePointRingSheaf B)
        ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj Q)).d n (n + 1) =
      ((ringExtensionComplex F hF).obj
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q)).d n (n + 1) ≫ t (n + 1) := by
  sorry

/-- Any degree maps with the normalized tensor-Hom formula commute with differentials.
Source: Stacks Project, more-algebra.tex, equation-base-change-RHom;
sites-cohomology.tex, section-hom-complexes (Tag 0A8X).
(blueprint: lem-pc-ring-hom-extension-differential).
Proof: in adjacent degrees use `ringHomExtension_differential_adjacent`. In all other
degrees both differentials are zero by the complex shape, so both composites vanish. -/
theorem ringHomExtension_differential
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (F : RingSiteModules A ⥤ RingSiteModules B)
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings (ringSiteMap φ) M)
    (hm : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom (ringSiteMap φ) M f ≫ eqToHom (h N).symm)
    (hF : F.Additive) (P Q : CochainComplex (RingSiteModules A) ℤ)
    (t : ∀ n : ℤ,
      F.obj ((homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n) ⟶
        (homComplex (R := CochainComplex.onePointRingSheaf B)
          ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj Q)).X n)
    (ht : ∀ (n p : ℤ) (U : (Discrete PUnit.{u + 1})ᵒᵖ) (b c : B)
      (f : (homComplex (R := CochainComplex.onePointRingSheaf A) P Q).X n |>.val.obj U)
      (x : (P.X p).val.obj U),
      ringHomEvaluate ((ringExtensionComplex F hF).obj P)
        ((ringExtensionComplex F hF).obj Q) n p U
        ((t n).val.app U (ringExtensionPure φ F h _ U b f))
        (ringExtensionPure φ F h (P.X p) U c x) =
      ringExtensionPure φ F h (Q.X (p + n)) U (b * c)
        (ringHomEvaluate P Q n p U f x)) :
    ∀ n m : ℤ,
      t n ≫ (homComplex (R := CochainComplex.onePointRingSheaf B)
        ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj Q)).d n m =
      ((ringExtensionComplex F hF).obj
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q)).d n m ≫ t m := by
  intro n m
  by_cases hnm : n + 1 = m
  · subst m
    exact ringHomExtension_differential_adjacent φ F h hm hF P Q t n ht
  · rw [((homComplex (R := CochainComplex.onePointRingSheaf B)
      ((ringExtensionComplex F hF).obj P) ((ringExtensionComplex F hF).obj Q)).shape n m hnm),
      ((ringExtensionComplex F hF).obj
        (homComplex (R := CochainComplex.onePointRingSheaf A) P Q)).shape n m hnm,
      comp_zero, zero_comp]

end CategoryTheory
