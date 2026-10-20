/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# K-flatness of complexes built from split free cells

Source: Stacks Project, More on Algebra, Tags 0BYH and 06Y3, and the proof of
lemma-resolution-filtered-complex (Tag 0H7X).
(blueprint: lem-kun-split-cell-complex-kflat).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

-- With zero differential, the degreewise inclusions are chain maps.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def singleCofan {R : Type u} [CommRing R]
    (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hd : ∀ i j, Q.d i j = 0) :
    Cofan (fun n : ℤ ↦ (HomologicalComplex.single (ModuleCat R) (.up ℤ) n).obj (Q.X n)) :=
  Cofan.mk Q (fun n ↦ HomologicalComplex.mkHomFromSingle (𝟙 _) (by simp [hd]))

-- The coproduct universal property is checked one degree at a time.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def singleCofanIsColimit {R : Type u} [CommRing R]
    (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hd : ∀ i j, Q.d i j = 0) : IsColimit (singleCofan Q hd) where
  desc s :=
    { f := fun n ↦ (HomologicalComplex.singleObjXSelf (.up ℤ) n (Q.X n)).inv ≫ (s.ι.app ⟨n⟩).f n
      comm' := by
        intro i j hij
        change ((HomologicalComplex.singleObjXSelf (.up ℤ) i (Q.X i)).inv ≫
          (s.ι.app ⟨i⟩).f i) ≫ s.pt.d i j = Q.d i j ≫ _
        rw [hd, zero_comp, Category.assoc]
        have h := (s.ι.app ⟨i⟩).comm i j
        change (s.ι.app ⟨i⟩).f i ≫ s.pt.d i j = 0 ≫ (s.ι.app ⟨i⟩).f j at h
        simpa only [zero_comp, comp_zero] using
          congrArg (fun f ↦ (HomologicalComplex.singleObjXSelf (.up ℤ) i (Q.X i)).inv ≫ f) h }
  fac s j := by
    apply HomologicalComplex.from_single_hom_ext
    simp [singleCofan]
  uniq s m hm := by
    apply HomologicalComplex.Hom.ext
    funext n
    have h := congrArg (fun f ↦ f.f n) (hm ⟨n⟩)
    simpa [singleCofan, Category.assoc] using
      congrArg (fun f ↦ (HomologicalComplex.singleObjXSelf (.up ℤ) n (Q.X n)).inv ≫ f) h

-- Single flat modules are K-flat, and K-flatness is closed under coproducts.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem kFlat_of_zero_differential {R : Type u} [CommRing R]
    (Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hd : ∀ i j, Q.d i j = 0) (hf : ∀ n, Module.Free R (Q.X n)) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat Q := by
  apply ObjectProperty.prop_of_isColimit _ (singleCofanIsColimit Q hd)
  intro n
  apply (kFlat_single_obj_iff_flat _ _).2
  apply (ModuleCat.flat_iff_flat _).2
  have := hf n.as
  infer_instance

-- Only degreewise splittings are needed to obtain a distinguished triangle in K(R).
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem kFlat_of_degreewise_split {R : Type u} [CommRing R]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [Mono f]
    (hsplit : ∀ n, ∃ r : L.X n ⟶ K.X n, f.f n ≫ r = 𝟙 _)
    (hK : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat K)
    (hQ : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat (cokernel f)) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat L := by
  classical
  let S := ShortComplex.cokernelSequence f
  have : Mono S.f := inferInstanceAs (Mono f)
  have : Epi S.g := inferInstanceAs (Epi (cokernel.π f))
  have hS : S.ShortExact := { exact := ShortComplex.cokernelSequence_exact f }
  let σ : ∀ n, (S.map (HomologicalComplex.eval (ModuleCat R) (.up ℤ) n)).Splitting :=
    fun n ↦
      ShortComplex.Splitting.ofExactOfRetraction _ (hS.map (HomologicalComplex.eval _ _ n)).exact
        (hsplit n).choose (hsplit n).choose_spec (hS.map (HomologicalComplex.eval _ _ n)).epi_g
  apply (HomotopyCategory.kFlat_quotient_obj_iff L).1
  exact ObjectProperty.ext_of_isTriangulatedClosed₂ _ (trianglehOfDegreewiseSplit S σ)
      ((HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit _).2
        ⟨S, σ, ⟨Iso.refl _⟩⟩)
      ((HomotopyCategory.kFlat_quotient_obj_iff K).2 hK)
      ((HomotopyCategory.kFlat_quotient_obj_iff (cokernel f)).2 hQ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def unionCocone {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)
    (ι : ∀ m, F m ⟶ C) (step : ∀ m, F m ⟶ F (m + 1))
    (hcompat : ∀ m, step m ≫ ι (m + 1) = ι m) :
    Cocone (Functor.ofSequence step) where
  pt := C
  ι := NatTrans.ofSequence ι (by simpa using hcompat)

-- Exhaustion gives surjectivity, and each stage inclusion is injective.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def unionIsColimit {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)
    (ι : ∀ m, F m ⟶ C) (step : ∀ m, F m ⟶ F (m + 1))
    (hmono : ∀ m, Mono (ι m))
    (hcompat : ∀ m, step m ≫ ι (m + 1) = ι m)
    (hexhaustive : ∀ (n : ℤ) (x : C.X n), ∃ (m : ℕ) (y : (F m).X n), (ι m).f n y = x) :
    IsColimit (unionCocone C F ι step hcompat) := by
  have : ReflectsColimitsOfShape ℕ (forget (ModuleCat.{u} R)) :=
    reflectsColimitsOfShape_of_equiv (AsSmall.equiv (C := ℕ)).symm _
  apply HomologicalComplex.isColimitOfEval
  intro n
  apply isColimitOfReflects (forget (ModuleCat R))
  apply Types.FilteredColimit.isColimitOf'
  · intro x
    obtain ⟨m, y, hy⟩ := hexhaustive n x
    exact ⟨m, y, hy.symm⟩
  · intro m x y hxy
    have := hmono m
    have hinj := (ModuleCat.mono_iff_injective ((ι m).f n)).1 inferInstance
    exact ⟨m, 𝟙 m, by simpa using hinj hxy⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- An exhaustive increasing sequence of subcomplexes, starting at zero, whose inclusions
split in each degree and whose successive quotients have zero differential and free terms,
has K-flat union. The monomorphisms `ι` identify `F m` with the subcomplexes of `C`;
`step` and `hcompat` express their increasing order. The quotient is the categorical
cokernel, which is the degreewise module quotient. Retractions are only degreewise,
not morphisms of complexes. No boundedness or finite-rank condition is imposed.
Source: Stacks Project, More on Algebra, Tags 0BYH, 06Y3 and 0H7X, proof of
lemma-resolution-filtered-complex, part (2).
(blueprint: lem-kun-split-cell-complex-kflat).

Proof:
1. A zero-differential complex is the coproduct of the complexes supported in each
   individual degree. The coproduct injections and universal property are constructed
   explicitly. Each free term is flat, so the library's single-complex K-flatness theorem
   applies. Closure of K-flatness under coproducts proves that each quotient is K-flat.
2. Apply `ShortComplex.Splitting.ofExactOfRetraction` degreewise to the cokernel sequence
   of each stage inclusion. The resulting degreewise split sequence gives a distinguished
   triangle in the homotopy category. K-flatness is triangulated there, so K-flatness of
   the previous stage and quotient implies K-flatness of the next stage. Induction starts
   with the zero complex.
3. Build the sequential diagram and its cocone with vertex `C`. Evaluation in each degree,
   followed by the forgetful functor to types, identifies this as a filtered colimit:
   exhaustion supplies every element, and monicity gives the required injectivity.
   Reflection by the forgetful functor and degreewise evaluation gives the colimit in
   complexes. Modules have exact filtered colimits, and tensoring preserves colimits,
   so the library's colimit-closure theorem proves K-flatness of `C`.

This follows the finite-stage induction and filtered-union argument of Tags 0BYH, 06Y3,
and 0H7X, using the proved categorical closure results directly for ordinary modules.
-/
theorem kFlat_of_split_free_cells {R : Type u} [CommRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (F : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)
    (ι : ∀ m : ℕ, F m ⟶ C) (step : ∀ m : ℕ, F m ⟶ F (m + 1))
    (hzero : IsZero (F 0))
    (hmono : ∀ m : ℕ, Mono (ι m))
    (hcompat : ∀ m : ℕ, step m ≫ ι (m + 1) = ι m)
    (hexhaustive : ∀ (n : ℤ) (x : C.X n),
      ∃ (m : ℕ) (y : (F m).X n), (ι m).f n y = x)
    (hsplit : ∀ (m : ℕ) (n : ℤ),
      ∃ r : (F (m + 1)).X n ⟶ (F m).X n,
        (step m).f n ≫ r = 𝟙 ((F m).X n))
    (hquot_d : ∀ (m : ℕ) (n : ℤ), (cokernel (step m)).d n (n + 1) = 0)
    (hquot_free : ∀ (m : ℕ) (n : ℤ), Module.Free R ((cokernel (step m)).X n)) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)).kFlat C := by
  have hF : ∀ m, (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat (F m) := by
    intro m
    induction m with
    | zero => exact ObjectProperty.prop_of_isZero _ hzero
    | succ m ih =>
      have := hmono m
      have : Mono (step m) := mono_of_mono_fac (hcompat m)
      apply kFlat_of_degreewise_split (step m) (hsplit m) ih
      apply kFlat_of_zero_differential _ _ (hquot_free m)
      intro i j
      by_cases hij : i + 1 = j
      · subst j
        exact hquot_d m i
      · exact (cokernel (step m)).shape i j hij
  have : HasExactColimitsOfShape ℕ (ModuleCat.{u} R) :=
    HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} R)
      (AsSmall.equiv (C := ℕ)).symm
  have (M : ModuleCat.{u} R) : PreservesColimitsOfShape ℕ
      ((MonoidalCategory.curriedTensor (ModuleCat.{u} R)).flip.obj M) :=
    inferInstanceAs (PreservesColimitsOfShape ℕ (MonoidalCategory.tensorRight M))
  exact ObjectProperty.prop_of_isColimit _
    (unionIsColimit C F ι step hmono hcompat hexhaustive) hF

end CochainComplex

