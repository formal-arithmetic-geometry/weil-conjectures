/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T3
-/
module

public import Sheaf.SixFunctors.ProEtale.DerivedCompletion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Sheaf.Topology.ProfiniteCondensedRing

/-! The signed comparison between a shifted Roos complex and the Roos complex
of a shifted input, including its augmentation.
Source: blueprint main-20261015, first-reduction lemma, Cones paragraph
(blueprint: det-pe-derived-nakayama-roos-shift-comparison).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory

private def shiftProductIso {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCountableProducts C] (P : ℕ → CochainComplex C ℤ) (r : ℤ) :
    (∏ᶜ fun n ↦ P n⟦r⟧) ≅ (∏ᶜ P)⟦r⟧ := by
  let F := shiftFunctor (CochainComplex C ℤ) r
  have : PreservesLimitsOfSize.{0,0} F :=
    (shiftEquiv (CochainComplex C ℤ) r).symm.toAdjunction.rightAdjoint_preservesLimits
  exact (PreservesProduct.iso F P).symm

private theorem shiftProductIso_π {C : Type u} [Category.{v} C] [Preadditive C]
    [HasCountableProducts C] (P : ℕ → CochainComplex C ℤ) (r : ℤ) (n : ℕ) :
    (shiftProductIso P r).hom ≫ (Pi.π P n)⟦r⟧' =
      Pi.π (fun n ↦ P n⟦r⟧) n := by
  let F := shiftFunctor (CochainComplex C ℤ) r
  have : PreservesLimitsOfSize.{0,0} F :=
    (shiftEquiv (CochainComplex C ℤ) r).symm.toAdjunction.rightAdjoint_preservesLimits
  change (PreservesProduct.iso F P).inv ≫ F.map (Pi.π P n) = _
  apply (cancel_epi (PreservesProduct.iso F P).hom).1
  simp only [Iso.hom_inv_id_assoc]
  exact (piComparison_comp_π F P n).symm

universe w
-- Keep instance inference from unfolding the inverse-image monoidal construction.
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  AlgebraicGeometry.ProEtale.monoidal_upperStarFromPoint

namespace AlgebraicGeometry.ProEtale.AdicCompletion
variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{w})
private def productShiftIso (P : CochainComplex (Modules l E X) ℤ) (r : ℤ) :
    product l E X (P⟦r⟧) ≅ (product l E X P)⟦r⟧ :=
  Limits.Pi.mapIso (fun n : ℕ ↦ ((level l E X n).commShiftIso r).app P) ≪≫
    shiftProductIso (fun n : ℕ ↦ (level l E X n).obj P) r

private theorem productShiftIso_π (P : CochainComplex (Modules l E X) ℤ) (r : ℤ)
    (n : ℕ) :
    (productShiftIso l E X P r).hom ≫
      (shiftFunctor (CochainComplex (Modules l E X) ℤ) r).map
        (Pi.π (fun n : ℕ ↦ (level l E X n).obj P) n) =
      Pi.π (fun n : ℕ ↦ (level l E X n).obj (P⟦r⟧)) n ≫
        ((level l E X n).commShiftIso r).hom.app P := by
  dsimp only [productShiftIso, Iso.trans_hom]
  rw [Category.assoc, shiftProductIso_π]
  simp

private theorem productShiftIso_f_π (P : CochainComplex (Modules l E X) ℤ)
    (r i : ℤ) (n : ℕ) :
    (productShiftIso l E X P r).hom.f i ≫
      (Pi.π (fun n : ℕ ↦ (level l E X n).obj P) n).f (i + r) =
      (Pi.π (fun n : ℕ ↦ (level l E X n).obj (P⟦r⟧)) n).f i := by
  have h := congrArg (fun a ↦ a.f i) (productShiftIso_π l E X P r n)
  simpa using h

private def productXIso (P : CochainComplex (Modules l E X) ℤ) (i : ℤ) :
    (product l E X P).X i ≅ ∏ᶜ (fun n : ℕ ↦ P.X i ⊗ finiteModule l E X n) :=
  asIso (piComparison (HomologicalComplex.eval (Modules l E X) (.up ℤ) i)
    (fun n : ℕ ↦ (level l E X n).obj P))

private theorem productShiftIso_step (P : CochainComplex (Modules l E X) ℤ) (r : ℤ) :
    oneSubShift l E X (P⟦r⟧) ≫ (productShiftIso l E X P r).hom =
      (productShiftIso l E X P r).hom ≫
        (shiftFunctor (CochainComplex (Modules l E X) ℤ) r).map (oneSubShift l E X P) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply (cancel_mono (productXIso l E X P (i + r)).hom).1
  apply Pi.hom_ext
  intro n
  simp only [productXIso, asIso_hom, Category.assoc]
  erw [piComparison_comp_π]
  change (oneSubShift l E X (P⟦r⟧)).f i ≫
      (productShiftIso l E X P r).hom.f i ≫
        (Pi.π (fun n : ℕ ↦ (level l E X n).obj P) n).f (i + r) =
    (productShiftIso l E X P r).hom.f i ≫
      (oneSubShift l E X P).f (i + r) ≫ (Pi.π (fun n : ℕ ↦ (level l E X n).obj P) n).f (i + r)
  rw [productShiftIso_f_π]
  have hn := congrArg (fun a ↦ a.f i)
    ((towerTransitionEndomorphism_eq_iff (K := fun n : ℕ ↦ (level l E X n).obj (P⟦r⟧))
      (levelStep l E X (P⟦r⟧)) _).1 rfl n)
  have hn' := congrArg (fun a ↦ a.f (i + r))
    ((towerTransitionEndomorphism_eq_iff (K := fun n : ℕ ↦ (level l E X n).obj P)
      (levelStep l E X P) _).1 rfl n)
  simp only [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply] at hn hn'
  dsimp only [oneSubShift] at *
  erw [hn, hn']
  simp only [Preadditive.comp_sub, productShiftIso_f_π]
  congr 1
  change _ ≫ _ = _ ≫ _ ≫ _
  rw [← Category.assoc, productShiftIso_f_π]
  rfl

private def signIso {C : Type u} [Category.{v} C] [Preadditive C]
    (A : C) (r : ℤ) : A ≅ A where
  hom := r.negOnePow • 𝟙 A
  inv := r.negOnePow • 𝟙 A
  hom_inv_id := by simp [Linear.comp_units_smul, smul_smul]
  inv_hom_id := by simp [Linear.comp_units_smul, smul_smul]

private def roosShiftXIso (P : CochainComplex (Modules l E X) ℤ) (r i : ℤ) :
    (roos l E X (P⟦r⟧)).X i ≅ ((roos l E X P)⟦r⟧).X i :=
  biprod.mapIso (HomologicalComplex.Hom.isoApp (productShiftIso l E X P r) i)
    (HomologicalComplex.Hom.isoApp (productShiftIso l E X P r) (i - 1) ≪≫
      eqToIso (congrArg (product l E X P).X (by omega : i - 1 + r = i + r - 1)) ≪≫
      signIso _ r)

private theorem roos_d (P : CochainComplex (Modules l E X) ℤ)
    (i j : ℤ) (h : i + 1 = j) :
    (roos l E X P).d i j =
      biprod.lift (biprod.fst ≫ (product l E X P).d i j)
        (biprod.fst ≫ (oneSubShift l E X P).f i ≫
          eqToHom (congrArg (product l E X P).X (by omega : i = j - 1)) -
          biprod.snd ≫ (product l E X P).d (i - 1) (j - 1)) := by
  subst j
  simp only [roos, CochainComplex.of_d, roosD]

private theorem matrix_shift_comm {C : Type u} [Category.{v} C] [Preadditive C]
    [HasBinaryBiproducts C] (M N : CochainComplex C ℤ) (r i : ℤ)
    (s : M ⟶ M) (t : N ⟶ N) (a : ∀ k : ℤ, N.X k ⟶ M.X (k + r))
    (ha : ∀ k k' : ℤ, a k ≫ (r.negOnePow • M.d (k + r) (k' + r)) =
      N.d k k' ≫ a k')
    (hs : ∀ k : ℤ, t.f k ≫ a k = a k ≫ s.f (k + r)) :
    biprod.map (a i)
        (r.negOnePow • (a (i - 1)) ≫
          eqToHom (congrArg M.X (by omega : i - 1 + r = i + r - 1))) ≫
      (r.negOnePow • biprod.lift (biprod.fst ≫ M.d (i + r) (i + 1 + r))
        (biprod.fst ≫ s.f (i + r) ≫
          eqToHom (congrArg M.X (by omega : i + r = i + 1 + r - 1)) -
          biprod.snd ≫ M.d (i + r - 1) (i + 1 + r - 1))) =
    biprod.lift (biprod.fst ≫ N.d i (i + 1))
        (biprod.fst ≫ t.f i ≫
          eqToHom (congrArg N.X (by omega : i = i + 1 - 1)) -
          biprod.snd ≫ N.d (i - 1) (i + 1 - 1)) ≫
      biprod.map (a (i + 1))
        (r.negOnePow • (a (i + 1 - 1)) ≫
          eqToHom (congrArg M.X (by omega : i + 1 - 1 + r = i + 1 + r - 1))) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, Linear.comp_units_smul, Linear.units_smul_comp,
      biprod.lift_fst, biprod.map_fst, biprod.map_fst_assoc, biprod.lift_fst_assoc]
    have h := ha i (i + 1)
    simpa only [CochainComplex.shiftFunctor_obj_d', Linear.comp_units_smul,
      Category.assoc] using congrArg (fun f ↦ biprod.fst ≫ f) h
  · simp only [Category.assoc, Linear.comp_units_smul, Linear.units_smul_comp,
      biprod.lift_snd, biprod.map_snd, biprod.map_fst_assoc,
      biprod.map_snd_assoc, biprod.lift_snd_assoc,
      Preadditive.comp_sub, Preadditive.sub_comp]
    congr 1
    congr 1
    · rw [← eqToHom_naturality_assoc a (by omega : i = i + 1 - 1), eqToHom_trans]
      rw [← reassoc_of% (hs i)]
    · have hd := M.eqToHom_comp_d (i := i - 1 + r) (i' := i + r - 1)
        (j := i + 1 + r - 1) (by change i - 1 + r + 1 = _; omega)
        (by change i + r - 1 + 1 = _; omega)
      rw [hd]
      have hn := N.d_comp_eqToHom (i := i - 1) (j := i + 1 - 1) (j' := i)
        (by change i - 1 + 1 = _; omega) (by change i - 1 + 1 = i; omega)
      rw [← reassoc_of% hn]
      rw [← eqToHom_naturality_assoc a (by omega : i = i + 1 - 1), eqToHom_trans]
      have hm := M.d_comp_eqToHom (i := i - 1 + r) (j := i + 1 + r - 1)
        (j' := i + r) (by change i - 1 + r + 1 = _; omega)
        (by change i - 1 + r + 1 = i + r; omega)
      rw [← hm]
      simpa only [Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc] using
        congrArg (fun f ↦ biprod.snd ≫ f ≫
          eqToHom (congrArg M.X (by omega : i + r = i + 1 + r - 1))) (ha (i - 1) i)

private theorem roosShiftXIso_comm
    (P : CochainComplex (Modules l E X) ℤ) (r i : ℤ) :
    (roosShiftXIso l E X P r i).hom ≫ ((roos l E X P)⟦r⟧).d i (i + 1) =
      (roos l E X (P⟦r⟧)).d i (i + 1) ≫
        (roosShiftXIso l E X P r (i + 1)).hom := by
  simp only [roosShiftXIso, biprod.mapIso_hom, HomologicalComplex.Hom.isoApp_hom,
    Iso.trans_hom, eqToIso.hom, signIso, Linear.comp_units_smul, Category.comp_id]
  rw [CochainComplex.shiftFunctor_obj_d']
  rw [roos_d l E X P (i + r) (i + 1 + r) (by omega),
    roos_d l E X (P⟦r⟧) i (i + 1) rfl]
  exact matrix_shift_comm _ _ r i _ _
    (fun k ↦ (productShiftIso l E X P r).hom.f k)
    (fun k k' ↦ (productShiftIso l E X P r).hom.comm k k')
    (fun k ↦ congrArg (fun f ↦ f.f k) (productShiftIso_step l E X P r))

private theorem productShiftIso_unit
    (P : CochainComplex (Modules l E X) ℤ) (r i : ℤ) :
    (unitProduct l E X (P⟦r⟧)).f i ≫ (productShiftIso l E X P r).hom.f i =
      (unitProduct l E X P).f (i + r) := by
  apply (cancel_mono (productXIso l E X P (i + r)).hom).1
  apply Pi.hom_ext
  intro n
  simp only [productXIso, asIso_hom, Category.assoc]
  erw [piComparison_comp_π]
  change (unitProduct l E X (P⟦r⟧)).f i ≫
      (productShiftIso l E X P r).hom.f i ≫
        (Pi.π (fun n : ℕ ↦ (level l E X n).obj P) n).f (i + r) =
    (unitProduct l E X P).f (i + r) ≫ (Pi.π (fun n : ℕ ↦ (level l E X n).obj P) n).f (i + r)
  rw [productShiftIso_f_π]
  change ((unitProduct l E X (P⟦r⟧)) ≫ Pi.π _ n).f i =
    ((unitProduct l E X P) ≫ Pi.π _ n).f (i + r)
  simp only [unitProduct, Pi.lift_π]
  rfl

private def roosShiftIso (P : CochainComplex (Modules l E X) ℤ) (r : ℤ) :
    roos l E X (P⟦r⟧) ≅ (roos l E X P)⟦r⟧ :=
  HomologicalComplex.Hom.isoOfComponents (roosShiftXIso l E X P r) (by
    intro i j hij
    obtain rfl : i + 1 = j := hij
    exact roosShiftXIso_comm l E X P r i)

private theorem roosShiftIso_augmentation
    (P : CochainComplex (Modules l E X) ℤ) (r : ℤ) :
    augmentation l E X (P⟦r⟧) ≫ (roosShiftIso l E X P r).hom =
      (augmentation l E X P)⟦r⟧' := by
  apply HomologicalComplex.Hom.ext
  funext i
  change biprod.lift ((unitProduct l E X (P⟦r⟧)).f i) 0 ≫
    (roosShiftXIso l E X P r i).hom =
      biprod.lift ((unitProduct l E X P).f (i + r)) 0
  apply biprod.hom_ext
  · simpa only [roosShiftXIso, biprod.mapIso_hom,
      HomologicalComplex.Hom.isoApp_hom, Category.assoc, biprod.map_fst,
      biprod.lift_fst_assoc, biprod.lift_fst] using productShiftIso_unit l E X P r i
  · simp [roosShiftXIso]

end AlgebraicGeometry.ProEtale.AdicCompletion


namespace AlgebraicGeometry.ProEtale

/-- The explicit Roos complex commutes with shifts, preserving the specified augmentation.

Source: blueprint main-20261015, first-reduction lemma, Cones paragraph, shift comparison
(blueprint: det-pe-derived-nakayama-roos-shift-comparison).

Proof. Each reduction functor is induced term by term by an additive tensor functor,
so it commutes with shifts. The shift equivalence preserves countable products; hence
there is a chain isomorphism from product(P[r]) to product(P)[r], commuting with the
one-minus-shift endomorphisms, as is checked on every product projection. In degree i,
use this comparison on the first Roos coordinate, and its degree i-1 component multiplied
by (-1)^r on the second coordinate (with the canonical reindexing). The differential
is the matrix with diagonal entries d and -d and off-diagonal entry one-minus-shift.
The sign on the second coordinate makes this matrix commute with the shifted
differential, whose entries are all multiplied by (-1)^r. The inverse uses the inverse
product comparison and the same sign. The augmentation has second coordinate zero;
its first coordinate is the product of the tensor units, which commute with the termwise
shift comparison. Therefore the augmentation equation holds in every degree. -/
theorem derived_nakayama_roos_shift_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    (P : CochainComplex (AdicCompletion.Modules l E X) ℤ) (r : ℤ) :
    ∃ j : AdicCompletion.roos l E X (P⟦r⟧) ≅ (AdicCompletion.roos l E X P)⟦r⟧,
      AdicCompletion.augmentation l E X (P⟦r⟧) ≫ j.hom =
        (AdicCompletion.augmentation l E X P)⟦r⟧' := by
  exact ⟨AdicCompletion.roosShiftIso l E X P r,
    AdicCompletion.roosShiftIso_augmentation l E X P r⟩

end AlgebraicGeometry.ProEtale
