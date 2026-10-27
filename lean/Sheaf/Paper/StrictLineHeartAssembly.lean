/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q95
-/
module

public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Paper.StrictLineHeartReduction

/-! # Assembling shifted line orientations in strict coefficient towers

Source: blueprint, sec-smooth-purity, tower-geometric-gamma proof (1), removing
its common shift and assembling maps of tower sheaves
(blueprint: lem-sp-strict-line-heart-assembly).

The helpers only expose the chosen ordinary derived category in the recorded
coefficient-tower datum and the standard exact-evaluation single/shift comparisons.
Index n denotes the positive coefficient level n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale.SpStrictLineHeart

variable {l : ℕ} [Fact l.Prime] {E : Type u} [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] {T : Scheme.{t}}
  (A : SpCoefficientTowersAbelian l E T)

/-- The dependency's ordinary derived category of strict towers.
Source: tower-geometric-gamma proof (1) (blueprint: lem-sp-strict-line-heart-assembly). -/
abbrev D :=
  letI := A.hasDerived
  DerivedCategory (spCoefficientTowers l E T)

/-- Its degree-zero single embedding, with the same localization model.
Source: tower-geometric-gamma proof (1) (blueprint: lem-sp-strict-line-heart-assembly). -/
abbrev single :=
  letI := A.hasDerived
  DerivedCategory.singleFunctor (spCoefficientTowers l E T) 0

/-- Cohomology in the dependency's localization model.
Source: tower-geometric-gamma proof (1) (blueprint: lem-sp-strict-line-heart-assembly). -/
abbrev H (i : ℤ) :=
  letI := A.hasDerived
  DerivedCategory.homologyFunctor (spCoefficientTowers l E T) i

/-- The recorded exact evaluation, with its prescribed sectionwise normalization.
Source: tower-geometric-gamma proof (1) (blueprint: lem-sp-strict-line-heart-assembly). -/
abbrev evaluation (n : ℕ) := spCoefficientEvaluation l E T A.equivalence n

/-- Derived evaluation in that same model.
Source: tower-geometric-gamma proof (1) (blueprint: lem-sp-strict-line-heart-assembly). -/
abbrev ev (n : ℕ) :=
  letI := A.hasDerived
  letI := A.equivalenceAdditive
  letI := A.evaluationLimits n
  letI := A.evaluationColimits n
  (evaluation A n).mapDerivedCategory

/-- The standard H-zero identification on a degree-zero single object.
Source: Stacks 06XS; tower-geometric-gamma proof (1)
(blueprint: lem-sp-strict-line-heart-assembly). -/
abbrev singleH :=
  letI := A.hasDerived
  DerivedCategory.singleFunctorCompHomologyFunctorIso (spCoefficientTowers l E T) 0

/-- Canonical exact-evaluation comparison for a shifted degree-zero sheaf tower.
Source: Stacks 015F; tower-geometric-gamma proof (1)
(blueprint: lem-sp-strict-line-heart-assembly). -/
def evaluationSingleShift (M : spCoefficientTowers l E T) (n : ℕ) (s : ℤ) :
    (ev A n).obj (((single A).obj M)⟦s⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj ((evaluation A n).obj M))⟦s⟧ :=
  letI := A.hasDerived
  letI := A.equivalenceAdditive
  letI := A.evaluationLimits n
  letI := A.evaluationColimits n
  ((ev A n).commShiftIso s).app ((single A).obj M) ≪≫
    (shiftFunctor _ s).mapIso (((evaluation A n).mapDerivedCategorySingleFunctor 0).app M)

/-- Shift back a single-degree identification using the standard shift cancellation.
Source: tower-geometric-gamma proof (1) (blueprint: lem-sp-strict-line-heart-assembly). -/
def shiftedIdentification (V : D A) (s : ℤ)
    (j : (single A).obj ((H A 0).obj (V⟦-s⟧)) ≅ V⟦-s⟧) :
    ((single A).obj ((H A 0).obj (V⟦-s⟧)))⟦s⟧ ≅ V :=
  (shiftFunctor _ s).mapIso j ≪≫ shiftNegShift V s

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory

private theorem concentration (L : spCoefficientTowers l E T) (V : D A) (s : ℤ)
    (a : ∀ n : ℕ,
      ((DerivedCategory.singleFunctor _ 0).obj ((evaluation A n).obj L))⟦s⟧ ≅
        (ev A n).obj V) :
    ∀ i : ℤ, i ≠ 0 → IsZero ((H A i).obj (V⟦-s⟧)) := by
  let := A.hasDerived
  let := A.equivalenceAdditive
  let := A.evaluationLimits
  let := A.evaluationColimits
  intro i hi
  apply (IsZero.iff_id_eq_zero _).2
  apply A.equivalence.functor.map_injective
  apply strictRingSystem_hom_ext
  intro n
  have e : (ev A n).obj (V⟦-s⟧) ≅
      (DerivedCategory.singleFunctor _ 0).obj ((evaluation A n).obj L) :=
    ((ev A n).commShiftIso (-s)).app V ≪≫
      (shiftFunctor _ (-s)).mapIso (a n).symm ≪≫ shiftShiftNeg _ s
  have hz : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      ((DerivedCategory.singleFunctor _ 0).obj ((evaluation A n).obj L))) := by
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact DerivedCategory.isZero_of_isGE _ 0 i hi
    · exact DerivedCategory.isZero_of_isLE _ 0 i hi
  have hz' : IsZero ((evaluation A n).obj ((H A i).obj (V⟦-s⟧))) :=
    hz.of_iso (((evaluation A n).mapDerivedCategoryHomologyFunctorIso i).app (V⟦-s⟧) ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso e)
  change (evaluation A n).map (𝟙 _) = (evaluation A n).map 0
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).1 hz'

private theorem normalized_identification (K : D A)
    (h : ∀ i : ℤ, i ≠ 0 → IsZero ((H A i).obj K)) :
    ∃ j : (single A).obj ((H A 0).obj K) ≅ K,
      (H A 0).map j.hom = (singleH A).hom.app ((H A 0).obj K) := by
  let := A.hasDerived
  have : K.IsGE 0 := (DerivedCategory.isGE_iff K 0).2 (fun i hi ↦ h i (ne_of_lt hi))
  have : K.IsLE 0 := (DerivedCategory.isLE_iff K 0).2 (fun i hi ↦ h i (ne_of_gt hi))
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0
  let c : (H A 0).obj K ≅ Y := (H A 0).mapIso e ≪≫ (singleH A).app Y
  refine ⟨(single A).mapIso c ≪≫ e.symm, ?_⟩
  change (H A 0).map ((single A).map c.hom ≫ e.inv) = _
  rw [CategoryTheory.Functor.map_comp]
  apply (cancel_mono ((H A 0).map e.hom ≫ (singleH A).hom.app Y)).1
  have he : (H A 0).map e.inv ≫ (H A 0).map e.hom = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, e.inv_hom_id,
      CategoryTheory.Functor.map_id]
  simp only [Category.assoc]
  rw [← Category.assoc ((H A 0).map e.inv), he, Category.id_comp]
  exact (singleH A).hom.naturality c.hom

private theorem evaluation_naturality {M N : spCoefficientTowers l E T}
    (f : M ⟶ N) (n : ℕ) (s : ℤ) :
    (ev A n).map (((single A).map f)⟦s⟧') ≫ (evaluationSingleShift A N n s).hom =
      (evaluationSingleShift A M n s).hom ≫
        ((DerivedCategory.singleFunctor _ 0).map ((evaluation A n).map f))⟦s⟧' := by
  let := A.hasDerived
  let := A.equivalenceAdditive
  let := A.evaluationLimits
  let := A.evaluationColimits
  have hs := ((ev A n).commShiftIso s).hom.naturality ((single A).map f)
  have ht := ((evaluation A n).mapDerivedCategorySingleFunctor 0).hom.naturality f
  dsimp only [evaluationSingleShift, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom]
  simp only [Iso.app_hom, Category.assoc]
  change (ev A n).map (((single A).map f)⟦s⟧') ≫
      ((ev A n).commShiftIso s).hom.app ((single A).obj N) =
    ((ev A n).commShiftIso s).hom.app ((single A).obj M) ≫
      ((ev A n).map ((single A).map f))⟦s⟧' at hs
  change (ev A n).map ((single A).map f) ≫
      ((evaluation A n).mapDerivedCategorySingleFunctor 0).hom.app N =
    ((evaluation A n).mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor _ 0).map ((evaluation A n).map f) at ht
  rw [← Category.assoc, hs, Category.assoc,
    ← CategoryTheory.Functor.map_comp, ht, CategoryTheory.Functor.map_comp]

/-- Compatible prescribed shifted line orientations assemble through the heart.

Source: blueprint tower-geometric-gamma proof (1), retained proof step 3;
Stacks 08J5, 06XS, 015F, 06YY, 07A6, 09T5 and 03CZ
(blueprint: lem-sp-strict-line-heart-assembly).

Proof:
1. Exact evaluation commutes with shifts and cohomology. Each evaluated V[-s]
   is L_n in degree zero. The system-level left-extension theorem's joint bound
   detection proves that H^i(V[-s]) vanishes for i different from zero.
2. Concentration gives j: H^0(V[-s])[0] isomorphic to V[-s]. Normalize j by the
   inverse of its H^0 map and the standard single-H^0 identification. Full
   faithfulness of the single embedding makes this normalization unique. Exact
   derived cohomology coherence preserves it under evaluation. Full faithfulness
   at each level recovers the unique sheaf isomorphism alpha_n from a_n[-s].
3. Remove the common shift from the assumed reduction square, using shift
   compatibility of the canonical tower reductions. Naturality for j, followed
   by cancellation of j_m, gives the reduction square for alpha_n[0]. Locally
   finite free derived scalars identifies the derived scalar extension of L_n[0]
   with its ordinary scalar extension, without flatness of the quotient ring.
4. Transpose that square by the normalized derived scalar Hom comparison and
   the ordinary scalar adjunction. The tensor generator 1 tensor x identifies
   its two transposes with t^W alpha_n and Res(alpha_m) q^L. Faithfulness of the
   single embedding proves their equality in sheaves. Multiply by the inverse
   alpha maps to obtain the second transition identity.
5. These maps and their inverses are strict tower maps and give alpha: L iso W.
   Apply the single embedding, compose with j and shift by s, cancelling [-s][s].
   Its evaluation is exactly each prescribed a_n by the defining level equation.
-/
theorem strict_line_heart_assembly
    (_hT : IsUnit (l : Γ(T, ⊤))) (L : spCoefficientTowers l E T)
    (_hline : ∀ (n : ℕ) (X : T.ProEt), ∃ S : Sieve X,
      S ∈ Scheme.ProEt.topology T X ∧
      ∀ (U : T.ProEt) (f : U ⟶ X), S f →
        Nonempty (((evaluation A n).obj L).over U ≅
          unit (((spCoefficientRings l E T).obj (op n)).over U)))
    (_hcart : ∀ {m n : ℕ} (h : m ≤ n), IsIso ((A.ordinaryReduction h).app L))
    (V : D A) (s : ℤ)
    (a : ∀ n : ℕ,
      ((DerivedCategory.singleFunctor _ 0).obj ((evaluation A n).obj L))⟦s⟧ ≅
        (ev A n).obj V)
    (_ha : ∀ {m n : ℕ} (h : m ≤ n),
      (systemDerivedTensor A.scalar (spCoefficientCommRings l E T) h).map
          ((evaluationSingleShift A L n s).hom ≫ (a n).hom) ≫
          (A.reduction h).app V =
        (A.reduction h).app (((single A).obj L)⟦s⟧) ≫
          (evaluationSingleShift A L m s).hom ≫ (a m).hom) :
    (∀ i : ℤ, i ≠ 0 → IsZero ((H A i).obj (V⟦-s⟧))) ∧
    ∃ (j : (single A).obj ((H A 0).obj (V⟦-s⟧)) ≅ V⟦-s⟧)
      (alpha : L ≅ (H A 0).obj (V⟦-s⟧)),
      (H A 0).map j.hom = (singleH A).hom.app ((H A 0).obj (V⟦-s⟧)) ∧
      (∀ (n : ℕ) (beta : (evaluation A n).obj L ≅
          (evaluation A n).obj ((H A 0).obj (V⟦-s⟧))),
        ((DerivedCategory.singleFunctor _ 0).map beta.hom)⟦s⟧' ≫
            (evaluationSingleShift A ((H A 0).obj (V⟦-s⟧)) n s).inv ≫
            (ev A n).map (shiftedIdentification A V s j).hom = (a n).hom ↔
          beta = (evaluation A n).mapIso alpha) ∧
      (∀ {m n : ℕ} (h : m ≤ n),
        ((A.equivalence.functor.mapIso alpha).hom.app n) ≫
            (A.equivalence.functor.obj ((H A 0).obj (V⟦-s⟧))).transition h =
          (A.equivalence.functor.obj L).transition h ≫
            (systemRestriction (spCoefficientCommRings l E T) h).map
              ((A.equivalence.functor.mapIso alpha).hom.app m)) ∧
      (∀ {m n : ℕ} (h : m ≤ n),
        (A.equivalence.functor.obj ((H A 0).obj (V⟦-s⟧))).transition h ≫
            (systemRestriction (spCoefficientCommRings l E T) h).map
              ((A.equivalence.functor.mapIso alpha).inv.app m) =
          ((A.equivalence.functor.mapIso alpha).inv.app n) ≫
            (A.equivalence.functor.obj L).transition h) ∧
      ∃ b : ((single A).obj L)⟦s⟧ ≅ V,
        b = (shiftFunctor _ s).mapIso ((single A).mapIso alpha) ≪≫
          shiftedIdentification A V s j ∧
        ∀ n : ℕ,
          (evaluationSingleShift A L n s).inv ≫ (ev A n).map b.hom = (a n).hom := by
  let := A.hasDerived
  let := A.equivalenceAdditive
  let := A.evaluationLimits
  let := A.evaluationColimits
  have hc := concentration A L V s a
  obtain ⟨j, hj⟩ := normalized_identification A (V⟦-s⟧) hc
  let W := (H A 0).obj (V⟦-s⟧)
  let J := shiftedIdentification A V s j
  let F := fun n : ℕ ↦
    DerivedCategory.singleFunctor
      (systemLevel.{t + 1, t, max u (t + 1)} (spCoefficientCommRings l E T) n) 0 ⋙
      shiftFunctor _ s
  let beta := fun n ↦ (F n).preimageIso
    (a n ≪≫ (ev A n).mapIso J.symm ≪≫ evaluationSingleShift A W n s)
  have hb0 (n : ℕ) :
      ((DerivedCategory.singleFunctor _ 0).map (beta n).hom)⟦s⟧' =
        (a n).hom ≫ (ev A n).map J.inv ≫ (evaluationSingleShift A W n s).hom := by
    exact (F n).map_preimage _
  have hb (n : ℕ) :
      ((DerivedCategory.singleFunctor _ 0).map (beta n).hom)⟦s⟧' ≫
          (evaluationSingleShift A W n s).inv ≫ (ev A n).map J.hom = (a n).hom := by
    rw [hb0]
    simp only [Category.assoc, Iso.hom_inv_id_assoc,
      ← CategoryTheory.Functor.map_comp, J.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  let g := fun n ↦ (evaluationSingleShift A L n s).hom ≫
    ((DerivedCategory.singleFunctor _ 0).map (beta n).hom)⟦s⟧' ≫
      (evaluationSingleShift A W n s).inv
  have hg (n : ℕ) : g n =
      ((evaluationSingleShift A L n s).hom ≫ (a n).hom) ≫ (ev A n).map J.inv := by
    dsimp only [g]
    rw [hb0]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hred : ∀ {m n : ℕ} (h : m ≤ n),
      (systemDerivedTensor A.scalar (spCoefficientCommRings l E T) h).map (g n) ≫
          (A.reduction h).app (((single A).obj W)⟦s⟧) =
        (A.reduction h).app (((single A).obj L)⟦s⟧) ≫ g m := by
    intro m n h
    rw [hg n, hg m, CategoryTheory.Functor.map_comp, Category.assoc]
    have hn := (A.reduction h).naturality J.inv
    change (systemDerivedTensor A.scalar (spCoefficientCommRings l E T) h).map
        ((ev A n).map J.inv) ≫ (A.reduction h).app (((single A).obj W)⟦s⟧) =
      (A.reduction h).app V ≫ (ev A m).map J.inv at hn
    rw [hn, ← Category.assoc, _ha h, Category.assoc]
  have hcomm : ∀ {m n : ℕ} (h : m ≤ n),
      (beta n).hom ≫ (A.equivalence.functor.obj W).transition h =
        (A.equivalence.functor.obj L).transition h ≫
          (systemRestriction (spCoefficientCommRings l E T) h).map (beta m).hom := by
    exact shifted_single_reduction_detects_transition A L W s
      (fun n ↦ (beta n).hom) (fun h ↦ hred h)
  let f : A.equivalence.functor.obj L ⟶ A.equivalence.functor.obj W :=
    { app := fun n ↦ (beta n).hom
      comm := hcomm }
  have : IsIso f := (strictRingSystem_isIso_iff (spCoefficientCommRings l E T) f).2 (fun n ↦ by
    change IsIso (beta n).hom
    infer_instance)
  let alpha : L ≅ W := A.equivalence.functor.preimageIso (asIso f)
  have halpha (n : ℕ) : (evaluation A n).mapIso alpha = beta n := by
    apply Iso.ext
    change (A.equivalence.functor.map alpha.hom).app n = _
    have he : A.equivalence.functor.map alpha.hom = f :=
      A.equivalence.functor.map_preimage f
    exact congrArg (fun k ↦ k.app n) he
  refine ⟨hc, j, alpha, hj, ?_, ?_, ?_, ?_⟩
  · intro n gamma
    rw [halpha]
    constructor
    · intro hgamma
      apply (F n).mapIso_injective
      apply Iso.ext
      change ((DerivedCategory.singleFunctor _ 0).map gamma.hom)⟦s⟧' =
        ((DerivedCategory.singleFunctor _ 0).map (beta n).hom)⟦s⟧'
      apply (cancel_mono
        ((evaluationSingleShift A W n s).inv ≫ (ev A n).map J.hom)).1
      simpa only [Category.assoc] using hgamma.trans (hb n).symm
    · rintro rfl
      exact hb n
  · intro m n h
    exact (A.equivalence.functor.map alpha.hom).comm h
  · intro m n h
    exact (A.equivalence.functor.map alpha.inv).comm h |>.symm
  · refine ⟨(shiftFunctor _ s).mapIso ((single A).mapIso alpha) ≪≫ J, rfl, ?_⟩
    intro n
    change (evaluationSingleShift A L n s).inv ≫
      (ev A n).map (((single A).map alpha.hom)⟦s⟧' ≫ J.hom) = _
    rw [(ev A n).map_comp]
    have hn := evaluation_naturality A alpha.hom n s
    have hb' := hb n
    rw [← halpha n] at hb'
    change ((DerivedCategory.singleFunctor _ 0).map
        ((evaluation A n).map alpha.hom))⟦s⟧' ≫
      (evaluationSingleShift A W n s).inv ≫ (ev A n).map J.hom = _ at hb'
    refine Eq.trans ?_ hb'
    apply (cancel_epi (evaluationSingleShift A L n s).hom).1
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← hn]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

end AlgebraicGeometry.ProEtale.SpStrictLineHeart
