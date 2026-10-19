/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.AlgebraicGeometry.FlatTelescopeStageMap
public import Sheaf.AlgebraicGeometry.BoundedFlatShiftRepresentative
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct

/-! # Literal telescope models for a countable coproduct

Source: steps 1--2 of lem-sc-flat-telescope-sum-comparison-is-iso, expanding
Stacks Tags 06YS and 06YJ. (blueprint: lem-sc-flat-telescope-sum-models).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

section PartialSums

variable {C : Type*} [Category C] [Preadditive C]
  [HasBinaryBiproducts C] [HasCountableCoproducts C]

private noncomputable def partialSum (E : ℕ → C) : ℕ → C
  | 0 => E 0
  | n + 1 => partialSum E n ⊞ E (n + 1)

private noncomputable def partialSumAug (E : ℕ → C) : ∀ n, partialSum E n ⟶ ∐ E
  | 0 => Sigma.ι E 0
  | n + 1 => biprod.desc (partialSumAug E n) (Sigma.ι E (n + 1))

private noncomputable def partialSumLast (E : ℕ → C) : ∀ n, E n ⟶ partialSum E n
  | 0 => 𝟙 _
  | _ + 1 => biprod.inr

private noncomputable def partialSumStep (E : ℕ → C) (n : ℕ) :
    partialSum E n ⟶ partialSum E (n + 1) := biprod.inl

private noncomputable def partialSumLeft (E : ℕ → C) :
    ∀ n, partialSum E n ⟶ ∐ partialSum E
  | 0 => 0
  | n + 1 => biprod.fst ≫ (partialSumLeft E n - Sigma.ι (partialSum E) n)

private noncomputable def partialSumDelta (E : ℕ → C) :
    (∐ partialSum E) ⟶ ∐ partialSum E :=
  𝟙 _ - Sigma.desc (fun n ↦ partialSumStep E n ≫ Sigma.ι (partialSum E) (n + 1))

private lemma partialSumDelta_ι (E : ℕ → C) (n : ℕ) :
    Sigma.ι (partialSum E) n ≫ partialSumDelta E =
      Sigma.ι (partialSum E) n - partialSumStep E n ≫
        Sigma.ι (partialSum E) (n + 1) := by
  simp [partialSumDelta, Preadditive.comp_sub]

private noncomputable def partialSumSequence (E : ℕ → C) : ShortComplex C :=
  ShortComplex.mk (partialSumDelta E) (Sigma.desc (partialSumAug E)) (by
    apply Sigma.hom_ext
    intro n
    rw [← Category.assoc, partialSumDelta_ι]
    simp [partialSumStep, partialSumAug, Preadditive.sub_comp, Category.assoc])

set_option backward.isDefEq.respectTransparency false in
private noncomputable def partialSumSplitting (E : ℕ → C) :
    (partialSumSequence E).Splitting where
  r := Sigma.desc (partialSumLeft E)
  s := Sigma.desc (fun n ↦ partialSumLast E n ≫ Sigma.ι (partialSum E) n)
  f_r := by
    change partialSumDelta E ≫ Sigma.desc (partialSumLeft E) = 𝟙 _
    apply Sigma.hom_ext
    intro n
    rw [← Category.assoc, partialSumDelta_ι]
    simp only [Preadditive.sub_comp, Category.assoc, Sigma.ι_desc, Category.comp_id]
    change partialSumLeft E n - biprod.inl ≫
      (biprod.fst ≫ (partialSumLeft E n - Sigma.ι (partialSum E) n)) = _
    simp only [← Category.assoc, biprod.inl_fst, Category.id_comp, sub_sub_cancel]
  s_g := by
    change (Sigma.desc fun n ↦ partialSumLast E n ≫ Sigma.ι (partialSum E) n) ≫
      Sigma.desc (partialSumAug E) = 𝟙 _
    apply Sigma.hom_ext
    intro n
    cases n <;> simp [partialSumLast, partialSumAug, Category.assoc]
  id := by
    change Sigma.desc (partialSumLeft E) ≫ partialSumDelta E +
      Sigma.desc (partialSumAug E) ≫
        Sigma.desc (fun n ↦ partialSumLast E n ≫ Sigma.ι (partialSum E) n) =
      𝟙 (∐ partialSum E)
    apply Sigma.hom_ext
    intro n
    simp only [Preadditive.comp_add, ← Category.assoc, Sigma.ι_desc, Category.comp_id]
    induction n with
    | zero => simp [partialSumLeft, partialSumAug, partialSumLast]
    | succ n ih =>
      apply biprod.hom_ext'
      · simp only [Preadditive.comp_add, partialSumLeft, partialSumAug, Category.assoc,
          biprod.inl_fst_assoc, biprod.inl_desc_assoc, Preadditive.sub_comp]
        rw [sub_add_eq_add_sub, ih, partialSumDelta_ι]
        simp [partialSumStep]
      · simp [partialSumLeft, partialSumAug, partialSumLast,
          Preadditive.comp_add, Category.assoc]

private noncomputable def constantLeft (X : C) : ℕ → (X ⟶ ∐ fun _ : ℕ ↦ X)
  | 0 => 0
  | n + 1 => constantLeft X n - Sigma.ι (fun _ : ℕ ↦ X) n

private noncomputable def constantDelta (X : C) :
    (∐ fun _ : ℕ ↦ X) ⟶ ∐ fun _ : ℕ ↦ X :=
  𝟙 _ - Sigma.desc (fun n : ℕ ↦ Sigma.ι (fun _ : ℕ ↦ X) (n + 1))

omit [HasBinaryBiproducts C] in
private lemma constantDelta_ι (X : C) (n : ℕ) :
    Sigma.ι (fun _ : ℕ ↦ X) n ≫ constantDelta X =
      Sigma.ι (fun _ : ℕ ↦ X) n - Sigma.ι (fun _ : ℕ ↦ X) (n + 1) := by
  simp [constantDelta, Preadditive.comp_sub]

private noncomputable def constantSequence (X : C) : ShortComplex C :=
  ShortComplex.mk (constantDelta X) (Sigma.desc (fun _ : ℕ ↦ 𝟙 X)) (by
    apply Sigma.hom_ext
    intro n
    rw [← Category.assoc, constantDelta_ι]
    simp [Preadditive.sub_comp])

private noncomputable def constantSplitting (X : C) : (constantSequence X).Splitting where
  r := Sigma.desc (constantLeft X)
  s := Sigma.ι (fun _ : ℕ ↦ X) 0
  f_r := by
    change constantDelta X ≫ Sigma.desc (constantLeft X) = 𝟙 _
    apply Sigma.hom_ext
    intro n
    rw [← Category.assoc, constantDelta_ι]
    simp [Preadditive.sub_comp, constantLeft]
  s_g := by
    change Sigma.ι (fun _ : ℕ ↦ X) 0 ≫ Sigma.desc (fun _ : ℕ ↦ 𝟙 X) = 𝟙 _
    simp
  id := by
    change Sigma.desc (constantLeft X) ≫ constantDelta X +
      Sigma.desc (fun _ : ℕ ↦ 𝟙 X) ≫ Sigma.ι (fun _ : ℕ ↦ X) 0 = 𝟙 _
    apply Sigma.hom_ext
    intro n
    simp only [Preadditive.comp_add, ← Category.assoc, Sigma.ι_desc,
      Category.id_comp, Category.comp_id]
    induction n with
    | zero => simp [constantLeft]
    | succ n ih =>
      simp only [constantLeft, Preadditive.sub_comp]
      rw [sub_add_eq_add_sub, ih, constantDelta_ι, sub_sub_cancel]

end PartialSums

section SplitCone

variable {C : Type*} [Category C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C]

private noncomputable def splitConeIso (S : ShortComplex (CochainComplex C ℤ))
    (σ : S.Splitting) :
    (HomotopyCategory.quotient C (.up ℤ)).obj (CochainComplex.mappingCone S.f) ≅
      (HomotopyCategory.quotient C (.up ℤ)).obj S.X₃ := by
  let τ (n : ℤ) := σ.map (HomologicalComplex.eval C (.up ℤ) n)
  let T := CochainComplex.trianglehOfDegreewiseSplit S τ
  have hT : T ∈ distTriang _ :=
    (HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit T).2
      ⟨S, τ, ⟨Iso.refl _⟩⟩
  exact CategoryTheory.Pretriangulated.Triangle.π₃.mapIso
    (CategoryTheory.Pretriangulated.isoTriangleOfIso₁₂
      (CochainComplex.mappingCone.triangleh S.f) T
      (HomotopyCategory.mappingCone_triangleh_distinguished S.f) hT
      (Iso.refl _) (Iso.refl _) (by simp [T, CochainComplex.mappingCone.triangleh]; rfl))

end SplitCone

private theorem flatOfIso {Y : Scheme.{u}}
    {M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace)}
    (e : M ≅ N) (hN : SheafOfModules.IsFlat N) : SheafOfModules.IsFlat M := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  change exactFunctor _ _ (MonoidalCategory.tensorRight N) at hN
  change exactFunctor _ _ (MonoidalCategory.tensorRight M)
  exact ObjectProperty.prop_of_iso _
    ((MonoidalCategory.curriedTensor _).flip.mapIso e.symm) hN

private theorem flatSum {Y : Scheme.{u}} {I : Type}
    (M : I → SheafOfModules.{u} (moduleRings Y.toRingedSpace))
    (hM : ∀ j, SheafOfModules.IsFlat (M j)) : SheafOfModules.IsFlat (∐ M) := by
  have h := SheafOfModules.isFlat_coproduct Y.sheaf
    (fun j : ULift.{u} I ↦ M j.down) (fun j ↦ hM j.down)
  exact flatOfIso (Limits.Sigma.reindex (Equiv.ulift : ULift.{u} I ≃ I) M).symm h

private theorem flatBiprod {Y : Scheme.{u}}
    {M N : SheafOfModules.{u} (moduleRings Y.toRingedSpace)}
    (hM : SheafOfModules.IsFlat M) (hN : SheafOfModules.IsFlat N) :
    SheafOfModules.IsFlat (M ⊞ N) := by
  apply flatOfIso (biprod.isoCoprod M N)
  exact flatSum _ (fun j ↦ by
    cases j
    · exact hM
    · exact hN)

private theorem flatComplexSum {Y : Scheme.{u}} {I : Type}
    (E : I → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hf : ∀ n i, SheafOfModules.IsFlat ((E n).X i)) (i : ℤ) :
    SheafOfModules.IsFlat ((∐ E).X i) := by
  exact flatOfIso
    (PreservesCoproduct.iso (HomologicalComplex.eval _ (.up ℤ) i) E)
    (flatSum _ (fun n ↦ hf n i))

private theorem zeroComplexSum {C : Type*} [Category C] [Preadditive C]
    {I : Type} [HasColimitsOfShape (Discrete I) C]
    (E : I → CochainComplex C ℤ) (i : ℤ) (hi : ∀ n, IsZero ((E n).X i)) :
    IsZero ((∐ E).X i) := by
  have hc := (Cofan.isColimitMapCoconeEquiv (HomologicalComplex.eval C (.up ℤ) i)
    E (Cofan.mk (∐ E) (Sigma.ι E))) (isColimitOfPreserves
      (HomologicalComplex.eval C (.up ℤ) i) (coproductIsCoproduct E))
  rw [IsZero.iff_id_eq_zero]
  apply Cofan.IsColimit.hom_ext hc
  intro n
  exact (hi n).eq_of_src _ _

private theorem partialSumBounded {Y : Scheme.{u}}
    (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hb : ∀ n, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i)) :
    ∀ n, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((partialSum E n).X i) := by
  intro n
  induction n with
  | zero => exact hb 0
  | succ n ih =>
    obtain ⟨b, hbN⟩ := ih
    obtain ⟨c, hc⟩ := hb (n + 1)
    refine ⟨max b c, fun i hi ↦ ?_⟩
    apply (Functor.mapBiprod (HomologicalComplex.eval _ (.up ℤ) i)
      (partialSum E n) (E (n + 1))).isZero_iff.2
    exact (biprod_isZero_iff _ _).2
      ⟨hbN i (lt_of_le_of_lt (le_max_left _ _) hi),
        hc i (lt_of_le_of_lt (le_max_right _ _) hi)⟩

private theorem partialSumFlat {Y : Scheme.{u}}
    (E : ℕ → CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hf : ∀ n i, SheafOfModules.IsFlat ((E n).X i)) :
    ∀ n i, SheafOfModules.IsFlat ((partialSum E n).X i) := by
  intro n
  induction n with
  | zero => exact hf 0
  | succ n ih =>
    intro i
    exact flatOfIso
      (Functor.mapBiprod (HomologicalComplex.eval _ (.up ℤ) i)
        (partialSum E n) (E (n + 1))) (flatBiprod (ih i) (hf (n + 1) i))

section HomotopyCoproduct

variable {C : Type*} [Category C] [Preadditive C] [HasCountableCoproducts C]

-- Assemble homotopies using the degreewise coproduct universal property.
private lemma sumHomotopy (K : ℕ → CochainComplex C ℤ) {L : CochainComplex C ℤ}
    (f g : ∐ K ⟶ L) (h : ∀ i, Homotopy (Sigma.ι K i ≫ f) (Sigma.ι K i ≫ g)) :
    Nonempty (Homotopy f g) := by
  let hc (n : ℤ) := isColimitOfPreserves
    (HomologicalComplex.eval C (.up ℤ) n) (coproductIsCoproduct K)
  let t (n m : ℤ) : Cocone (Discrete.functor K ⋙ HomologicalComplex.eval C (.up ℤ) n) :=
    { pt := L.X m
      ι := { app := fun i ↦ (h i.as).hom n m
             naturality := by
               rintro ⟨i⟩ ⟨j⟩ f
               obtain rfl := Discrete.eq_of_hom f
               simp } }
  let a (n m : ℤ) : (∐ K).X n ⟶ L.X m := (hc n).desc (t n m)
  have ha (i : ℕ) (n m : ℤ) : (Sigma.ι K i).f n ≫ a n m = (h i).hom n m :=
    (hc n).fac (t n m) ⟨i⟩
  refine ⟨{ hom := a, zero := ?_, comm := ?_ }⟩
  · intro n m hnm
    apply (hc n).hom_ext
    rintro ⟨i⟩
    simpa only [Functor.mapCocone_ι_app, Cofan.mk_ι_app, HomologicalComplex.eval_map,
      ha, comp_zero] using (h i).zero n m hnm
  · intro n
    apply (hc n).hom_ext
    rintro ⟨i⟩
    change (Sigma.ι K i).f n ≫ f.f n = _
    simp only [Functor.mapCocone_ι_app, Cofan.mk_ι_app, HomologicalComplex.eval_map,
      Preadditive.comp_add, dNext, prevD, AddMonoidHom.mk'_apply]
    rw [(Sigma.ι K i).comm_assoc, ha, ← Category.assoc, ha]
    exact (h i).comm n

private noncomputable def quotientCoproduct (K : ℕ → CochainComplex C ℤ) :
    IsColimit (Cofan.mk ((HomotopyCategory.quotient C (.up ℤ)).obj (∐ K))
      (fun i ↦ (HomotopyCategory.quotient C (.up ℤ)).map (Sigma.ι K i))) := by
  classical
  let q := HomotopyCategory.quotient C (.up ℤ)
  have hu (X : HomotopyCategory C (.up ℤ)) (a : ∀ i, q.obj (K i) ⟶ X) :
      ∃! d : q.obj (∐ K) ⟶ X, ∀ i, q.map (Sigma.ι K i) ≫ d = a i := by
    obtain ⟨J, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    choose f hf using fun i ↦ q.map_surjective (a i)
    refine ⟨q.map (Sigma.desc f), ?_, ?_⟩
    · intro i
      rw [← Functor.map_comp, Sigma.ι_desc, hf]
    · intro m hm
      obtain ⟨g, rfl⟩ := q.map_surjective m
      have h (i : ℕ) : Homotopy (Sigma.ι K i ≫ g) (Sigma.ι K i ≫ Sigma.desc f) :=
        HomotopyCategory.homotopyOfEq _ _ (by
          rw [Sigma.ι_desc, Functor.map_comp, hm, hf])
      exact HomotopyCategory.eq_of_homotopy _ _ (sumHomotopy K g (Sigma.desc f) h).some
  exact Cofan.IsColimit.mk _ (fun t ↦ (hu t.pt t.inj).choose)
    (fun t i ↦ (hu t.pt t.inj).choose_spec.1 i)
    (fun t m hm ↦ (hu t.pt t.inj).choose_spec.2 m hm)

end HomotopyCoproduct

private noncomputable def transportCoproduct {C : Type*} [Category C]
    {E T : ℕ → C} {S R : C} (j : ∀ n, E n ⟶ S)
    (h : IsColimit (Cofan.mk S j)) (e : S ≅ R) (a : ∀ n, T n ≅ E n) :
    IsColimit (Cofan.mk R (fun n ↦ (a n).hom ≫ j n ≫ e.hom)) := by
  refine Cofan.IsColimit.mk _
    (fun c ↦ e.inv ≫ Cofan.IsColimit.desc h (fun n ↦ (a n).inv ≫ c.inj n)) ?_ ?_
  · intro c n
    dsimp only [cofan_mk_inj]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [show j n ≫ Cofan.IsColimit.desc h (fun n ↦ (a n).inv ≫ c.inj n) =
      (a n).inv ≫ c.inj n from Cofan.IsColimit.fac h _ n]
    simp
  · intro c m hm
    apply (cancel_epi e.hom).1
    simp only [Iso.hom_inv_id_assoc]
    apply Cofan.IsColimit.hom_ext h
    intro n
    change j n ≫ (e.hom ≫ m) = _
    rw [Cofan.IsColimit.fac]
    apply (cancel_epi (a n).hom).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, cofan_mk_inj] using hm n

private theorem constantConeBounded {Y : Scheme.{u}}
    (E : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hb : ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero (E.X i)) :
    ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((CochainComplex.mappingCone (constantDelta E)).X i) := by
  obtain ⟨b, hb⟩ := hb
  refine ⟨b, fun i hi ↦ ?_⟩
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨zeroComplexSum _ _ (fun _ ↦ hb (i + 1) (by omega)),
    zeroComplexSum _ _ (fun _ ↦ hb i hi)⟩

private theorem constantConeFlat {Y : Scheme.{u}}
    (E : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hf : ∀ i, SheafOfModules.IsFlat (E.X i)) (i : ℤ) :
    SheafOfModules.IsFlat ((CochainComplex.mappingCone (constantDelta E)).X i) := by
  apply flatOfIso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod (constantDelta E) i (i + 1) rfl)
  exact flatBiprod (flatComplexSum _ (fun _ ↦ hf) (i + 1))
    (flatComplexSum _ (fun _ ↦ hf) i)

-- Preserve the original existential witness names in the statement.
set_option linter.unusedVariables false in
/-- A sum of individually bounded flat complexes admits a literal telescope model
and a coproduct cofan whose summands are bounded literal telescope models.

Source: steps 1--2 of lem-sc-flat-telescope-sum-comparison-is-iso, expanding
Stacks Tags 06YS and 06YJ.

Proof. Put B_n = E_0 + ... + E_n, with the split inclusion into B_(n+1),
and let R be the mapping cone of one minus transition on the coproduct of B_n.
Each B_n has flat terms and is bounded by the finite maximum of its stage bounds.
Reindex the double coproduct by pairs (n,j) with j <= n. For each j its contribution
is the constant identity tower on E_j, starting at n=j. The augmentation sums the
coordinates, and the section inserts into the first coordinate. One minus successor
identifies the direct sum with the augmentation kernel: the inverse sends a
zero-sum finite sequence to its finite partial sums. Its tail vanishes precisely
because the input sums to zero. These operations commute with differentials.
Equivalently, on the n-th tail coordinate define the retraction of one minus
successor by minus the sum of the preceding coordinate inclusions. This sum is
finite on each input summand, so the coproduct universal property defines a
cochain map without any choice of lifts. The retraction identities telescope:
delta followed by retraction is identity; retraction followed by delta plus
augmentation followed by section is identity. The split cone is therefore E_j
plus a contractible identity cone. Sum these
splittings to obtain q(sum E) isomorphic to qR.
For each j let T_j be the same identity-tower cone on E_j. Its terms are sums of
flat terms and it is bounded above by the bound of E_j increased by one.
The same splitting gives qT_j isomorphic to qE_j. Compose its augmentation,
the j-th coprojection and the inverse augmentation of R to obtain the cofan legs.
The homotopy quotient preserves this coproduct: degreewise coproducts assemble
both chain maps and homotopies, so restriction to the summands gives a bijection
on homotopy classes into every target. Transport that universal property along
the displayed homotopy isomorphisms. This also proves the assertion for zero
complexes and the empty scheme; no uniform bound on j is used.
(blueprint: lem-sc-flat-telescope-sum-models). -/
theorem exists_flat_telescope_sum_models (Y : Scheme.{u})
    (E : ℕ → CochainComplex
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hb : ∀ n : ℕ, ∃ b : ℤ, ∀ i : ℤ, b < i → IsZero ((E n).X i))
    (hf : ∀ (n : ℕ) (i : ℤ), SheafOfModules.IsFlat ((E n).X i)) :
    ∃ (R : CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (hR : isFlatTelescope Y R)
      (T : ℕ → CochainComplex
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (hT : ∀ n, isFlatTelescope Y (T n))
      (s : ∀ n, (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (T n) ⟶
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R),
      Nonempty ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (∐ E) ≅
        (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R) ∧
      (∀ n, boundedFlatShiftRepresentative Y
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (T n))) ∧
      Nonempty (IsColimit (Cofan.mk
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj R) s)) := by
  let q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)
  let R := CochainComplex.mappingCone (partialSumDelta E)
  have hR : isFlatTelescope Y R :=
    ⟨partialSum E, partialSumStep E, partialSumBounded E hb, partialSumFlat E hf, rfl⟩
  let T (n : ℕ) := CochainComplex.mappingCone (constantDelta (E n))
  have hT (n : ℕ) : isFlatTelescope Y (T n) := by
    refine ⟨fun _ ↦ E n, fun _ ↦ 𝟙 _, fun _ ↦ hb n, fun _ ↦ hf n, ?_⟩
    simp only [Category.id_comp]
    rfl
  let eR : q.obj (∐ E) ≅ q.obj R :=
    (splitConeIso (partialSumSequence E) (partialSumSplitting E)).symm
  let a (n : ℕ) : q.obj (T n) ≅ q.obj (E n) :=
    splitConeIso (constantSequence (E n)) (constantSplitting (E n))
  refine ⟨R, hR, T, hT, fun n ↦ (a n).hom ≫ q.map (Sigma.ι E n) ≫ eR.hom,
    ⟨eR⟩, ?_, ⟨transportCoproduct _ (quotientCoproduct E) eR a⟩⟩
  intro n
  exact ⟨T n, constantConeBounded (E n) (hb n), constantConeFlat (E n) (hf n),
    Or.inl rfl⟩

end AlgebraicGeometry
