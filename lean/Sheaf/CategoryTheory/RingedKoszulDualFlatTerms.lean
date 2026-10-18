/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSystem
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
import Sheaf.Algebra.Homology.HomComplexToSingle
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Sheaf.Algebra.Homology.KFlatCoefficientUniverse

/-! # Bounded flat terms of the actual finite Koszul dual

Source: Stacks Project, Tags 0913 and 06YQ. -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)

private def coproductSupportIso
    {A : Type*} [Category A] [HasZeroMorphisms A] {I : Type*}
    (X : I → A) (P : I → Prop) [HasCoproduct X] [HasCoproduct (fun i : Subtype P ↦ X i)]
    (hz : ∀ i, ¬ P i → IsZero (X i)) :
    ∐ X ≅ ∐ (fun i : Subtype P ↦ X i) := by
  classical
  refine
    { hom := Sigma.desc (fun i ↦ if h : P i then Sigma.ι (fun j : Subtype P ↦ X j) ⟨i, h⟩ else 0)
      inv := Sigma.desc (fun i ↦ Sigma.ι X i)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Sigma.hom_ext
    intro i
    by_cases h : P i
    · simp [h]
    · exact (hz i h).eq_of_src _ _
  · apply Sigma.hom_ext
    intro i
    simp [i.property]

private theorem finiteFree_coproduct
    {I : Type} [Finite I]
    (X : I → SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (hf : ∀ i, ∃ (S : Type u) (_ : Fintype S), Nonempty (X i ≅ SheafOfModules.free S)) :
    ∃ (S : Type u) (_ : Fintype S), Nonempty ((∐ X) ≅ SheafOfModules.free S) := by
  classical
  choose S hS e using hf
  exact ⟨Σ i, S i, Fintype.ofFinite _, ⟨Sigma.mapIso (fun i ↦ (e i).some) ≪≫
    sigmaSigmaIso S (fun _ _ ↦ SheafOfModules.unit _)⟩⟩

private theorem finiteFree_zero
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (h : IsZero M) :
    ∃ (S : Type u) (_ : Fintype S), Nonempty (M ≅ SheafOfModules.free S) := by
  exact ⟨PEmpty, inferInstance, ⟨h.iso
    ((colimit.isColimit (Discrete.functor (fun _ : PEmpty ↦ SheafOfModules.unit _))).isZero_pt
      (Functor.isZero _ (fun i ↦ PEmpty.elim i.as)))⟩⟩

private theorem finiteFree_unit :
    ∃ (S : Type u) (_ : Fintype S), Nonempty
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ≅
        SheafOfModules.free S) := by
  exact ⟨PUnit, inferInstance, ⟨(coproductUniqueIso (fun _ : PUnit.{u+1} ↦
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))).symm⟩⟩

private theorem positive_tensor_terms
    (s : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) (Q : ringedSiteComplex O)
    (q : ℕ)
    (hQ : ∀ n : ℤ, n < 0 ∨ (q : ℤ) < n → IsZero (Q.X n))
    (hfQ : ∀ n : ℤ, ∃ (S : Type u) (_ : Fintype S),
      Nonempty (Q.X n ≅ SheafOfModules.free S)) :
    (∀ n : ℤ, n < 0 ∨ (q + 1 : ℕ) < n →
      IsZero ((((ringedKoszulTensor O).obj (ringedKoszulFactor O s m)).obj Q).X n)) ∧
    (∀ n : ℤ, ∃ (S : Type u) (_ : Fintype S), Nonempty
      ((((ringedKoszulTensor O).obj (ringedKoszulFactor O s m)).obj Q).X n ≅
        SheafOfModules.free S)) := by
  classical
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let := SheafOfModules.isGrothendieckAbelian
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  let := (SheafOfModules.tensorClosed O).2.1.some
  let P := ringedKoszulFactor O s m
  have hzP (i : ℤ) (hi : i ≠ 0 ∧ i ≠ 1) : IsZero (P.X i) :=
    HomologicalComplex.isZero_double_X _ _ _ hi.1 hi.2
  have hfreeP (i : ℤ) : ∃ (S : Type u) (_ : Fintype S),
      Nonempty (P.X i ≅ SheafOfModules.free S) := by
    by_cases h0 : i = 0
    · subst i
      obtain ⟨S, hS, ⟨e⟩⟩ := finiteFree_unit O
      exact ⟨S, hS, ⟨HomologicalComplex.doubleXIso₀ _ _ ≪≫ e⟩⟩
    by_cases h1 : i = 1
    · subst i
      obtain ⟨S, hS, ⟨e⟩⟩ := finiteFree_unit O
      exact ⟨S, hS, ⟨HomologicalComplex.doubleXIso₁ _ _ (by decide) ≪≫ e⟩⟩
    exact finiteFree_zero O _ (hzP i ⟨h0, h1⟩)
  have hterm (i j : ℤ) : ∃ (S : Type u) (_ : Fintype S),
      Nonempty (P.X i ⊗ Q.X j ≅ SheafOfModules.free S) := by
    obtain ⟨I, hI, ⟨eI⟩⟩ := hfreeP i
    obtain ⟨K, hK, ⟨eK⟩⟩ := hfQ j
    exact ⟨Σ _ : I, K, inferInstance,
      ⟨(eI ⊗ᵢ eK) ≪≫ SheafOfModules.freeTensorFreeIso I K⟩⟩
  constructor
  · intro n hn
    let T := { p : ℤ × ℤ // p.1 + p.2 = n }
    let X : T → A := fun p ↦ P.X p.val.1 ⊗ Q.X p.val.2
    change IsZero (∐ X)
    apply (colimit.isColimit (Discrete.functor X)).isZero_pt
    apply Functor.isZero
    intro i
    change IsZero (P.X i.as.val.1 ⊗ Q.X i.as.val.2)
    by_cases hi : i.as.val.1 = 0 ∨ i.as.val.1 = 1
    · exact (MonoidalCategory.tensorLeft _).map_isZero (hQ _ (by
        have ht := i.as.property
        rcases hi with hi | hi <;> rcases hn with hn | hn <;> omega))
    · exact (MonoidalCategory.tensorRight _).map_isZero (hzP _ (not_or.mp hi))
  · intro n
    let T := { p : ℤ × ℤ // p.1 + p.2 = n }
    let X : T → A := fun p ↦ P.X p.val.1 ⊗ Q.X p.val.2
    let S := {p : T // p.val.1 = 0 ∨ p.val.1 = 1}
    let : Fintype {z : ℤ // z = 0 ∨ z = 1} :=
      Fintype.ofFinset {0, 1} (by
        intro x
        change x ∈ ({0, 1} : Finset ℤ) ↔ x = 0 ∨ x = 1
        simp)
    have : Finite S := Finite.of_injective
      (fun i : S ↦ (⟨i.val.val.1, i.property⟩ : {z : ℤ // z = 0 ∨ z = 1})) (by
        intro i j hij
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · exact congrArg Subtype.val hij
        · have hi := i.val.property
          have hj := j.val.property
          have he := congrArg Subtype.val hij
          dsimp at he
          omega)
    let _ := Fintype.ofFinite S
    change ∃ (I : Type u) (_ : Fintype I), Nonempty ((∐ X) ≅ SheafOfModules.free I)
    obtain ⟨I, hI, ⟨e⟩⟩ := finiteFree_coproduct O (fun p : S ↦ X p)
      (fun p ↦ hterm _ _)
    exact ⟨I, hI, ⟨coproductSupportIso X (fun p ↦ p.val.1 = 0 ∨ p.val.1 = 1)
      (fun p hp ↦ (MonoidalCategory.tensorRight _).map_isZero
        (hzP _ (not_or.mp hp))) ≪≫ e⟩⟩

private theorem positive_terms : ∀ (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ),
    (∀ n : ℤ, n < 0 ∨ (r : ℤ) < n → IsZero (((ringedKoszulDiagram O r b).obj m).X n)) ∧
    (∀ n : ℤ, ∃ (S : Type u) (_ : Fintype S), Nonempty
      (((ringedKoszulDiagram O r b).obj m).X n ≅ SheafOfModules.free S)) := by
  intro r
  induction r with
  | zero =>
    intro b m
    constructor
    · intro n hn
      exact HomologicalComplex.isZero_single_obj_X _ _ _ n (by omega)
    · intro n
      by_cases hn : n = 0
      · subst n
        obtain ⟨S, hS, ⟨e⟩⟩ := finiteFree_unit O
        exact ⟨S, hS, ⟨HomologicalComplex.singleObjXSelf _ _ _ ≪≫ e⟩⟩
      · exact finiteFree_zero O _ (HomologicalComplex.isZero_single_obj_X _ _ _ n hn)
  | succ r ih =>
    intro b m
    obtain ⟨hb, hf⟩ := ih (fun i ↦ b i.succ) m
    exact positive_tensor_terms O (b 0) m _ r hb hf

/-- The actual Hom dual has no positive terms and has flat terms in every degree.
Source: Stacks Project, More on Algebra, Tag 0913; Cohomology on Sites, Tag 06YQ.
(blueprint: lem-weil-pbc-ringed-koszul-dual-flat-terms).

Proof: the positive ordered tensor has finite free terms indexed by subsets I, in
degree |I|. Hom into O[0] has degree n equal to Hom(P^(-n),O): all the other factors
in the Hom product are zero. It therefore vanishes unless -r ≤ n ≤ 0. Its surviving
terms are finite free, dual to those same subset bases. Tensoring a finite free sheaf
is a finite direct-sum functor, which preserves finite limits and colimits in the
abelian category of module sheaves. The zero terms are flat by the same argument
with an empty sum. For r=0 the surviving term is O in degree zero. -/
theorem ringedKoszulDual_flat_terms (m : ℕ) :
    (∀ n : ℤ, 0 < n → IsZero (((ringedKoszulDualTower O r b).obj (op m)).X n)) ∧
      ∀ n : ℤ, SheafOfModules.IsFlat
        (((ringedKoszulDualTower O r b).obj (op m)).X n) := by
  classical
  let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  let R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj O
  let := SheafOfModules.isGrothendieckAbelian R
  let := SheafOfModules.monoidalCategory O
  let := SheafOfModules.symmetricCategory O
  let := (SheafOfModules.tensorClosed O).1.some
  let := (SheafOfModules.tensorClosed O).2.1.some
  let P := (ringedKoszulDiagram O r b).obj m
  obtain ⟨hb, hf⟩ := positive_terms O r b m
  obtain ⟨e⟩ := homComplex_to_single_iso (R := O) P (SheafOfModules.unit R)
  have ex (n : ℤ) : ((ringedKoszulDualTower O r b).obj (op m)).X n ≅
      SheafOfModules.homObj (R := O) (P.X (-n)) (SheafOfModules.unit R) :=
    (HomologicalComplex.eval A (ComplexShape.up ℤ) n).mapIso e
  constructor
  · intro n hn
    exact (((SheafOfModules.homFunctor O).flip.obj (SheafOfModules.unit R)).map_isZero
      (hb (-n) (Or.inl (by omega))).op).of_iso (ex n)
  · intro n
    obtain ⟨S, hS, ⟨eS⟩⟩ := hf (-n)
    let e' := ex n ≪≫
      ((SheafOfModules.homFunctor O).flip.obj (SheafOfModules.unit R)).mapIso eS.symm.op ≪≫
        SheafOfModules.homObjFreeUnitIso (R := O) S
    have hfree : ObjectProperty.flat (SheafOfModules.free (R := R) S) :=
      ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _)
    exact (ObjectProperty.flat_of_retract ⟨e'.hom, e'.inv, e'.hom_inv_id⟩ hfree).2

end CategoryTheory
