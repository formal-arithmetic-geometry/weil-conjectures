/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.Helper.SequentialSemilinearDerivedDiagramsDefs

/-! Assembly of adjacent complex maps into a strict-system complex.

This helper isolates the coherence of iterated scalar restrictions from the
right-fraction argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.SequentialDerived
open Helper

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

variable (L : ∀ n : ℕ, CochainComplex (systemLevel B n) ℤ)
  (b : ∀ n : ℕ, L (n + 1) ⟶
    ((systemRestriction B (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)).obj (L n))

private def assemblyTransition : ∀ (n m : ℕ) (h : m ≤ n) (i : ℤ),
    (L n).X i ⟶ (systemRestriction B h).obj ((L m).X i)
  | 0, m, h, i => by
    have hm : m = 0 := by omega
    subst m
    exact (systemScalarRestrictionUnit (B.map (homOfLE (Nat.le_refl 0)).op)
      (B.map_id (op 0))).inv.app ((L 0).X i)
  | n + 1, m, h, i => by
    by_cases he : m = n + 1
    · subst m
      exact (systemScalarRestrictionUnit (B.map (homOfLE (Nat.le_refl (n + 1))).op)
        (B.map_id (op (n + 1)))).inv.app ((L (n + 1)).X i)
    · have hm : m ≤ n := by omega
      exact (b n).f i ≫ (systemRestriction B (Nat.le_succ n)).map
        (assemblyTransition n m hm i) ≫
        (systemScalarRestrictionComposition (B.map (homOfLE (Nat.le_succ n)).op)
          (B.map (homOfLE hm).op) (B.map (homOfLE h).op) (by
            rw [← B.map_comp]
            rfl)).hom.app ((L m).X i)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem assemblyTransition_self (n : ℕ) (i : ℤ) (U : Cᵒᵖ)
    (x : ((L n).X i).val.obj U) :
    (assemblyTransition B L b n n (Nat.le_refl n) i).val.app U x = x := by
  cases n <;> simp only [assemblyTransition]
  all_goals rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem assemblyTransition_succ {m n : ℕ} (h : m ≤ n) (i : ℤ) (U : Cᵒᵖ)
    (x : ((L (n + 1)).X i).val.obj U) :
    (assemblyTransition B L b (n + 1) m (h.trans (Nat.le_succ n)) i).val.app U x =
      (assemblyTransition B L b n m h i).val.app U ((b n).f i |>.val.app U <| x) := by
  simp only [assemblyTransition, dif_neg (show m ≠ n + 1 by omega)]
  rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem assemblyTransition_comp {l m n : ℕ} (h : l ≤ m) (k : m ≤ n)
    (i : ℤ) (U : Cᵒᵖ) (x : ((L n).X i).val.obj U) :
    (assemblyTransition B L b n l (h.trans k) i).val.app U x =
      (assemblyTransition B L b m l h i).val.app U
        ((assemblyTransition B L b n m k i).val.app U x) := by
  induction n, k using Nat.le_induction with
  | base => rw [assemblyTransition_self]
  | succ n k ih =>
    rw [assemblyTransition_succ B L b (h.trans k), assemblyTransition_succ B L b k]
    exact ih _

private def assemblyTerm (i : ℤ) : StrictRingSystem B where
  level n := (L n).X i
  transition {m n} h := assemblyTransition B L b n m h i
  identity n U x := assemblyTransition_self B L b n i U x
  compose h k U x := assemblyTransition_comp B L b h k i U x

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}] in
private theorem assemblyTransition_d {m n : ℕ} (h : m ≤ n) (i j : ℤ) :
    (L n).d i j ≫ assemblyTransition B L b n m h j =
      assemblyTransition B L b n m h i ≫ (systemRestriction B h).map ((L m).d i j) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change (assemblyTransition B L b n m h j).val.app U ((L n).d i j |>.val.app U <| x) =
    ((L m).d i j).val.app U ((assemblyTransition B L b n m h i).val.app U x)
  induction n, h using Nat.le_induction with
  | base => rw [assemblyTransition_self, assemblyTransition_self]
  | succ n h ih =>
    rw [assemblyTransition_succ B L b h, assemblyTransition_succ B L b h]
    have hb := congrArg (fun f ↦ f.val.app U x) ((b n).comm i j).symm
    change ((b n).f j).val.app U ((L (n + 1)).d i j |>.val.app U <| x) =
      ((L n).d i j).val.app U (((b n).f i).val.app U x) at hb
    rw [hb]
    exact ih _

private def assemblyDifferential (i j : ℤ) :
    assemblyTerm B L b i ⟶ assemblyTerm B L b j where
  app n := (L n).d i j
  comm h := assemblyTransition_d B L b h i j

private def assemblyComplex : CochainComplex (StrictRingSystem B) ℤ where
  X := assemblyTerm B L b
  d := assemblyDifferential B L b
  shape i j h := by
    apply strictRingSystem_hom_ext B
    intro n
    change (L n).d i j = (systemEvaluation B n).map
      (0 : assemblyTerm B L b i ⟶ assemblyTerm B L b j)
    rw [Functor.map_zero]
    exact (L n).shape i j h
  d_comp_d' i j k _ _ := by
    apply strictRingSystem_hom_ext B
    intro n
    change (systemEvaluation B n).map
      (assemblyDifferential B L b i j ≫ assemblyDifferential B L b j k) =
        (systemEvaluation B n).map 0
    rw [Functor.map_comp, Functor.map_zero]
    exact (L n).d_comp_d i j k

private def assemblyEvaluation (n : ℕ) :
    ((systemEvaluation B n).mapHomologicalComplex (.up ℤ)).obj
      (assemblyComplex B L b) ≅ L n :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (by
    intros
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl)

private theorem assemblyAdjacent (n : ℕ) :
    ((strictSystemTransition B (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)).app
        (assemblyComplex B L b) ≫
      ((systemRestriction B (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)).map
        (assemblyEvaluation B L b n).hom =
      (assemblyEvaluation B L b (n + 1)).hom ≫ b n := by
  apply HomologicalComplex.hom_ext
  intro i
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  change (assemblyTransition B L b (n + 1) n (Nat.le_succ n) i).val.app U x =
    ((b n).f i).val.app U x
  rw [assemblyTransition_succ B L b (Nat.le_refl n), assemblyTransition_self]

/-- Assemble compatible adjacent complex maps into one complex of strict systems.

Given complexes `L n` at each coefficient level and adjacent chain maps `b n`,
construct a complex `P` of strict systems, isomorphisms from its evaluations to
`L n` in the derived categories, and the localized transition equation. The proof
uses the actual composite scalar-restriction maps and verifies identity, composition,
and the chain differential equations degreewise. This is the coherence/assembly
part of the sequential realization argument.

Proof source: the coherent-tower sentence of paragraph 4 of the proof of
`lem-coef-integral-finite-extension` (steps 2-3 of
`lem-sf-sequential-semilinear-derived-realization`), with the scalar-restriction
unit and compositor of `lem-pur-system-scalar-coherence` and the cochain
representative formula `systemDerivedTransition_rep` of
`lem-pur-system-derived-transition`.
(blueprint: lem-sf-sequential-semilinear-strict-system-assembly). -/
theorem sequentialSemilinearStrictSystemAssembly
    (L : ∀ n : ℕ, CochainComplex (systemLevel B n) ℤ)
    (b : ∀ n : ℕ,
      L (n + 1) ⟶
        ((systemRestriction B (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)).obj (L n)) :
    ∃ (P : CochainComplex (StrictRingSystem B) ℤ)
      (c : ∀ n : ℕ,
        (derivedSystemEvaluation B n).obj (DerivedCategory.Q.obj P) ≅
          DerivedCategory.Q.obj (L n)),
      ∀ n : ℕ,
        (systemDerivedTransition B (Nat.le_succ n)).app (DerivedCategory.Q.obj P) ≫
            (adjacentRestriction B n).map (c n).hom ≫
            (systemRestriction B (Nat.le_succ n)).mapDerivedCategoryFactors.hom.app (L n) =
          (c (n + 1)).hom ≫ DerivedCategory.Q.map (b n) := by
  let P := assemblyComplex B L b
  let c : ∀ n : ℕ,
      (derivedSystemEvaluation B n).obj (DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj (L n) := fun n ↦
    (systemEvaluation B n).mapDerivedCategoryFactors.app P ≪≫
      DerivedCategory.Q.mapIso (assemblyEvaluation B L b n)
  refine ⟨P, c, ?_⟩
  intro n
  dsimp only [c, Iso.trans_hom, Functor.mapIso_hom]
  simp only [Iso.app_hom, Functor.map_comp, Category.assoc]
  rw [Functor.mapDerivedCategoryFactors_hom_naturality]
  calc
    _ = (systemEvaluation B (n + 1)).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map
          (((strictSystemTransition B (Nat.le_succ n)).mapHomologicalComplex
            (.up ℤ)).app P) ≫
        DerivedCategory.Q.map
          (((systemRestriction B (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)).map
            (assemblyEvaluation B L b n).hom) := by
      simpa only [Category.assoc] using congrArg
        (fun f ↦ f ≫ DerivedCategory.Q.map
          (((systemRestriction B (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)).map
            (assemblyEvaluation B L b n).hom))
        (systemDerivedTransition_rep B (Nat.le_succ n) P)
    _ = _ := by
      rw [← DerivedCategory.Q.map_comp, assemblyAdjacent]
      simp only [Functor.map_comp]

end SheafOfModules.SequentialDerived
