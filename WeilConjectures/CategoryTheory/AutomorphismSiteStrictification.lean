/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Data.Int.Init

/-! # Strictification of an automorphism by integer sequences

Source: `literature/stacks-project/categories.tex`, Tags 001J and 02C3, and
`literature/stacks-project/sites.tex`, Tag 03CI (blueprint:
`lem-pur-topos-automorphism-site-strictification`).
-/

open CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

@[expose] public section

universe u

namespace CategoryTheory

variable {A : Type u} [SmallCategory A]

/-- An integer-indexed family with an isomorphism from `F X_n` to `X_(n+1)`.

Source: agent integer-sequence construction refining Stacks Sites, Tag 03CI;
Categories, Tag 001J (blueprint: lem-pur-topos-automorphism-site-strictification).
-/
structure CoherentIntegerSequence (F : A ⥤ A) where
  obj : ℤ → A
  step : ∀ n : ℤ, F.obj (obj n) ≅ obj (n + 1)

namespace CoherentIntegerSequence

/-- A morphism of coherent integer sequences, commuting with every step map.

Source: agent integer-sequence construction refining Stacks Sites, Tag 03CI;
Categories, Tag 001J (blueprint: lem-pur-topos-automorphism-site-strictification).
-/
@[ext] structure Morphism {F : A ⥤ A} (X Y : CoherentIntegerSequence F) where
  app : ∀ n : ℤ, X.obj n ⟶ Y.obj n
  comm : ∀ n : ℤ,
    (X.step n).hom ≫ app (n + 1) = F.map (app n) ≫ (Y.step n).hom

/-- Componentwise identities and composition.

Source: agent integer-sequence construction refining Stacks Sites, Tag 03CI;
Categories, Tag 001J (blueprint: lem-pur-topos-automorphism-site-strictification).
-/
instance (F : A ⥤ A) : SmallCategory (CoherentIntegerSequence F) where
  Hom X Y := Morphism X Y
  id X :=
    { app := fun _ ↦ 𝟙 _
      comm := fun n ↦ by simp }
  comp {X Y Z} f g :=
    { app := fun n ↦ f.app n ≫ g.app n
      comm := fun n ↦ by
        calc
          _ = ((X.step n).hom ≫ f.app (n + 1)) ≫ g.app (n + 1) :=
            (Category.assoc _ _ _).symm
          _ = (F.map (f.app n) ≫ (Y.step n).hom) ≫ g.app (n + 1) :=
            congrArg (fun t ↦ t ≫ g.app (n + 1)) (f.comm n)
          _ = F.map (f.app n) ≫ ((Y.step n).hom ≫ g.app (n + 1)) :=
            Category.assoc _ _ _
          _ = F.map (f.app n) ≫ (F.map (g.app n) ≫ (Z.step n).hom) :=
            congrArg (fun t ↦ F.map (f.app n) ≫ t) (g.comm n)
          _ = _ := by rw [Functor.map_comp, Category.assoc] }
  id_comp := by
    intro X Y f
    apply CoherentIntegerSequence.Morphism.ext
    funext n
    exact Category.id_comp _
  comp_id := by
    intro X Y f
    apply CoherentIntegerSequence.Morphism.ext
    funext n
    exact Category.comp_id _
  assoc := by
    intro W X Y Z f g h
    apply CoherentIntegerSequence.Morphism.ext
    funext n
    exact Category.assoc _ _ _

end CoherentIntegerSequence

/-- The category `𝒟_F` of coherent integer sequences for an endofunctor `F`.

Source: agent integer-sequence construction refining Stacks Sites, Tag 03CI;
Categories, Tag 001J (blueprint: lem-pur-topos-automorphism-site-strictification).
-/
abbrev coherentSequenceCategory (F : A ⥤ A) := CoherentIntegerSequence F

/-- Evaluation at the zeroth term.

Source: agent integer-sequence construction refining Stacks Sites, Tag 03CI;
Categories, Tag 001J (blueprint: lem-pur-topos-automorphism-site-strictification).
-/
def coherentSequenceEvaluation (F : A ⥤ A) :
    coherentSequenceCategory F ⥤ A where
  obj X := X.obj 0
  map f := (f : CoherentIntegerSequence.Morphism _ _).app 0
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    rfl

/-- Translation of a coherent sequence by one integer.

Source: agent integer-sequence construction refining Stacks Sites, Tag 03CI;
Categories, Tag 001J (blueprint: lem-pur-topos-automorphism-site-strictification).
-/
def coherentSequenceTranslation (F : A ⥤ A) :
    coherentSequenceCategory F ⥤ coherentSequenceCategory F where
  obj X :=
    { obj := fun n ↦ X.obj (n + 1)
      step := fun n ↦ X.step (n + 1) }
  map f :=
    { app := fun n ↦ (f : CoherentIntegerSequence.Morphism _ _).app (n + 1)
      comm := fun n ↦ (f : CoherentIntegerSequence.Morphism _ _).comm (n + 1) }
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    rfl


/-- The transition map of the inverse translation, with its integer reindexing cast.

Source: agent integer-sequence construction refining Stacks Sites, Tag 03CI;
Categories, Tag 001J (blueprint: lem-pur-topos-automorphism-site-strictification).
-/
def coherentSequenceInverseStep {F : A ⥤ A}
    (X : CoherentIntegerSequence F) (n : ℤ) :
    F.obj (X.obj (n - 1)) ≅ X.obj (n + 1 - 1) :=
  X.step (n - 1) ≪≫
    eqToIso (congrArg X.obj (show (n - 1) + 1 = n + 1 - 1 by omega))

/-- Compatibility for the inverse translation after reindexing.

Proof: apply the defining compatibility equation at `n - 1`. Postcompose
with the equality transport from `(n - 1) + 1` to `(n + 1) - 1`;
dependent naturality of the family `f.app` identifies the left side.
Both index expressions equal `n`, so this is precisely the required square.
This is the compatibility assertion in step 4 of the node's proof.

Source: agent integer-sequence construction refining Stacks Sites, Tag 03CI;
Categories, Tag 001J (blueprint: lem-pur-topos-automorphism-site-strictification).
-/
theorem coherentSequenceTranslationInverse_comm
    {F : A ⥤ A} {X Y : CoherentIntegerSequence F}
    (f : CoherentIntegerSequence.Morphism X Y) (n : ℤ) :
    (coherentSequenceInverseStep X n).hom ≫ f.app (n + 1 - 1) =
      F.map (f.app (n - 1)) ≫ (coherentSequenceInverseStep Y n).hom := by
  let p : (n - 1) + 1 = n + 1 - 1 := by omega
  have h := eqToHom_naturality (fun i ↦ f.app i) p
  dsimp only [coherentSequenceInverseStep, Iso.trans_hom, eqToIso.hom]
  calc
    ((X.step (n - 1)).hom ≫ eqToHom (congrArg X.obj p)) ≫ f.app (n + 1 - 1) =
        (X.step (n - 1)).hom ≫ (eqToHom (congrArg X.obj p) ≫ f.app (n + 1 - 1)) :=
      Category.assoc _ _ _
    _ = (X.step (n - 1)).hom ≫ (f.app ((n - 1) + 1) ≫ eqToHom (congrArg Y.obj p)) :=
      congrArg (fun t ↦ (X.step (n - 1)).hom ≫ t) h.symm
    _ = ((X.step (n - 1)).hom ≫ f.app ((n - 1) + 1)) ≫ eqToHom (congrArg Y.obj p) :=
      (Category.assoc _ _ _).symm
    _ = (F.map (f.app (n - 1)) ≫ (Y.step (n - 1)).hom) ≫ eqToHom (congrArg Y.obj p) :=
      congrArg (fun t ↦ t ≫ eqToHom (congrArg Y.obj p)) (f.comm (n - 1))
    _ = F.map (f.app (n - 1)) ≫ ((Y.step (n - 1)).hom ≫ eqToHom (congrArg Y.obj p)) :=
      Category.assoc _ _ _

/-- Translation of a coherent sequence by minus one integer.

Source: agent integer-sequence construction refining Stacks Sites, Tag 03CI;
Categories, Tag 001J (blueprint: lem-pur-topos-automorphism-site-strictification).
-/
def coherentSequenceTranslationInverse (F : A ⥤ A) :
    coherentSequenceCategory F ⥤ coherentSequenceCategory F where
  obj X :=
    { obj := fun n ↦ X.obj (n - 1)
      step := fun n ↦ coherentSequenceInverseStep X n }
  map f :=
    { app := fun n ↦ (f : CoherentIntegerSequence.Morphism _ _).app (n - 1)
      comm := fun n ↦ coherentSequenceTranslationInverse_comm
        (f : CoherentIntegerSequence.Morphism _ _) n }
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    apply CoherentIntegerSequence.Morphism.ext
    funext n
    rfl

/-- The step at zero intertwines evaluation with the original endofunctor.

Source: agent integer-sequence construction refining Stacks Sites, Tag 03CI;
Categories, Tag 001J (blueprint: lem-pur-topos-automorphism-site-strictification).
-/
def coherentSequenceEvaluationIso (F : A ⥤ A) :
    coherentSequenceEvaluation F ⋙ F ≅
      coherentSequenceTranslation F ⋙ coherentSequenceEvaluation F :=
  NatIso.ofComponents (fun X ↦ X.step 0) (fun f ↦ by
    exact (f : CoherentIntegerSequence.Morphism _ _).comm 0 |>.symm)

end CategoryTheory

namespace CategoryTheory

variable {A : Type u} [SmallCategory A]

/-- Coherent integer sequences strictify an autoequivalence and inherit finite limits.

Source: Stacks Categories, Tags 001J and 02C3, and Sites, Tag 03CI; the
integer-sequence construction is the agent argument attached to those sources
(blueprint: lem-pur-topos-automorphism-site-strictification).

Proof:
1. Evaluation is faithful: a compatible family is determined by its zeroth map,
   by induction upwards (the source steps are isomorphisms) and downwards
   (`e.functor` is faithful and the target steps are isomorphisms).
2. Evaluation is full: from a zeroth map, recurse upwards by conjugating
   `F(g)` with the steps and downwards by the preimage under the fully faithful
   `e.functor`; the recursion equations give the compatibility squares.
3. Above an object `B`, use iterates of `e.functor` at nonnegative indices and
   of `e.inverse` at negative indices, with identity steps upwards and the counit
   of `e` downwards; evaluation is essentially surjective, hence an equivalence
   (`lem-trf-fully-faithful-ess-surj-equivalence`).
4. Both translation composites are reindexing by a function equal to the
   identity, hence equal to the identity functor; the zero step is the
   intertwiner `coherentSequenceEvaluationIso`.
5. Given finite limits in `A`, transfer them across the evaluation equivalence;
   evaluation and both translations are equivalences and so preserve them
   (`lem-galois-equivalence-preserves-limits`).
6. The object and morphism structures use only integer-indexed products and
   subtypes in universe `u`, so both collections remain `u`-small
   (`def-weil-size-convention`).
-/
theorem coherentSequenceStrictification
    (e : A ≌ A) :
    (coherentSequenceEvaluation e.functor).IsEquivalence ∧
      coherentSequenceTranslation e.functor ⋙
        coherentSequenceTranslationInverse e.functor = 𝟭 (coherentSequenceCategory e.functor) ∧
      coherentSequenceTranslationInverse e.functor ⋙
        coherentSequenceTranslation e.functor = 𝟭 (coherentSequenceCategory e.functor) ∧
      (∃ a : coherentSequenceEvaluation e.functor ⋙ e.functor ≅
          coherentSequenceTranslation e.functor ⋙ coherentSequenceEvaluation e.functor,
        ∀ X : coherentSequenceCategory e.functor, a.app X = X.step 0) ∧
      (HasFiniteLimits A →
        HasFiniteLimits (coherentSequenceCategory e.functor) ∧
          PreservesFiniteLimits (coherentSequenceEvaluation e.functor) ∧
          PreservesFiniteLimits (coherentSequenceTranslation e.functor) ∧
          PreservesFiniteLimits (coherentSequenceTranslationInverse e.functor)) := by
  classical
  let F := e.functor
  let E := coherentSequenceEvaluation F
  have faithful : E.Faithful := by
    constructor
    intro X Y f g h
    apply CoherentIntegerSequence.Morphism.ext
    funext n
    change f.app 0 = g.app 0 at h
    induction n using Int.induction_on with
    | zero => exact h
    | succ n ih =>
      apply (cancel_epi (X.step (n : ℤ)).hom).mp
      rw [f.comm, g.comm, ih]
    | pred n ih =>
      apply F.map_injective
      apply (cancel_mono (Y.step (-(n : ℤ) - 1)).hom).mp
      rw [← f.comm, ← g.comm]
      have hi : -(n : ℤ) - 1 + 1 = -(n : ℤ) := by omega
      let P (k : ℤ) := f.app k = g.app k
      have hk : P (-(n : ℤ) - 1 + 1) := (congrArg P hi).mpr ih
      exact congrArg (fun t ↦ (X.step (-(n : ℤ) - 1)).hom ≫ t) hk
  have full : E.Full := by
    constructor
    intro X Y f
    let next (n : ℤ) (g : X.obj n ⟶ Y.obj n) :
        X.obj (n + 1) ⟶ Y.obj (n + 1) :=
      (X.step n).inv ≫ F.map g ≫ (Y.step n).hom
    let prev (n : ℤ) (g : X.obj n ⟶ Y.obj n) :
        X.obj (n - 1) ⟶ Y.obj (n - 1) :=
      F.preimage ((X.step (n - 1)).hom ≫
        eqToHom (congrArg X.obj (by omega : n - 1 + 1 = n)) ≫ g ≫
        eqToHom (congrArg Y.obj (by omega : n = n - 1 + 1)) ≫
        (Y.step (n - 1)).inv)
    let app (n : ℤ) : X.obj n ⟶ Y.obj n :=
      Int.inductionOn' n 0 f (fun k _ g ↦ next k g) (fun k _ g ↦ prev k g)
    have hz : app 0 = f := Int.inductionOn'_self
    have hs (n : ℤ) (hn : 0 ≤ n) : app (n + 1) = next n (app n) :=
      Int.inductionOn'_add_one hn
    have hp (n : ℤ) (hn : n ≤ 0) : app (n - 1) = prev n (app n) :=
      Int.inductionOn'_sub_one hn
    let P (n : ℤ) :=
      (X.step n).hom ≫ app (n + 1) = F.map (app n) ≫ (Y.step n).hom
    have down (k : ℤ) (hk : k ≤ 0) : P (k - 1) := by
      let hi : k - 1 + 1 = k := by omega
      have h : app (k - 1 + 1) =
          eqToHom (congrArg X.obj hi) ≫ app k ≫ eqToHom (congrArg Y.obj hi.symm) := by
        rw [← Category.assoc, ← eqToHom_naturality (fun i ↦ app i) hi, Category.assoc]
        simp
      dsimp only [P]
      rw [hp k hk]
      simp [prev, Category.assoc]
    refine ⟨{ app := app, comm := ?_ }, hz⟩
    intro n
    by_cases hn : 0 ≤ n
    · rw [hs n hn]
      simp [next]
    · exact (congrArg P (show n + 1 - 1 = n by omega)).mp
        (down (n + 1) (by omega))
  have essSurj : E.EssSurj := by
    constructor
    intro B
    let obj (n : ℤ) : A :=
      Int.inductionOn' n 0 B (fun _ _ C ↦ F.obj C) (fun _ _ C ↦ e.inverse.obj C)
    have hz : obj 0 = B := Int.inductionOn'_self
    have hs (n : ℤ) (hn : 0 ≤ n) : obj (n + 1) = F.obj (obj n) :=
      Int.inductionOn'_add_one hn
    have hp (n : ℤ) (hn : n ≤ 0) : obj (n - 1) = e.inverse.obj (obj n) :=
      Int.inductionOn'_sub_one hn
    let step (n : ℤ) : F.obj (obj n) ≅ obj (n + 1) := by
      by_cases hn : 0 ≤ n
      · exact eqToIso (hs n hn).symm
      · have hh := hp (n + 1) (by omega)
        simp only [Int.add_sub_cancel] at hh
        exact F.mapIso (eqToIso hh) ≪≫ e.counitIso.app (obj (n + 1))
    exact ⟨⟨obj, step⟩, ⟨eqToIso hz⟩⟩
  have equiv : E.IsEquivalence := { }
  let R (i : ℤ → ℤ) (hi : ∀ n, i n + 1 = i (n + 1)) :
      coherentSequenceCategory F ⥤ coherentSequenceCategory F :=
    { obj X :=
        { obj := fun n ↦ X.obj (i n)
          step := fun n ↦ X.step (i n) ≪≫ eqToIso (congrArg X.obj (hi n)) }
      map f :=
        { app := fun n ↦ f.app (i n)
          comm := fun n ↦ by
            dsimp
            rw [Category.assoc, ← eqToHom_naturality (fun k ↦ f.app k) (hi n)]
            rw [← Category.assoc, f.comm, Category.assoc] }
      map_id _ := rfl
      map_comp _ _ := rfl }
  have hr (i : ℤ → ℤ) (hi : ∀ n, i n + 1 = i (n + 1)) (h : i = id) :
      R i hi = 𝟭 (coherentSequenceCategory F) := by
    subst i
    have ev {X Y : coherentSequenceCategory F} (h : X = Y) (n : ℤ) :
        (eqToHom h : X ⟶ Y).app n =
          eqToHom (congrArg (fun Z ↦ Z.obj n) h) := by
      subst h
      rfl
    have hobj (X : coherentSequenceCategory F) : (R id hi).obj X = X := by simp [R]
    refine CategoryTheory.Functor.ext hobj ?_
    intro X Y f
    apply CoherentIntegerSequence.Morphism.ext
    funext n
    change f.app n = (eqToHom (hobj X)).app n ≫ f.app n ≫
      (eqToHom (hobj Y).symm).app n
    rw [ev, ev]
    simp
  have h₁ : coherentSequenceTranslation F ⋙ coherentSequenceTranslationInverse F =
      𝟭 (coherentSequenceCategory F) := by
    change R (fun n ↦ n - 1 + 1) (fun n ↦ by omega) = _
    exact hr _ (fun n ↦ by omega) (by funext n; dsimp; omega)
  have h₂ : coherentSequenceTranslationInverse F ⋙ coherentSequenceTranslation F =
      𝟭 (coherentSequenceCategory F) := by
    change R (fun n ↦ n + 1 - 1) (fun n ↦ by omega) = _
    exact hr _ (fun n ↦ by omega) (by funext n; dsimp; omega)
  have : (coherentSequenceTranslation F).IsEquivalence :=
    Functor.IsEquivalence.mk' (coherentSequenceTranslationInverse F)
      (eqToIso h₁).symm (eqToIso h₂)
  have : (coherentSequenceTranslationInverse F).IsEquivalence :=
    Functor.IsEquivalence.mk' (coherentSequenceTranslation F)
      (eqToIso h₂).symm (eqToIso h₁)
  refine ⟨equiv, h₁, h₂, ⟨coherentSequenceEvaluationIso F, fun _ ↦ rfl⟩, ?_⟩
  intro h
  have : HasFiniteLimits (coherentSequenceCategory F) :=
    ⟨fun J _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence E⟩
  exact ⟨this, inferInstance, inferInstance, inferInstance⟩

end CategoryTheory
