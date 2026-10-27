/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F6
-/
module

public import Sheaf.Paper.LocalFrobeniusLargeCoefficients
import Sheaf.Paper.LocalFrobeniusLargeCompositionCoherence

/-! # Addition of positive Weil iterates

Source: Bhatt--Scholze, Remark 6.8.15; the composition calculation in the
constant-extension clause of the local Frobenius comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option allowUnsafeReducibility true in
attribute [local irreducible] WeilConjectures.commonStageDerivedPullback
  WeilConjectures.LocalFrobeniusLarge.composition
  WeilConjectures.LocalFrobeniusLarge.weilIterate
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.LocalFrobeniusLarge

private theorem positivePower_add {X : Scheme.{u}} (g : X ⟶ X) (a b : ℕ) :
    localPositivePower g a ≫ localPositivePower g b =
      localPositivePower g (a + b + 1) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [show a + (b + 1) + 1 = (a + b + 1) + 1 by omega]
    change localPositivePower g a ≫ (localPositivePower g b ≫ g) =
      localPositivePower g (a + b + 1) ≫ g
    rw [← Category.assoc, ih]

private theorem post_heq {C : Type*} [Category* C] {A A' B T : C}
    (e : A = A') {f : A ⟶ B} {g : A' ⟶ B}
    (h : HEq f g) (t : B ⟶ T) : HEq (f ≫ t) (g ≫ t) := by
  cases e
  cases h
  rfl

private theorem dependent_apply_heq {A : Sort*} {B : A → Sort*} {T : A → Sort*}
    (F : (a : A) → B a → T a) {a b : A} (e : a = b)
    {x : B a} {y : B b} (h : HEq x y) : HEq (F a x) (F b y) := by
  cases e
  cases h
  rfl

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]

/-- Two consecutive positive Weil iterates compose to their sum, using the prescribed
pullback compositor. Heterogeneous equality retains the equality of scheme powers
without selecting a second endpoint comparison.

Source: BS Remark 6.8.15; blueprint real-mixed-by-curves, paragraph 1,
constant-extension calculation, as expanded in the proof of sfWeil_blocks
(blueprint: lem-zl-large-weil-iterate-addition).

Proof: induct on b. For b = 0 the assertion is exactly the successor recursion
for weilIterate, since its positive index a denotes a+1 factors. For b+1, expand
its final one-step Weil map. Naturality of the pullback compositor moves that
map past the earlier compositor. The associativity law identifies the two
parenthesizations of the three pullbacks, and the induction hypothesis combines
the preceding a+1 and b+1 factors. The resulting word is the successor formula
for a+b+3 factors. The common-stage compositor has this naturality and associativity:
on each finite coefficient stage it is the rationalized integral compositor;
integralPullbackComposition supplies its associativity, and localization preserves
it. The prescribed scalar comparisons and pullbackStage cancel in both words,
so the same equality holds for arbitrary common-stage objects. The equality of
scheme powers follows by induction and associativity of scheme composition.
No preservation of an integral lattice by the Weil isomorphism is used. -/
theorem weilIterate_add (K : sfCommonStageWeilComplex D l hl Y₀ Ω) (a b : ℕ) :
    letI := sfWeilPrimeInvertible D l hl Y₀
    HEq
      ((composition l Ω
          (localPositivePower (D.geometricFrobenius Y₀).hom a)
          (localPositivePower (D.geometricFrobenius Y₀).hom b) K.carrier).hom ≫
        (@commonStageDerivedPullback l _ Ω _ _ _ _ _
          (localPositivePower (D.geometricFrobenius Y₀).hom a)
          (sfWeilPrimeInvertible D l hl Y₀) (sfWeilPrimeInvertible D l hl Y₀)).map
            (weilIterate D l hl Ω Y₀ K b).hom ≫
        (weilIterate D l hl Ω Y₀ K a).hom)
      (weilIterate D l hl Ω Y₀ K (a + b + 1)).hom := by
  let := sfWeilPrimeInvertible D l hl Y₀
  let g := (D.geometricFrobenius Y₀).hom
  let P := fun f : (D.geometricFiber Y₀).left ⟶ (D.geometricFiber Y₀).left ↦
    commonStageDerivedPullback l Ω f
  let θ := fun n ↦ (weilIterate D l hl Ω Y₀ K n).hom
  have step (n : ℕ) : θ (n + 1) =
      (composition l Ω (localPositivePower g n) g K.carrier).hom ≫
        (P (localPositivePower g n)).map K.str.hom ≫ θ n := by
    dsimp only [θ]
    rw [weilIterate]
    rfl
  have zero : θ 0 = K.str.hom := by
    simp only [θ, weilIterate]
  change HEq ((composition l Ω _ _ K.carrier).hom ≫ (P _).map (θ b) ≫ θ a)
    (θ (a + b + 1))
  induction b with
  | zero =>
    simpa only [Nat.add_zero, localPositivePower, zero] using heq_of_eq (step a).symm
  | succ b ih =>
    have hpow := positivePower_add g a b
    have hc := composition_map_assoc l Ω (D.geometricFiber Y₀).left
      (localPositivePower g a) (localPositivePower g b) g K.carrier K.carrier K.str.hom
    have hc' := post_heq
      (congrArg (fun f ↦ (P f).obj K.carrier)
        (Category.assoc (localPositivePower g a) (localPositivePower g b) g).symm)
      hc ((P (localPositivePower g a)).map (θ b) ≫ θ a)
    simp only [Category.assoc] at hc'
    have hi := dependent_apply_heq
      (fun (f : (D.geometricFiber Y₀).left ⟶ (D.geometricFiber Y₀).left)
        (t : (P f).obj K.carrier ⟶ K.carrier) ↦
          (composition l Ω f g K.carrier).hom ≫ (P f).map K.str.hom ≫ t)
      hpow ih
    have hh := hc'.trans hi
    have hs := heq_of_eq (step (a + b + 1)).symm
    have ht := hh.trans hs
    simpa only [step, Functor.map_comp, Category.assoc, Nat.add_succ,
      localPositivePower] using ht

end WeilConjectures.LocalFrobeniusLarge
