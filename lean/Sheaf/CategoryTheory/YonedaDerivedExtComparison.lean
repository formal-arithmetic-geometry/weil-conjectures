/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.CategoryTheory.YonedaExtensionData
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Sheaf.CategoryTheory.YonedaExtensionClass
import Sheaf.CategoryTheory.YonedaClassNaturality
import Sheaf.CategoryTheory.YonedaClassClassification
import Sheaf.CategoryTheory.YonedaClassSplice
import Sheaf.CategoryTheory.YonedaBaerExistence
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-! # Yoneda extensions and derived Ext

Source: Stacks Project, Derived Categories, Tags 06XU and 06XV, and Homology,
Section 010I (blueprint: lem-coef-yoneda-derived-ext-comparison).

The carrier is the quotient of actual finite exact sequences by endpoint-fixed
zigzags. `YonedaDerivedExtComparison` specifies the comparison, its normalization
on short exact sequences and splices, naturality, and the Baer group operation.
The splice normalization characterizes the canonical map in every positive degree;
it uses Mathlib's short-exact-sequence class with the signs of the positive-projection
roof, and composition in derived Ext.

## Main definitions

* `YonedaExtension` and `YonedaExtension.Classes`: exact sequences and their quotient.
* `YonedaExtension.BaerSum`: the specified direct-sum/pullback/pushout construction.
* `YonedaDerivedExtComparison`: the canonically normalized natural comparison.

## Main statements

* `nonempty_yonedaDerivedExtComparison`: the comparison and its stated properties exist.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open Limits Abelian

/-- The canonical natural comparison in all positive degrees, including its Baer
addition and degree-one zero criterion. Normalization on short exact sequences
and on splices fixes the comparison uniquely: every exact sequence can be cut at
the image of its first differential, and this lowers its degree by one.

Source: Stacks Project, Derived Categories, Tags 06XU and 06XV, and Homology,
Section 010I (blueprint: lem-coef-yoneda-derived-ext-comparison). -/
structure YonedaDerivedExtComparison (A : Type u) [Category.{v} A] [Abelian A]
    [HasExt.{w} A] where
  /-- The group is carried by the quotient of actual exact sequences. -/
  classGroup (V U : A) (n : ℕ) : AddCommGroup (YonedaExtension.Classes V U (n + 1))
  /-- The additive isomorphism with the recorded derived Ext. -/
  comparison (V U : A) (n : ℕ) :
    @AddEquiv (YonedaExtension.Classes V U (n + 1)) (Ext U V (n + 1))
      (classGroup V U n).toAdd inferInstance
  /-- In degree one the positive-projection roof is the negative of Mathlib's
  connecting class: its cone triangle uses the negative projection. -/
  shortExact_class (V U : A) (E : YonedaExtension A V U 1)
      (h : (E.sequence.sc E.exact.toIsComplex 0).ShortExact) :
    comparison V U 0 E.classOf =
      -(((Ext.mk₀ E.rightIso.inv).comp h.extClass (zero_add 1)).comp
        (Ext.mk₀ E.leftIso.hom) (add_zero 1))
  /-- A splice is normalized by the positive-projection roof. Shifting the short
  complex by `n + 1` contributes `(-1)^(n + 1)`, and replacing its positive
  projection by Mathlib's negative connecting class contributes one more minus. -/
  splice_class (U : A) (n : ℕ) (S : ShortComplex A) (hS : S.ShortExact)
      (F : YonedaExtension A S.X₃ U (n + 1))
      (E : YonedaExtension A S.X₁ U (n + 2)) (s : YonedaExtension.Splice S F E) :
    comparison S.X₁ U (n + 1) E.classOf =
      (-1 : ℤ) ^ n • ((comparison S.X₃ U n F.classOf).comp hS.extClass (by omega))
  /-- Naturality for any commutative map of sequences, with the induced maps on
  the two endpoints. It includes both pullback in `U` and pushout in `V`. -/
  naturality (V U V' U' : A) (n : ℕ) (E : YonedaExtension A V U (n + 1))
      (F : YonedaExtension A V' U' (n + 1)) (φ : E.sequence ⟶ F.sequence) :
    (comparison V U n E.classOf).comp (Ext.mk₀ (E.leftMap F φ)) (add_zero _) =
      (Ext.mk₀ (E.rightMap F φ)).comp (comparison V' U' n F.classOf) (zero_add _)
  /-- The geometric Baer construction is the addition on quotient classes. -/
  baer_sum (V U : A) (n : ℕ) (E F G : YonedaExtension A V U (n + 1))
      (h : YonedaExtension.BaerSum E F G) :
    G.classOf = (classGroup V U n).add E.classOf F.classOf
  /-- The Baer construction exists for every pair of extensions. -/
  baer_exists (V U : A) (n : ℕ) (E F : YonedaExtension A V U (n + 1)) :
    ∃ G : YonedaExtension A V U (n + 1), YonedaExtension.BaerSum E F G
  /-- Exactly the split short extensions have zero class. -/
  split_iff (V U : A) (E : YonedaExtension A V U 1) :
    comparison V U 0 E.classOf = 0 ↔ E.IsSplit
  /-- Injective second arguments give zero groups in every positive degree. -/
  injective_vanishing (V U : A) [Injective V] (n : ℕ) : Subsingleton (Ext U V (n + 1))

private theorem baer_class_of_naturality {A : Type u} [Category.{v} A] [Abelian A]
    [HasExt.{w} A] (n : ℕ)
    (d : ∀ V U : A, YonedaExtension A V U (n + 1) → Ext U V (n + 1))
    (hn : ∀ (V U V' U' : A) (E : YonedaExtension A V U (n + 1))
      (F : YonedaExtension A V' U' (n + 1)) (φ : E.sequence ⟶ F.sequence),
      (d V U E).comp (Ext.mk₀ (E.leftMap F φ)) (add_zero _) =
        (Ext.mk₀ (E.rightMap F φ)).comp (d V' U' F) (zero_add _))
    {V U : A} (E F G : YonedaExtension A V U (n + 1))
    (h : YonedaExtension.BaerSum E F G) :
    d V U G = d V U E + d V U F := by
  obtain ⟨T, P, p₁, p₂, b, c, hl₁, hl₂, hr₁, hr₂, _, hbl, hbr, _, _, hcl, hcr, _, _⟩ := h
  have hp₁ := hn _ _ _ _ T E p₁
  have hp₂ := hn _ _ _ _ T F p₂
  have hb := hn _ _ _ _ P T b
  have hc := hn _ _ _ _ P G c
  rw [hl₁, hr₁] at hp₁
  rw [hl₂, hr₂] at hp₂
  rw [hbl, hbr, Ext.comp_mk₀_id] at hb
  rw [hcl, hcr, Ext.mk₀_id_comp] at hc
  rw [← hc, Ext.mk₀_add, Ext.comp_add, hb]
  congr 1
  · rw [Ext.comp_assoc_of_third_deg_zero, hp₁,
      ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
    simp
  · rw [Ext.comp_assoc_of_third_deg_zero, hp₂,
      ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]
    simp

private theorem comparison_of_class_properties (A : Type u) [Category.{v} A]
    [Abelian A] [HasExt.{w} A]
    (hn : ∀ (V U V' U' : A) (n : ℕ) (E : YonedaExtension A V U (n + 1))
      (F : YonedaExtension A V' U' (n + 1)) (φ : E.sequence ⟶ F.sequence),
      (E.derivedClass n).comp (Ext.mk₀ (E.leftMap F φ)) (add_zero _) =
        (Ext.mk₀ (E.rightMap F φ)).comp (F.derivedClass n) (zero_add _))
    (hb : ∀ (V U : A) (n : ℕ),
      Function.Surjective (YonedaExtension.derivedClass (A := A) (V := V) (U := U) n) ∧
      ∀ E F : YonedaExtension A V U (n + 1),
        E.derivedClass n = F.derivedClass n → E.Equivalent F)
    (hs : ∀ (U : A) (n : ℕ) (S : ShortComplex A) (hS : S.ShortExact)
      (F : YonedaExtension A S.X₃ U (n + 1))
      (E : YonedaExtension A S.X₁ U (n + 2)), YonedaExtension.Splice S F E →
      E.derivedClass (n + 1) =
        (-1 : ℤ) ^ n • ((F.derivedClass n).comp hS.extClass (by omega)))
    (he : ∀ (V U : A) (n : ℕ) (E F : YonedaExtension A V U (n + 1)),
      ∃ G : YonedaExtension A V U (n + 1), YonedaExtension.BaerSum E F G) :
    Nonempty (YonedaDerivedExtComparison A) := by
  classical
  have hi (V U : A) (n : ℕ) (E F : YonedaExtension A V U (n + 1))
      (h : E.Equivalent F) : E.derivedClass n = F.derivedClass n := by
    induction h with
    | rel E F h =>
      obtain ⟨φ, hl, hr⟩ := h
      simpa [hl, hr] using hn V U V U n E F φ
    | refl => rfl
    | symm _ _ _ h => exact h.symm
    | trans _ _ _ _ _ h₁ h₂ => exact h₁.trans h₂
  let f (V U : A) (n : ℕ) : YonedaExtension.Classes V U (n + 1) → Ext U V (n + 1) :=
    Quot.lift (YonedaExtension.derivedClass n) (hi V U n)
  have hf (V U : A) (n : ℕ) : Function.Bijective (f V U n) := by
    constructor
    · intro x y
      refine Quot.inductionOn x ?_
      intro E
      refine Quot.inductionOn y ?_
      intro F h
      exact Quot.sound ((hb V U n).2 E F h)
    · intro x
      obtain ⟨E, hE⟩ := (hb V U n).1 x
      exact ⟨E.classOf, hE⟩
  let e (V U : A) (n : ℕ) := Equiv.ofBijective (f V U n) (hf V U n)
  refine ⟨{
    classGroup := fun V U n => (e V U n).addCommGroup
    comparison := fun V U n => (e V U n).addEquiv
    shortExact_class := ?_
    splice_class := ?_
    naturality := ?_
    baer_sum := ?_
    baer_exists := he
    split_iff := ?_
    injective_vanishing := fun V U _ n => Ext.subsingleton_of_injective U V n }⟩
  · intro V U E h
    rfl
  · intro U n S hS F E s
    exact hs U n S hS F E s
  · intro V U V' U' n E F φ
    exact hn V U V' U' n E F φ
  · intro V U n E F G h
    apply (e V U n).injective
    change G.derivedClass n =
      (e V U n) ((e V U n).symm (E.derivedClass n + F.derivedClass n))
    simpa only [Equiv.apply_symm_apply] using
      baer_class_of_naturality n (fun _ _ E => E.derivedClass n)
        (fun V U V' U' E F φ => hn V U V' U' n E F φ) E F G h
  · intro V U E
    exact E.derivedClass_zero_iff

/-- Yoneda extension classes are naturally isomorphic as abelian groups to
positive derived Ext, with the Baer addition, split-zero criterion and injective
vanishing specified in `YonedaDerivedExtComparison`.

Source: Stacks Project, Derived Categories, Tags 06XU and 06XV, and Homology,
Section 010I (blueprint: lem-coef-yoneda-derived-ext-comparison).

Proof:
1. Cut each extension at successive actual cokernels and compose its short exact
connecting classes with the positive-projection signs. Naturality of these
classes makes the result invariant under endpoint-fixed maps and their zigzags.
2. The classification theorem proves surjectivity by effacing a positive Ext
class with a monomorphism and applying the covariant Ext exact sequence. This
lowers the degree; induction and the signed splice identity construct an actual
representing extension. In degree one use the pullback of a cokernel sequence.
3. For injectivity, degree-one equality gives a short-complex map with the fixed
endpoints. In higher degrees push out the first injections to a common head.
The difference of the resulting tail classes lifts to the middle object by Ext
exactness. Efface that lift, push out the tails, and apply induction. Splicing the
tail zigzag gives equivalence of the original extensions.
4. Descend the concrete class by Quot.lift. Classification makes this map
bijective; transport the abelian group structure along Equiv.ofBijective. The
recursive definition and the signed splice identity give both normalizations.
5. Apply naturality to the two product projections, the diagonal pullback map,
and the addition pushout map of the Baer construction. Bilinearity of Ext gives
addition of classes; injectivity transfers this identity to the quotient.
Products and endpoint pullback and pushout constructions prove Baer existence.
6. The degree-one zero criterion follows from the contravariant Ext exact
sequence: vanishing lifts the first identity to a retraction, giving a splitting.
Mathlib's injective-vanishing theorem supplies the remaining field; it requires
only the given second argument to be injective, without enough injectives.
-/
theorem nonempty_yonedaDerivedExtComparison (A : Type u) [Category.{v} A]
    [Abelian A] [HasExt.{w} A] : Nonempty (YonedaDerivedExtComparison A) := by
  exact comparison_of_class_properties A YonedaExtension.derivedClass_naturality
    YonedaExtension.derivedClass_classification YonedaExtension.derivedClass_splice
    YonedaExtension.baerSum_exists

end CategoryTheory
