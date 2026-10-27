module

public import Sheaf.CategoryTheory.DgAlgebraDerivedCategory
public import Mathlib.Algebra.Module.CharacterModule

/-!
# DG embeddings with character-dual layers

Source: literature/stacks-project/dga.tex, Tag 09KT, lemma-good-sub
(blueprint: lem-sfb-dg-good-character-embedding).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DgAlgebra

/-- An admissible short exact sequence of right DG modules, split after forgetting d.
Source: Stacks Project, dga.tex, Tag 09KT, lemma-good-sub
(blueprint: lem-sfb-dg-good-character-embedding). -/
structure GradedSplitShortExact (A : Algebra.{u})
    (E' E E'' : RightModule A) where
  inclusion : E' ⟶ E
  projection : E ⟶ E''
  inclusion_injective : ∀ n : ℤ,
    Function.Injective (((underlying A).map inclusion).f n)
  projection_surjective : ∀ n : ℤ,
    Function.Surjective (((underlying A).map projection).f n)
  exact : ∀ (n : ℤ) (x : ((underlying A).obj E).X n),
    ((underlying A).map projection).f n x = 0 ↔
      ∃ y : ((underlying A).obj E').X n, ((underlying A).map inclusion).f n y = x
  sectionMap : ∀ n : ℤ, ((underlying A).obj E'').X n →+
    ((underlying A).obj E).X n
  section_right_inverse : ∀ (n : ℤ) (x : ((underlying A).obj E'').X n),
    ((underlying A).map projection).f n (sectionMap n x) = x
  section_action : ∀ (n m : ℤ) (x : ((underlying A).obj E'').X n)
    (a : A.X.X m),
    sectionMap (n + m) (act A E'' n m x a) =
      act A E n m (sectionMap n x) a

/-- A DG module whose graded pieces are products of shifted character duals.
The coordinate equations pin the character-dual differential and right action.
Source: Stacks Project, dga.tex, definition-shift and Tag 09KT, lemma-good-sub
(blueprint: lem-sfb-dg-good-character-embedding). -/
structure CharacterDualShiftProduct (A : Algebra.{u}) where
  module : RightModule A
  index : Type u
  shift : index → ℤ
  coordinate (n : ℤ) :
    ((underlying A).obj module).X n ≃+
      (∀ i : index, CharacterModule (A.X.X (-(n + shift i))))
  coordinate_differential (n : ℤ) (x : ((underlying A).obj module).X n)
      (i : index) (b : A.X.X (-(n + 1 + shift i))) :
    coordinate (n + 1) ((((underlying A).obj module).d n (n + 1)) x) i b =
      (n + 1).negOnePow • coordinate n x i
        (cast (congrArg (fun r : ℤ ↦ (A.X.X r : Type u)) (by omega))
          ((A.X.d (-(n + 1 + shift i)) (-(n + 1 + shift i) + 1)) b))
  coordinate_action (n m : ℤ) (x : ((underlying A).obj module).X n)
      (a : A.X.X m) (i : index) (b : A.X.X (-(n + m + shift i))) :
    coordinate (n + m) (act A module n m x a) i b =
      coordinate n x i
        (cast (congrArg (fun r : ℤ ↦ (A.X.X r : Type u)) (by omega))
          (act A (regular A) m (-(n + m + shift i)) a b))

/-- The additive subgroup of degree-`n` boundaries.
Source: Stacks Project, dga.tex, Tag 09KT, lemma-good-sub
(blueprint: lem-sfb-dg-good-character-embedding). -/
def differentialBoundarySubgroup (A : Algebra.{u}) (M : RightModule A) (n : ℤ) :
    AddSubgroup (((underlying A).obj M).X n) :=
  AddSubgroup.closure {x | ∃ y : ((underlying A).obj M).X (n - 1),
    x = cast (congrArg (fun r : ℤ ↦ (((underlying A).obj M).X r : Type u)) (by omega))
      (((underlying A).obj M).d (n - 1) n y)}

/-- The degree-`n` differential cokernel.
Source: Stacks Project, dga.tex, Tag 09KT, lemma-good-sub
(blueprint: lem-sfb-dg-good-character-embedding). -/
abbrev DifferentialCokernel (A : Algebra.{u}) (M : RightModule A) (n : ℤ) : Type u :=
  ((underlying A).obj M).X n ⧸ differentialBoundarySubgroup A M n

/-- The induced map on differential cokernels is injective in every degree.
Source: Stacks Project, dga.tex, Tag 09KT, lemma-good-sub
(blueprint: lem-sfb-dg-good-character-embedding). -/
def DGMapInducesCokernelInjection (A : Algebra.{u})
    {M E : RightModule A} (f : M ⟶ E) : Prop :=
  ∀ n : ℤ, ∃ φ : DifferentialCokernel A M n →+ DifferentialCokernel A E n,
    (∀ x : ((underlying A).obj M).X n,
      φ (QuotientAddGroup.mk' (differentialBoundarySubgroup A M n) x) =
        QuotientAddGroup.mk' (differentialBoundarySubgroup A E n)
          ((((underlying A).map f).f n) x)) ∧
      Function.Injective φ

/--
DG embeddings preserving differential cokernels with two dual-free layers.

Source: literature/stacks-project/dga.tex, Tag 09KT, lemma-good-sub
(blueprint: lem-sfb-dg-good-character-embedding).

The proof constructs two-layer disks from the character dual, takes one product
for all additive characters to obtain a degreewise embedding, and adds a second
product indexed by characters of each differential cokernel.  The latter detects
every nonzero cokernel class.  Coordinatewise kernels and sections give the
DG short exact sequence and its graded splitting.  It uses
`CharacterModule.exists_character_apply_ne_zero_of_ne_zero` and imposes no
boundedness or finiteness hypothesis.
-/
theorem dg_good_character_embedding (A : Algebra.{u}) :
    ∀ (M : RightModule A),
      ∃ (E E' E'' : RightModule A) (u : M ⟶ E),
        Nonempty (GradedSplitShortExact A E' E E'') ∧
          (∀ n : ℤ, Function.Injective (((underlying A).map u).f n)) ∧
          DGMapInducesCokernelInjection A u ∧
          (∃ P' P'' : CharacterDualShiftProduct A,
            Nonempty (E' ≅ P'.module) ∧ Nonempty (E'' ≅ P''.module)) := by
  sorry

end CategoryTheory.DgAlgebra
