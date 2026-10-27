module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Descending cycles in a kernel-closed exact-image class

Source: Stacks Project, Derived Categories, dual of Tags 015D and 015E; the abstract
class-level descending-cycle argument extracted from the acyclic-computation proof
(blueprint: lem-trf-resolving-class-cycle-acyclicity).
-/

@[expose] public section

universe u₁ v₁ u₂ v₂

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

/-- Descending cycles of a bounded above acyclic complex remain in a kernel-closed class
on whose short exact sequences an additive functor is exact. Their images represent both
cycles and boundaries of the image complex, which is therefore acyclic.

Source: Stacks Project, Derived Categories, dual of Tags 015D and 015E, abstracted to the
stated class condition (blueprint: lem-trf-resolving-class-cycle-acyclicity).

Proof:
1. Vanishing homology makes each incoming cycle lift epic: use the zero cohomology
cokernel and the epimorphic-refinement criteria of lem-sp-abelian-refinements, clauses
(c) and (a). Since the next cycle inclusion is monic, the kernel of the outgoing cycle
lift is the current cycle inclusion. Thus all cycle sequences are short exact.
2. Above b the cycles are zero and belong to the class. Descending induction, starting
at b+1 and applying the class condition to the cycle sequences, shows that every cycle
belongs to the class and every image cycle sequence is short exact.
3. Write I_n and P_n for the images of the cycle inclusion and outgoing cycle lift.
The image differential is P_n followed by I_(n+1). Since I_(n+1) is monic, its kernel
is ker P_n, which exactness identifies with the image subobject of I_n.
4. The preceding differential is P_(n-1) followed by I_n. Since P_(n-1) is epic,
its image is the subobject represented by I_n. Equivalently, lift generalized elements
through P_(n-1) after an epimorphic refinement and use clause (b) of
lem-sp-abelian-refinements. Hence images equal kernels in every degree, and the image
complex is acyclic (def-weil-abstract-derived-category). -/
theorem resolving_class_cycle_acyclicity
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Abelian A] [Abelian B] (V : A ⥤ B) [V.Additive]
    (𝓔 : A → Prop)
    (hzero : ∀ X : A, IsZero X → 𝓔 X)
    (hiso : ∀ {X Y : A}, (X ≅ Y) → 𝓔 X → 𝓔 Y)
    (hclosed : ∀ S : ShortComplex A, S.ShortExact → 𝓔 S.X₂ → 𝓔 S.X₃ →
      𝓔 S.X₁ ∧ (S.map V).ShortExact)
    (E : CochainComplex A ℤ) (b : ℤ)
    (hbounded : ∀ n : ℤ, b < n → IsZero (E.X n))
    (hacyclic : ∀ n : ℤ, IsZero (E.homology n))
    (hterms : ∀ n : ℤ, 𝓔 (E.X n)) :
    (∀ n : ℤ, 𝓔 (E.cycles n)) ∧
      (∀ n : ℤ, ((E.cyclesShortComplex n (n + 1)).map V).ShortExact ∧
        imageSubobject (V.map (E.iCycles n)) =
          kernelSubobject (((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d n (n + 1)) ∧
        imageSubobject (V.map (E.iCycles n)) =
          imageSubobject (((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj E).d (n - 1) n)) ∧
      ((V.mapHomologicalComplex (ComplexShape.up ℤ)).obj E).Acyclic := by
  sorry

end HomologicalComplex
