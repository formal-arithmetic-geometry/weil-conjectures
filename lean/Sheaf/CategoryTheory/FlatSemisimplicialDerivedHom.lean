module

public import Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory
import Sheaf.CategoryTheory.SemisimplicialEvaluationFreeAdjoint
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Morphisms of flat semisimplicial cartesian derived objects

Source: Stacks Project, spaces-simplicial.tex, Tags 0D9R and 0D9S,
with the injective-order-map adaptation supplied by the DAG
(blueprint: lem-sfb-flat-semisimplicial-derived-hom).

Evaluation is bijective onto the subtype of families commuting with every derived
transition. A morphism is zero whenever its degree-zero evaluation is zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Bicategory

namespace CategoryTheory.SemisimplicialRingedTotal

/-- Evaluation identifies morphisms of cartesian derived objects with compatible
component families under all-negative component Hom vanishing. In particular,
degree-zero evaluation detects a zero morphism.

Source: Stacks Project, spaces-simplicial.tex, Tags 0D9R
(lemma-nullity-cartesian-modules-derived) and 0D9S
(lemma-hom-cartesian-modules-derived), injective-order-map adaptation
(blueprint: lem-sfb-flat-semisimplicial-derived-hom).

Proof: (1) Use lem-sfb-semisimplicial-cartesian-simplex-filtration for B. Write
X_p for the free extension of B_p and F_N for the finite stages. By
lem-sfb-semisimplicial-evaluation-free-adjoint, Hom(X_p[r], C) identifies with
Hom(B_p, C_p[-r]), which vanishes for every positive r. The map X_0 to B is the counit.
(2) Given a compatible family v, take the adjunct a_0 of v_0. Its composites
with the two labelled face maps X_1 to X_0 have the same adjunct v_1. Their difference
is zero. Clause (i) of lem-weil-pbc-hom-out-of-triangle-exact extends a_0 to F_1.
(3) For N positive the rotated filtration triangle starts with X_{N+1}[N],
whose Hom into C vanishes by (1). The same exactness extends a_N to a_{N+1}.
Choose these extensions recursively, compatibly with all the stage maps.
(4) On the coproduct S of the F_N the maps a_N assemble to a map annihilating
1-s. Triangle exactness on the telescope gives a global morphism gamma from B
to C; its degree-zero evaluation is v_0 by the counit identification.
(5) Naturality of the derived transitions makes the evaluations of gamma a
compatible family. An injection [0] into [n] and cancellation of B's cartesian
transition show that its degree-n evaluation is v_n. This proves surjectivity.
(6) The shifted filtration triangles and (1) give Hom(F_N[1], C) = 0 by induction,
using clause (i) of triangle exactness to factor a map through the outer term.
(7) If w has zero degree-zero evaluation, its composite with X_0 to B is zero.
Inductively its composite with F_{N+1} to B factors through X_{N+1}[N+1],
so vanishes by (1). Thus w vanishes on S. Clause (ii) of triangle exactness
factors w through the telescope boundary B to S[1]. The shifted coprojections
exhibit S[1] as the coproduct of F_N[1], so (6) kills this factor. Hence w = 0.
Applying this to a difference proves injectivity and the final assertion. -/
theorem flat_semisimplicial_derived_hom
    {F : LocallyDiscrete (SemiSimplexCategoryᵒᵖ)ᵒᵖ ⥤ᵖ Cat.{u, u}}
    {D : CoherentSitePseudofunctor SemiSimplexCategoryᵒᵖ F}
    {R : RingDiagram D} {h : Presheaf.IsSheaf D.totalTopology R.presheaf}
    (P : Presentation R h)
    (exact : ∀ {i j : SemiSimplexCategoryᵒᵖ} (a : i ⟶ j),
      PreservesFiniteLimits (P.pullback a).ordinary ∧
        PreservesFiniteColimits (P.pullback a).ordinary)
    (B C : (R.total h).D) (hB : P.IsCartesian B) (hC : P.IsCartesian C)
    (negative : ∀ (i : SemiSimplexCategoryᵒᵖ) (t : ℤ), t < 0 →
      Subsingleton ((P.evaluation i).derived.obj B ⟶
        ((P.evaluation i).derived.obj C)⟦t⟧)) :
    Function.Bijective (fun w : B ⟶ C ↦
      (⟨fun i ↦ (P.evaluation i).derived.map w,
        fun {_ _} a ↦ (P.derivedTransition a).naturality w⟩ :
        {v : ∀ i : SemiSimplexCategoryᵒᵖ,
          (P.evaluation i).derived.obj B ⟶ (P.evaluation i).derived.obj C //
          ∀ {i j : SemiSimplexCategoryᵒᵖ} (a : i ⟶ j),
            (P.pullback a).derived.map (v j) ≫ (P.derivedTransition a).app C =
              (P.derivedTransition a).app B ≫ v i})) ∧
    (∀ w : B ⟶ C,
      (P.evaluation (op (SemiSimplexCategory.mk 0))).derived.map w = 0 → w = 0) := by
  sorry

end CategoryTheory.SemisimplicialRingedTotal
