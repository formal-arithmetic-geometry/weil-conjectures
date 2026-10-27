/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q25
-/
module

public import Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory
public import Sheaf.CategoryTheory.SemisimplicialEvaluationFreeAdjoint
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit

/-! # Simplex filtration of a cartesian semisimplicial derived object

Source: Stacks Project, spaces-simplicial.tex, Tags 0D9B, 0D9E and 0D9Q,
with the injective-order-map adaptation recorded in the DAG
(blueprint: lem-sfb-semisimplicial-cartesian-simplex-filtration).

The free terms and first boundary are defined from the recorded adjunction and
labelled inclusions. The statement supplies actual distinguished triangles,
the telescope maps, and both coproduct universal properties in the unbounded
category. The equality at stage zero is transported explicitly in its two uses.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Bicategory
open CategoryTheory.Pretriangulated

namespace CategoryTheory.SemisimplicialRingedTotal

variable {F : LocallyDiscrete (SemiSimplexCategoryᵒᵖ)ᵒᵖ ⥤ᵖ Cat.{u, u}}
  {D : CoherentSitePseudofunctor SemiSimplexCategoryᵒᵖ F}
  {R : RingDiagram D} {h : Presheaf.IsSheaf D.totalTopology R.presheaf}

/-- The term `X_n = ℓ_n e_n B`, using the specified exact free extension.
Source: Stacks Project, spaces-simplicial.tex, Tags 0D9E and 0D9Q, face-only adaptation
(blueprint: lem-sfb-semisimplicial-cartesian-simplex-filtration). -/
abbrev cartesianSimplexTerm (P : Presentation R h)
    (L : ∀ n : ℕ, EvaluationFreeExtension P (op (SemiSimplexCategory.mk n)))
    (B : (R.total h).D) (n : ℕ) : (R.total h).D :=
  (L n).ordinary.mapDerivedCategory.obj
    ((P.evaluation (op (SemiSimplexCategory.mk n))).derived.obj B)

/-- The map from `X_n` to `X_m` adjunct to the inverse cartesian transition followed
by the inclusion of the `a`-labelled summand. In particular, taking the opposite
of `δ_i : [0] ↪ [1]` gives exactly the map `q_i` in the statement.
Source: Stacks Project, spaces-simplicial.tex, Tags 0D9B and 0D9E, face-only adaptation
(blueprint: lem-sfb-semisimplicial-cartesian-simplex-filtration). -/
def cartesianSimplexFace (P : Presentation R h)
    (L : ∀ n : ℕ, EvaluationFreeExtension P (op (SemiSimplexCategory.mk n)))
    (B : (R.total h).D) (hB : P.IsCartesian B) {m n : ℕ}
    (a : op (SemiSimplexCategory.mk n) ⟶ op (SemiSimplexCategory.mk m)) :
    cartesianSimplexTerm P L B n ⟶ cartesianSimplexTerm P L B m :=
  ((L n).derivedAdjunction.homEquiv _ _).symm
    (@CategoryTheory.inv _ _ _ _ ((P.derivedTransition a).app B) (hB a) ≫
      ((L m).derivedInclusion a).app
        ((P.evaluation (op (SemiSimplexCategory.mk m))).derived.obj B))

/-- The cartesian simplex filtration, its signed first boundary, and its distinguished
sequential telescope, including the coproduct after shifting.

Source: Stacks Project, spaces-simplicial.tex, Tags 0D9B, 0D9E and 0D9Q;
agent-supplied injective-order-map adaptation
(blueprint: lem-sfb-semisimplicial-cartesian-simplex-filtration).

Proof: (1) Represent B by an arbitrary unbounded complex C of total modules. In
component m let A_p be the sum of copies of C_m labelled by injections [p] ↪ [m].
A transition carries the a summand to the ba summand using C's transition. Define
the faces by deleting vertices, and b_p by their alternating sum. The semisimplicial
identities give b squared zero and the fold augmentation kills b_1.
(2) By lem-sfb-semisimplicial-evaluation-free-adjoint, transitions induce a map
ℓ_p C_p → A_p. Exact pullback and cartesianness make every labelled component a
quasi-isomorphism. Exact jointly conservative evaluations from
lem-sfb-semisimplicial-ringed-total-category detect that this is a quasi-isomorphism.
Thus X_p is isomorphic to Q(A_p), with the augmentation at p = 0 the counit.
(3) Totalize the first N+1 horizontal terms with differential b + (-1)^p d_C.
The horizontal and vertical mixed terms cancel. The total T over all p is finite
in component m, since p > m gives an empty sum. The finite totals T_N stabilize
there for N ≥ m, so T is their degreewise colimit. The fold gives compatible
augmentations T_N → C and T → C.
(4) In component m contract the augmented simplex by adjoining the minimum vertex
0 to a label not containing it, and use zero when it already contains 0. The
horizontal identity is bh + hb = 1 - eε, and the vertical terms cancel by the
opposite totalization signs. Hence Dh + hD = 1 - et and te = 1. This makes T → C
a componentwise homotopy equivalence, hence a quasi-isomorphism by conservative
exact evaluation. This contraction need not respect transitions.
(5) The degreewise split sequence T_N → T_(N+1) → A_(N+1)[N+1] gives a distinguished
triangle by lem-weil-pbc-degreewise-split-derived-triangle. Transport by the
isomorphisms of (2), taking K_0 literally X_0, to obtain the asserted triangles,
structure maps, augmentations, and the counit at zero.
(6) T_1 is the cone of b_1 = d_0 - d_1. The adjunct of d_i after the comparison
from (2) is the inverse cartesian transition followed by the δ_i inclusion.
The normalized derived adjunction therefore identifies this map with q_i.
Transporting the cone triangle gives the asserted first-stage triangle.
(7) Apply lem-kun-complex-colimit-hocolim to T_N in the small total ringed site.
It gives the derived coproduct and its distinguished telescope triangle with
third vertex Q(T). Replace Q(T) by B using (4), and replace the zeroth summand
using (2). This supplies s, p and the boundary with the stated restrictions.
(8) The shift equivalence preserves this coproduct: the shift adjunction and its
universal property identify Hom(S[1], Y) with the product of Hom(K_N[1], Y),
by restriction along the shifted coprojections. No step bounds C or assumes
negative Hom vanishing. -/
theorem semisimplicial_cartesian_simplex_filtration (P : Presentation R h)
    (exact : ∀ {m n : SemiSimplexCategoryᵒᵖ} (a : m ⟶ n),
      PreservesFiniteLimits (P.pullback a).ordinary ∧
        PreservesFiniteColimits (P.pullback a).ordinary)
    (L : ∀ n : ℕ, EvaluationFreeExtension P (op (SemiSimplexCategory.mk n)))
    (B : (R.total h).D) (hB : P.IsCartesian B) :
    ∃ (K : ℕ → (R.total h).D) (u : ∀ N : ℕ, K N ⟶ K (N + 1))
      (j : ∀ N : ℕ, K N ⟶ B),
      (∀ N : ℕ, u N ≫ j (N + 1) = j N) ∧
      ∃ hK : K 0 = cartesianSimplexTerm P L B 0,
        j 0 = eqToHom hK ≫ (L 0).derivedAdjunction.counit.app B ∧
        (∀ N : ℕ,
          ∃ (v : K (N + 1) ⟶ (cartesianSimplexTerm P L B (N + 1))⟦(N + 1 : ℤ)⟧)
            (w : (cartesianSimplexTerm P L B (N + 1))⟦(N + 1 : ℤ)⟧ ⟶ K N⟦(1 : ℤ)⟧),
            Triangle.mk (u N) v w ∈ distTriang (R.total h).D) ∧
        (∃ w : K 1 ⟶ (cartesianSimplexTerm P L B 1)⟦(1 : ℤ)⟧,
          Triangle.mk
            ((cartesianSimplexFace P L B hB
                (SemiSimplexCategory.homOfMono (SimplexCategory.δ (0 : Fin 2))).op -
              cartesianSimplexFace P L B hB
                (SemiSimplexCategory.homOfMono (SimplexCategory.δ (1 : Fin 2))).op) ≫
              eqToHom hK.symm)
            (u 0) w ∈ distTriang (R.total h).D) ∧
        ∃ (S : (R.total h).D) (ι : ∀ N : ℕ, K N ⟶ S) (s : S ⟶ S)
          (p : S ⟶ B) (boundary : B ⟶ S⟦(1 : ℤ)⟧),
          Nonempty (IsColimit (Cofan.mk S ι)) ∧
          (∀ N : ℕ, ι N ≫ s = u N ≫ ι (N + 1)) ∧
          (∀ N : ℕ, ι N ≫ p = j N) ∧
          Triangle.mk (𝟙 S - s) p boundary ∈ distTriang (R.total h).D ∧
          Nonempty (IsColimit (Cofan.mk (S⟦(1 : ℤ)⟧)
            (fun N : ℕ ↦ (shiftFunctor (R.total h).D (1 : ℤ)).map (ι N)))) := by
  sorry

end CategoryTheory.SemisimplicialRingedTotal
