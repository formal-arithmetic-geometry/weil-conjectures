/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Sheaf.CategoryTheory.EssentiallyConstantSystem

/-!
# Mittag-Leffler systems in a short exact sequence

Source: Stacks Project, Homology, Lemma 12.31.6, Tag 070D
(blueprint: lem-weil-pbc-exact-sequence-ml).
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory.ShortComplex

/-- In a termwise short exact sequence of inverse systems of abelian groups, an essentially
constant quotient makes the kernel Mittag-Leffler exactly when the middle system is
Mittag-Leffler (Stacks Project, Homology, Lemma 12.31.6, Tag 070D).
The index `n : ℕ` denotes the positive index `n + 1`; composing with `forget AddCommGrpCat`
expresses ML by the existing underlying-set definition, equivalently stabilization of images
as subgroups.

Proof (following the nine steps of the node):
1. By injectivity of the first map, identify each A_i with the kernel inside B_i. Naturality
identifies its transitions with restrictions of those of B. Dropping finitely many indices
preserves ML: witnesses on the tail work there, and for an earlier i use the witness at the
first retained index N and factor all transitions through N.
2. Apply `lem-weil-pbc-essentially-constant-splitting` to the cone and retraction provided by
`def-weil-pbc-essentially-constant-system`. After dropping a finite initial segment,
C_j = π_j(X) ⊕ Z_j, with compatible projections p_j to X and transitions on Z_j that are
zero eventually into each fixed term. The projection q_j(c) = c - π_j(p_j(c)) onto Z_j
is surjective, has kernel π_j(X), and commutes with transitions.
3. For an essentially zero quotient Z', choose m* ≥ m whose transition into Z'_m is zero.
Then B'_{m*} maps into A'_m. For k ≥ m* and i ≤ m this gives, inside B'_i,
Im(A'_k → A'_i) ⊆ Im(B'_k → B'_i) ⊆ Im(A'_m → A'_i).
4. If A' is ML at i with witness c, choose c* as in step 3. For k ≥ c*, both outer
images in the inclusion chain equal Im(A'_c → A'_i), so the middle images stabilize.
Conversely, if B' is ML with witness c, for k ≥ c use step 3 with m = k and k* ≥ k.
The two B' images surrounding the A'_k image equal the stabilized B' image. Thus A' is ML.
5. Put B'_i = v_i⁻¹(π_i(X)). Naturality makes these subgroups a tower. The composite
q_i v_i is surjective with kernel B'_i and gives an exact sequence B' → B → Z.
Steps 3 and 4 imply that B' is ML exactly when B is ML.
6. Restrict p_i v_i to B'_i to obtain s_i : B'_i → X. Its kernel is A_i, since
π_i(X) ∩ Z_i = 0; it is surjective by lifting π_i(x) along v_i. These maps commute
with transitions into the constant system X, giving 0 → A_i → B'_i → X → 0.
7. Write I_{k,i} and J_{k,i} for the transition images of A and B'. For k ≥ i,
s_i(J_{k,i}) = X since s_i b_{k,i} = s_k is surjective. Also J_{k,i} ∩ A_i = I_{k,i}:
a lift b of an element in that intersection satisfies s_k(b) = 0, hence lies in A_k.
Thus 0 → I_{k,i} → J_{k,i} → X → 0 is exact.
8. If I stabilizes at c, take y ∈ J_{c,i} and k ≥ c. Surjectivity in step 7 gives
y' ∈ J_{k,i} with s_i(y') = s_i(y). Then y - y' lies in I_{c,i} = I_{k,i}, hence
in J_{k,i}, so J stabilizes. Conversely, if J stabilizes, intersect with A_i and use
step 7 to see that I stabilizes.
9. Combining tail invariance, step 8, step 5, and tail invariance again gives the stated
ML equivalence for A and B. ML throughout is `def-weil-pbc-mittag-leffler-system`.
(blueprint: lem-weil-pbc-exact-sequence-ml) -/
theorem isMittagLeffler_iff_of_isEssentiallyConstant
    (S : ShortComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{u}))
    (hS : ∀ n : ℕᵒᵖ, (S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).ShortExact)
    (hC : S.X₃.IsEssentiallyConstant) :
    (S.X₁ ⋙ forget AddCommGrpCat).IsMittagLeffler ↔
      (S.X₂ ⋙ forget AddCommGrpCat).IsMittagLeffler := by
  sorry

end CategoryTheory.ShortComplex
