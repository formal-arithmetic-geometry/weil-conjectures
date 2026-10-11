/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Mittag-Leffler quotients and exact inverse limits

Source: Stacks Project, Homology, Lemma Tag 02N1, parts (2) and (3)
(blueprint: lem-weil-pbc-mittag-leffler-limit-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

/-- A termwise short exact sequence of towers of abelian groups has ML quotient when its
middle system is ML, and its inverse limit is short exact when its kernel is ML.
Source: Stacks Project, Homology, Tag 02N1 (2), (3); Algebra, Tags 0598 and 03CA.
(blueprint: lem-weil-pbc-mittag-leffler-limit-exact)

The index `n : ℕ` denotes the positive index `n + 1`. Towers and their morphisms are
functors `ℕᵒᵖ ⥤ AddCommGrpCat` and natural transformations (`def-weil-inverse-system`), and
the sequence `0 → A → B → C → 0` is the short complex `S` of towers, short exact at every
index (`hS`), as in `isMittagLeffler_iff_of_isEssentiallyConstant` (Tag 070D). ML is
Mathlib's `IsMittagLeffler` of the underlying-set system
(`def-weil-pbc-mittag-leffler-system`); the images decrease, so it is stabilization of
images as subgroups. The inverse limit is Mathlib's `lim`, which in `AddCommGrpCat` is the
group of compatible sequences, and `S.map lim` is `0 → lim A → lim B → lim C → 0` with the
induced maps; its short exactness is injectivity of `lim u`, exactness at `lim B` and
surjectivity of `lim v`.

Proof (the node's six steps):
1. Write a, b, t for transitions of A, B, C, and use functoriality for their composites
from k to i. Naturality of u and v gives commuting squares for these composites.
Termwise exactness means u is injective, v is surjective, and ker v = im u.
Compatibility of a sequence with adjacent transitions implies compatibility with composites.
2. If B is ML at i with witness c, then surjectivity of v at k and naturality give
im(t_{k,i}) = v_i(im(b_{k,i})). Stabilization for B therefore implies stabilization
for C with the same witness c (`def-weil-pbc-mittag-leffler-system`).
3. Assume A is ML and fix a compatible c in the limit of C. The fibres E_i = v_i⁻¹(c_i)
are nonempty by surjectivity. Naturality and compatibility restrict b to a tower of
nonempty sets (`def-weil-inverse-system`).
4. Choose j witnessing ML for A at i. For k ≥ j, the image of E_k in E_i is contained
in that of E_j. For the reverse inclusion take e_j in E_j and any e'_k in E_k.
Put e'_j = b_{k,j}(e'_k). Exactness writes e_j - e'_j = u_j(α).
Stabilization supplies β in A_k with a_{k,i}(β) = a_{j,i}(α).
Then x_k = e'_k + u_k(β) is in E_k and b_{k,i}(x_k) = b_{j,i}(e_j).
Thus E is ML (`def-weil-pbc-mittag-leffler-system`).
5. Apply `lem-weil-pbc-ml-sets-tower-limit-nonempty` to obtain compatible e_i in E_i.
This gives a preimage of c, proving surjectivity of the map on limits.
6. Left exactness is `lem-weil-pbc-tower-limit-exact-surjective-kernels` (b), applied
with R = ℤ and the canonical module structures on abelian groups. Combine with step 5. -/
theorem mittagLeffler_quotient_and_limit_exact
    (S : ShortComplex (ℕᵒᵖ ⥤ AddCommGrpCat.{u}))
    (hS : ∀ n : ℕᵒᵖ, (S.map ((evaluation ℕᵒᵖ AddCommGrpCat).obj n)).ShortExact) :
    ((S.X₂ ⋙ forget AddCommGrpCat).IsMittagLeffler →
      (S.X₃ ⋙ forget AddCommGrpCat).IsMittagLeffler) ∧
    ((S.X₁ ⋙ forget AddCommGrpCat).IsMittagLeffler →
      (S.map (lim : (ℕᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u})).ShortExact) := by
  sorry

end CategoryTheory.ShortComplex
