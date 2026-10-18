/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q61
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Functor
import Sheaf.CategoryTheory.TruncationDescends
import WeilConjectures.CategoryTheory.TruncationTriangle

/-!
# Finite cohomological amplitude from bounds on cohomology objects

Source: Stacks Project, derived.tex, Tag 08J5, remark-truncation-distinguished-triangle;
more-etale.tex, Tag 0G2A, lemma-derived-lower-shriek-bounded, proof of (3)
(blueprint: lem-pur-bounded-heart-amplitude).
-/

@[expose] public section

universe uA vA wA uB vB wB

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace DerivedCategory

/-- An exact triangulated functor bounded on a class of heart objects has the corresponding
finite cohomological amplitude on bounded objects with cohomology in that class.
Source: Stacks Project, derived.tex, Tag 08J5; more-etale.tex, Tag 0G2A, proof of (3)
(blueprint: lem-pur-bounded-heart-amplitude).

Proof:
1. Choose a complex C representing K. Let K_q be its canonical upper truncation at q.
   By lem-weil-pbc-truncation-descends its cohomology agrees with that of K through q
   and vanishes above q. Induct on n from 0 to b-a+1, bounding T(K_{a-1+n}) in
   the fixed interval [a+c,b+d]. This is a finite induction and uses no limit.
2. For a <= q <= b, the heart hypothesis bounds T(H^q(K)[0]) in [c,d]. The shift
   comparisons of T and lem-sp-derived-cohomology-shift identify the cohomology in
   degree i of T(H^q(K)[-q]) with that in degree i-q of T(H^q(K)[0]). It therefore
   vanishes outside [q+c,q+d], hence outside [a+c,b+d].
3. K_{a-1} is acyclic, so its representative is quasi-isomorphic to zero and K_{a-1}
   is zero in the derived category. Exactness implies additivity of T, hence T
   preserves zero objects. This gives the base case.
4. Use lem-weil-pbc-truncation-triangle to obtain the distinguished triangle
   K_{q-1} -> K_q -> H^q(K)[-q] -> K_{q-1}[1]. Exactness of T preserves this triangle.
   By lem-sf-derived-homology-long-exact, its degree-i cohomology is exact at the
   middle term. Outside [a+c,b+d], the adjacent terms vanish by induction and step 2,
   forcing the middle term to vanish.
5. Finally, K_b -> K induces isomorphisms on every cohomology object, using the upper
   bound b, and is therefore an isomorphism in the localization D(A). Applying T and
   cohomology transports the bound to T(K). No product preservation or completeness
   assumption has been used. -/
theorem bounded_heart_amplitude
    (A : Type uA) [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (B : Type uB) [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
    (T : DerivedCategory A ⥤ DerivedCategory B) [T.CommShift ℤ] [T.IsTriangulated]
    (S : A → Prop)
    (_hSiso : ∀ (M N : A), (M ≅ N) → S M → S N)
    (_hSzero : S (0 : A))
    (c d : ℤ) (_hcd : c ≤ d)
    (_hHeart : ∀ (M : A), S M → ∀ (i : ℤ), i < c ∨ d < i →
      IsZero ((homologyFunctor B i).obj (T.obj ((singleFunctor A 0).obj M))))
    (a b : ℤ) (_hab : a ≤ b) (K : DerivedCategory A)
    (_hK : ∀ (r : ℤ), r < a ∨ b < r → IsZero ((homologyFunctor A r).obj K))
    (_hKS : ∀ (r : ℤ), S ((homologyFunctor A r).obj K)) :
    ∀ (i : ℤ), i < a + c ∨ b + d < i → IsZero ((homologyFunctor B i).obj (T.obj K)) := by
  sorry

end DerivedCategory
