/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Sections on a finite coproduct in a small étale site

Source: literature/stacks-project/pione.tex, Tag 03SF, finite Galois descent
calculation (sections on the finite disjoint union)
(blueprint: lem-exc-finite-galois-sheaf-sections-coproduct).
-/

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: literature/stacks-project/pione.tex, Tag 03SF, finite Galois descent
calculation (blueprint: lem-exc-finite-galois-sheaf-sections-coproduct).

Step 1 (lem-weil-pbc-scheme-coproduct-family): the coprojections are open
immersions with disjoint images covering X. Open immersions are étale (Stacks
Tag 02GP), so the family is a covering in the small étale site of S
(def-weil-pbc-etale-sheaf-of-sets). Off-diagonal pullbacks are empty. On the
diagonal, the two pullback projections coincide because each open immersion
is a monomorphism.

Step 2 (def-weil-pbc-etale-sheaf-of-sets; Stacks, sites.tex, Definition 00VM):
apply the sheaf equalizer condition to this covering. Restrictions to an
off-diagonal overlap agree because sections on the empty object form a
singleton; diagonal restrictions agree by Step 1. Every family is therefore
compatible and has a unique glued section. Restriction is consequently a
bijection, and its components are the displayed restriction maps. The inverse
of the equivalence is precisely unique gluing: its inverse laws and the
component formula give existence and uniqueness of a section restricting to
any given family. For the empty finite family, both sides are singletons.
-/
theorem finiteEtaleCoproductSections
    (S : Scheme.{u})
    (F : Sheaf S.smallEtaleTopology (Type v))
    {I : Type w} [Finite I]
    (X : S.Etale) (Xi : I → S.Etale) (j : ∀ i, Xi i ⟶ X)
    (hopenclosed : ∀ i, IsOpenImmersion (j i).left ∧ IsClosedImmersion (j i).left)
    (hcop : IsColimit (Cofan.mk X j))
    (hoverlap : ∀ ⦃i k : I⦄, i ≠ k →
      IsInitial (pullback (j i) (j k)))
    (hempty : ∀ (e : S.Etale), IsInitial e →
      Nonempty (F.obj.obj (op e)) ∧ Subsingleton (F.obj.obj (op e))) :
    Sieve.ofArrows Xi j ∈ S.smallEtaleTopology X ∧
    ∃ e : F.obj.obj (op X) ≃ (∀ i, F.obj.obj (op (Xi i))),
      ∀ (s : F.obj.obj (op X)) (i : I),
        e s i = F.obj.map (j i).op s := by
  sorry

end AlgebraicGeometry.Scheme
