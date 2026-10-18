/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal

/-!
# Kernel pair of the fppf quotient of an equivalence relation

Source: Stacks Project, Groupoids, Tag 045Y and the preceding quotient-sheaf definition,
with the monomorphism hypothesis (blueprint: lem-trf-etale-relation-kernel-pair).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A monomorphic equivalence relation is the kernel pair of its fppf sheaf quotient.
The presheaf coequalizer is the pointwise quotient. The pair `F, η`, with `hη`, specifies
its sheafification by the universal property of `presheafToSheaf`, without requiring
sheafification for every small-valued presheaf on the big site. The pullback assertion
says precisely that the canonical relation-to-kernel-pair map is an isomorphism: the
representables are fppf sheaves, and their pullback is computed in presheaves.
Source: Stacks Project, Groupoids, Tag 045Y and the preceding quotient-sheaf definition
(blueprint: lem-trf-etale-relation-kernel-pair).

Proof:
1. For a test scheme, equality in the pointwise quotient is the existence of a single
   relation witness, since `hrel` is already an equivalence relation. Equality after
   sheafification is locally equality before sheafification, by
   lem-weil-pbc-site-sheafification-sections-local (Stacks Tags 00WB and 00WK).
   Thus a pair with equal quotient images locally lifts to the relation, as in Tag 045Y.
2. Two relation sections with the same projections are equal by monicity of `(s,t)`.
   This proves local injectivity of the canonical map.
3. Apply lem-galois-set-sheaf-local-bijection-isomorphism to local surjectivity from
   Step 1 and local injectivity from Step 2. The resulting isomorphism onto the kernel
   pair is equivalent to the asserted pullback square. -/
theorem etale_relation_kernel_pair {S : Scheme.{u}} {R U : Over S} (s t : R ⟶ U)
    [Mono (prod.lift s t)]
    (hrel : ∀ T : Over S, Equivalence (fun a b : T ⟶ U ↦
      ∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b))
    (F : Sheaf (Scheme.fppfTopology.over S) (Type u))
    (η : coequalizer (yoneda.map s) (yoneda.map t) ⟶ F.obj)
    (hη : ∀ G : Sheaf (Scheme.fppfTopology.over S) (Type u),
      Function.Bijective (fun g : F.obj ⟶ G.obj ↦ η ≫ g)) :
    IsPullback (yoneda.map s) (yoneda.map t)
      (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η)
      (coequalizer.π (yoneda.map s) (yoneda.map t) ≫ η) := by
  sorry

end AlgebraicGeometry.Scheme
