/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

/-!
# Restriction of abelian Zariski sheaves to an open

Source: Stacks Project, Cohomology on Sites, Lemma 03F3 and its proof; Cohomology of
Sheaves, Lemma 01E1 (blueprint: lem-weil-pbc-zariski-open-restriction-injectives).
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

/-- Restriction is additive because morphisms and their sums restrict componentwise.
Source: Stacks Project, Lemma 03F3, restriction construction
(blueprint: lem-weil-pbc-zariski-open-restriction-injectives).

Proof: Step 1 of the node: coverings inside U are also coverings in X, so the restricted
presheaf is a sheaf. Restriction of morphisms is componentwise, and addition of morphisms
of abelian sheaves is sectionwise (lem-weil-pbc-abelian-presheaves-evaluation-exact).
Consequently restriction commutes with sums and zero morphisms. -/
@[instance]
theorem zariski_open_restriction_additive (X : Scheme.{u}) (U : X.Opens) :
    (U.sheafRestrict (C := AddCommGrpCat.{u})).Additive := by
  sorry

/-- Open restriction of abelian sheaves is exact and preserves injectives.
Source: Stacks Project, Lemmas 03F3 and 01E1 and their proofs
(blueprint: lem-weil-pbc-zariski-open-restriction-injectives).

Proof: Step 1: the coverings of an open inside U are the same as in X, so precomposition
is a sheaf, acts componentwise on morphisms, and respects addition. Step 2: kernels are
computed sectionwise (lem-weil-pbc-sheafification-exact). Exactness is equivalently that
the map to the kernel is epi (lem-weil-pbc-abelian-exact-iff-epi-kernel-lift). An epi is
locally surjective (lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective), and the same
local lifts work inside U. Step 3: extension by zero is an exact left adjoint of restriction
(lem-weil-pbc-zariski-extension-by-zero-adjunction and
lem-weil-pbc-zariski-extension-by-zero-exact). Thus restriction preserves injectives by
lem-sp-right-adjoint-preserves-injectives. -/
theorem zariski_open_restriction_injectives (X : Scheme.{u}) (U : X.Opens) :
    (∀ S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
      S.Exact → (S.map (U.sheafRestrict (C := AddCommGrpCat.{u}))).Exact) ∧
    (∀ I : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u},
      Injective I → Injective ((U.sheafRestrict (C := AddCommGrpCat.{u})).obj I)) := by
  sorry

/-- Restricting an injective resolution gives the termwise restricted resolution with the
restricted augmentation. Its global section complex on U equals evaluation of the original
complex at U, including the differentials.
Source: Stacks Project, Lemma 03F3, proof of (2), and Lemma 01E1
(blueprint: lem-weil-pbc-zariski-open-restriction-injectives).

Proof: Step 4: apply exactness from Steps 1--2 of zariski_open_restriction_injectives to
every consecutive triple of the augmented resolution (def-weil-pbc-exact-sequence), and
apply Step 3 to every injective term (def-sp-injective-resolutions). This produces the
restricted injective resolution. Evaluation at the terminal open of U is evaluation at U
in X, both on objects and differentials (def-weil-pbc-sites-and-cohomology), proving the
section-complex equality. -/
theorem zariski_open_restriction_injectiveResolution (X : Scheme.{u}) (U : X.Opens)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (I : InjectiveResolution F) :
    (∃ (J : InjectiveResolution ((U.sheafRestrict (C := AddCommGrpCat.{u})).obj F))
      (h : J.cocomplex =
        ((U.sheafRestrict (C := AddCommGrpCat.{u})).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex),
      J.ι.f 0 ≫ eqToHom (congrArg (fun K ↦ K.X 0) h) =
        (U.sheafRestrict (C := AddCommGrpCat.{u})).map (I.ι.f 0)) ∧
    (((sheafSections (Opens.grothendieckTopology U)
      AddCommGrpCat.{u}).obj (op ⊤)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
        (((U.sheafRestrict (C := AddCommGrpCat.{u})).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex) =
      (((sheafSections (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).obj (op U)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex := by
  sorry

end AlgebraicGeometry
