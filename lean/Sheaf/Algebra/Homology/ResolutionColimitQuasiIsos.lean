/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Category.Preorder

import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Sheaf.Algebra.Homology.BoundedStageRoofComparison
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits

/-!
# Quasi-isomorphisms between colimits of resolving towers

Source: Stacks Project, Derived Categories, Tag 0794,
`proposition-left-derived-exists`, the cone argument and the claim beginning "Suppose that".
(blueprint: lem-trf-resolution-colimit-quasi-isos).

The index `k : ℕ` represents the positive stage `k + 1`. The diagrams carry the transitions;
the cocones carry compatible augmentations, and their colimit property is imposed degreewise.
-/

@[expose] public section

set_option autoImplicit false

universe uA vA uB vB

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace CategoryTheory.Functor

/-- An additive functor satisfying the bounded-above acyclicity condition on a
quotient-generating additive class preserves any quasi-isomorphism between termwise
sequential colimits of towers resolving successive good truncations. No map between
these towers inducing the given quasi-isomorphism is required.

Source: Stacks Project, Derived Categories, Tag 0794,
`proposition-left-derived-exists`, first paragraph and the claim beginning "Suppose that"
through the cohomology-colimit calculation.
(blueprint: lem-trf-resolution-colimit-quasi-isos).

Proof:
1. Pass from P to its isomorphism closure. This contains zero, is closed under finite
   biproducts and covers every object by an epimorphism. For a bounded-above acyclic
   complex in this closure, choose degreewise P-representatives (zero above a bound)
   and transport the differentials along their isomorphisms. This produces an acyclic
   bounded-above P-complex isomorphic to the original one. The assumed acyclicity
   after F and functoriality of homology transfer it back to the original complex.
2. For a quasi-isomorphism between bounded-above complexes in this closure, its cone
   is acyclic by lem-pur-quasi-iso-cone-acyclic. The cone terms are finite biproducts,
   so step 1 applies. Additivity identifies its F-image with the cone of the F-image
   map (including the negative differential). Apply the cone criterion again to
   conclude that F preserves this bounded-above quasi-isomorphism.
3. Apply lem-trf-bounded-stage-roof-comparison to this isomorphism closure and step 2.
   Obtain cohomology isomorphisms between the F-images of E and G, compatible both
   with their transitions and with the augmentations followed by F(alpha). This is
   valid for the arbitrary given alpha, without a morphism of towers.
4. Preservation of sequential colimits by F makes the image augmentation cocones
   termwise colimits. Degreewise colimit universality also makes them colimits of
   complexes: the induced maps commute with differentials after every cocone leg,
   hence commute by uniqueness. By src-weil-homology-preserves-exact-colimits and
   exact sequential colimits in B, their cohomology cocones are colimits in every
   degree. Exactness of sequential colimits in A is unnecessary.
5. For each degree, the inverses of the compatible isomorphisms of step 3 induce a
   map from the cohomology of F(Y) to that of F(X), by colimit universality. The
   augmentation equation of step 3 shows that both composites with H(F(alpha))
   are identities after every colimit leg, hence are identities by uniqueness.
   Thus every homology map of F(alpha) is invertible, which is a quasi-isomorphism.
-/
theorem resolution_colimit_quasiIso
    {A : Type uA} [Category.{vA} A] [Abelian A]
    {B : Type uB} [Category.{vB} B] [Abelian B]
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ B]
    (F : A ⥤ B) [F.Additive] [PreservesColimitsOfShape ℕ F]
    (P : A → Prop) (hzero : P (0 : A))
    (hsum : ∀ (M N : A), P M → P N → P (M ⊞ N))
    (hcover : ∀ M : A, ∃ (N : A) (p : N ⟶ M), P N ∧ Epi p)
    (hF : ∀ K : CochainComplex A ℤ,
      (∃ b : ℤ, ∀ j : ℤ, b < j → IsZero (K.X j)) →
      (∀ j : ℤ, P (K.X j)) → K.Acyclic →
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).Acyclic)
    (E G : ℕ ⥤ CochainComplex A ℤ)
    (hEbound : ∀ k : ℕ, ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero ((E.obj k).X j))
    (hGbound : ∀ k : ℕ, ∃ b : ℤ, ∀ j : ℤ, b < j → IsZero ((G.obj k).X j))
    (hEterms : ∀ (k : ℕ) (j : ℤ), ∃ M : A, P M ∧ Nonempty (M ≅ (E.obj k).X j))
    (hGterms : ∀ (k : ℕ) (j : ℤ), ∃ M : A, P M ∧ Nonempty (M ≅ (G.obj k).X j))
    (X Y : CochainComplex A ℤ)
    (e : E ⟶ (Functor.const ℕ).obj X) (g : G ⟶ (Functor.const ℕ).obj Y)
    (hecolim : ∀ j : ℤ, IsColimit
      ((HomologicalComplex.eval A (ComplexShape.up ℤ) j).mapCocone (Cocone.mk X e)))
    (hgcolim : ∀ j : ℤ, IsColimit
      ((HomologicalComplex.eval A (ComplexShape.up ℤ) j).mapCocone (Cocone.mk Y g)))
    (hEvanish : ∀ (k : ℕ) (j : ℤ), (k : ℤ) + 1 < j →
      IsZero ((E.obj k).homology j))
    (hGvanish : ∀ (k : ℕ) (j : ℤ), (k : ℤ) + 1 < j →
      IsZero ((G.obj k).homology j))
    (heiso : ∀ (k : ℕ) (j : ℤ), j ≤ (k : ℤ) + 1 →
      IsIso (HomologicalComplex.homologyMap (e.app k) j))
    (hgiso : ∀ (k : ℕ) (j : ℤ), j ≤ (k : ℤ) + 1 →
      IsIso (HomologicalComplex.homologyMap (g.app k) j))
    (α : X ⟶ Y) (hα : QuasiIso α) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α) := by
  sorry

end CategoryTheory.Functor
