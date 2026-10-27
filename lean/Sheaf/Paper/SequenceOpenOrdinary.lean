/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SequenceSiteOpenData

/-! # Existence of open extension on ringed sequence sites

Source: Stacks Project, Tags 03DI, 03DJ and 05RU
(blueprint: lem-pur-sequence-open-ordinary).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r u s
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory
namespace WeilConjectures.SemilinearSections

/-- Ordinary extension by zero on a sequence site, with its actual horizontal transitions.
The prescribed coefficient datum has the summand normalization, rather than an arbitrary
automorphism of a level extension.
Source: Stacks Project, sites.tex Tags 04GZ and 0791; sites-modules.tex Tags 04IE,
03DI and 03DJ (blueprint: lem-pur-sequence-open-ordinary).

Proof: form the constant-in-index sheaf represented by the open object. Its element
site is the product of the index poset with the slice site: an object is (n,X,s:X→V),
and both sites have the same vertical covering sieves. The restricted ring is B_n(X).
The element-site slice equivalence therefore gives the geometric localization, including
its sectionwise inverse image and identity structural ring map. Transport through a
small presentation if the site and coefficient universes differ. Module restriction L
is sectionwise, is left adjoint to the induced geometric direct image, and is exact.

At level n put (JM)_n=j_{!,B_n}M_n. For n≤m extend the actual transition of M by
j_{!,B_m}, then apply the supplied normalized coefficient comparison. Its naturality
and composition equation give the triple-index system law; its identity equation gives
the identity transition. Apply each level functor to morphisms to construct J. Transpose
a family of level maps along the fixed open adjunctions. Their transition squares are
preserved and reflected because the coefficient comparison commutes with units and
counits. This constructs J⊣L with the stated evaluated unit and counit equations.
Uniqueness of a left adjoint identifies J with extension on the geometric slice topos,
so J is additive and exact. The level isomorphisms are the identity on the constructed
components, and their transition equation is the definition of the new transition.
The scalar-restriction identification between the composite localized tower map and
the restriction of the composite ambient map is the sectionwise identity: both compose
the same ring homomorphisms. The chosen coefficient datum is retained throughout.
Empty opens, zero rings, equality indices and non-flat coefficient maps require no
change to this construction. -/
theorem sequenceOpenOrdinary (W : Scheme.{u}) (V : W.ProEt)
    [IsOpenImmersion V.hom]
    (B : ℕ → Sheaf (Scheme.ProEt.topology W) CommRingCat.{max (u + 1) r})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
    (A : SequenceOpenCoefficientData.{u + 1, u, r} (Scheme.ProEt.topology W) V) :
    ∃ O : SequenceOpenOrdinary.{u + 1, u, r} (Scheme.ProEt.topology W) V B τ,
      O.coefficients = A ∧ O.Transitions := by
  sorry

end WeilConjectures.SemilinearSections
