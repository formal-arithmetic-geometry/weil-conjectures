/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Order.RelClasses
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Component data for a well-ordered projective presentation

Source: Stacks Project, Algebra, Lemma 0D1U, direct-sum presentation construction,
adapted to supplied projective augmentations and arbitrary index universes.
(blueprint: lem-weil-pbc-well-ordered-presentation-component-data).
-/

@[expose] public section

universe u v w

namespace ModuleCat

open CategoryTheory

/-- Construct the filtered projective middle module and its component maps, before
intersecting with the kernel of the presentation.
Source: Stacks Project, Algebra, Lemma 0D1U, direct-sum presentation construction;
the active-index size reduction is the construction in the parent node.
(blueprint: lem-weil-pbc-well-ordered-presentation-component-data).

Proof: let V_e be the supremum of F_i for i < e, and call e active when
F_e / (V_e.comap F_e.subtype) is nonzero. Choose x_e in F_e outside V_e at each
active index. If e < f, then x_e belongs to V_f whereas x_f does not, so these
choices give an injection of the active indices into M. Hence they are small
in universe v, and their shrunk type can index a direct sum B in universe v.
For each active e, lift the supplied projective degree-zero augmentation
through the quotient epimorphism F_e → F_e / V_e using categorical projectivity.
Define b on each summand by this lift followed by F_e.subtype. Define H_e by
support in indices at most e. These submodules are monotone and exhaustive:
a finite nonempty support has a largest index, and for empty support an index
exists by applying hcover to zero. B is categorically projective by lifting
maps from each summand through an epimorphism and summing the lifts.

Prove map b H_e = F_e by well-founded induction. The inclusion into F_e
follows from monotonicity. For the reverse inclusion, at an active stage lift
the quotient class using surjectivity of the augmentation, subtract the image
of the corresponding summand, and obtain an element of V_e. The nonempty
predecessor chain has supremum equal to its union, so induction lifts this
remainder from an earlier partial sum. If there are no predecessors, V_e is
zero. At an inactive stage F_e = V_e and induction alone suffices.

At an inactive stage no summand is added, so H_e is the predecessor supremum.
At an active stage take p to be the component projection. It is surjective by
the summand inclusion. Its kernel is the vectors supported strictly before e;
finite support identifies this with the predecessor supremum pulled back to
H_e. Take a to be b restricted to H_e with codomain F_e. After quotienting,
every earlier summand vanishes, and the e summand gives the augmentation,
which proves the displayed commuting identity. This also handles repeated
stages (inactive), a least active stage (zero predecessors), and M = 0 (no
active indices). No object is defined by choosing from this unfinished theorem. -/
theorem exists_projective_presentation_component_data
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    {E : Type w} [LinearOrder E] [IsWellOrder E (· < ·)]
    (F : E → Submodule R M) (hF : Monotone F)
    (hcover : ∀ x : M, ∃ e : E, x ∈ F e)
    (P : ∀ e : E, ProjectiveResolution
      (ModuleCat.of R ((F e) ⧸
        ((⨆ i : {j : E // j < e}, F i.val).comap (F e).subtype)))) :
    ∃ (B : ModuleCat.{v} R) (_ : Projective B) (b : B →ₗ[R] M)
      (H : E → Submodule R B),
      Monotone H ∧ (∀ x : B, ∃ e : E, x ∈ H e) ∧
      (∀ e : E, (H e).map b = F e) ∧
      ∀ e : E,
        H e = ⨆ i : {j : E // j < e}, H i.val ∨
        ∃ p : H e →ₗ[R] (P e).complex.X 0,
          Function.Surjective p ∧
          p.ker = (⨆ i : {j : E // j < e}, H i.val).comap (H e).subtype ∧
          ∃ a : H e →ₗ[R] F e,
            (F e).subtype.comp a = b.comp (H e).subtype ∧
            ((P e).π.f 0).hom.comp p =
              ((⨆ i : {j : E // j < e}, F i.val).comap (F e).subtype).mkQ.comp a := by
  sorry

end ModuleCat
