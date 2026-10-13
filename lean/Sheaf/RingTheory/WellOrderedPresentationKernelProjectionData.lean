/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
public import Mathlib.Order.RelClasses
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Partial sums and kernel projections for a well-ordered presentation

Source: Stacks Project, Algebra, Lemma 0D1U, successor argument, with the
projective presentations supplied by the quotient resolutions in place of free modules.
(blueprint: lem-weil-pbc-well-ordered-presentation-kernel-projection-data).
-/

@[expose] public section

universe u v w

namespace ModuleCat

open CategoryTheory CategoryTheory.Limits

/-- Partial-sum presentation with the surjective kernel projections, before taking quotients.
Source: Stacks Project, Algebra, Lemma 0D1U, successor construction.
(blueprint: lem-weil-pbc-well-ordered-presentation-kernel-projection-data).

Proof: write U_e for the predecessor supremum of F and Q_e for F_e/U_e.
Call e active if Q_e is nonzero. Choose an element of F_e outside U_e for each
active e. These elements are distinct, since the earlier one lies in the later
predecessor supremum. Thus the active indices inject into M and can be shrunk
to universe v. For each active e lift the supplied degree-zero augmentation
P(e)_0 → Q_e to F_e using categorical projectivity and the quotient epimorphism.
Let B be the direct sum of these degree-zero objects over the shrunk index set,
and let b : B → M be the sum of the lifts followed by inclusions. Define H_e
as the submodule of vectors supported on active indices at most e.

Well-founded induction shows b(H_e)=F_e: lift the class in Q_e at an active
stage and subtract it; the remainder lies in U_e. The nonempty predecessor
chain has supremum equal to its union, so induction lifts this remainder from
an earlier partial sum. At a least stage the remainder is zero. At an inactive
stage F_e=U_e. Exhaustion of F now makes b surjective. B is categorically
projective: lift a map on each projective summand through an epimorphism and
sum the lifts. Let S be the short exact kernel complex of b with S.X₃=M.
The H_e are monotone and exhaustive by finite support and the existence of a
largest index in any nonempty finite support. For empty support choose an index
using hcover at zero.

Pull H_e back along the kernel inclusion S.f to obtain K_e. At an active e,
projection to the e summand restricts to a linear map from K_e to the linear
augmentation kernel, then to the categorical kernel through their canonical
isomorphism. It is surjective: a vector killed by the augmentation has lifted
image in U_e; lift that image from the predecessor partial sum and subtract.
Its kernel consists exactly of vectors supported strictly before e. Finite
support identifies these with the predecessor supremum of K_i, pulled back
along K_e.subtype. At an inactive e no summand was added, so this predecessor
submodule is top. These are precisely the alternatives asserted below.
Repeated stages are inactive; at a least active stage the predecessor is zero.
The construction uses categorical projectivity in universe v throughout and
needs no size assumption on R. No object is defined by selecting a witness
from this unfinished existence proof. -/
theorem exists_projective_presentation_kernel_projection_data
    {R : Type u} [CommRing R] (M : ModuleCat.{v} R)
    {E : Type w} [LinearOrder E] [IsWellOrder E (· < ·)]
    (F : E → Submodule R M) (hF : Monotone F)
    (hcover : ∀ x : M, ∃ e : E, x ∈ F e)
    (P : ∀ e : E, ProjectiveResolution
      (ModuleCat.of R ((F e) ⧸
        ((⨆ i : {j : E // j < e}, F i.val).comap (F e).subtype)))) :
    ∃ S : ShortComplex (ModuleCat.{v} R), S.X₃ = M ∧ S.ShortExact ∧
      Projective S.X₂ ∧ ∃ H : E → Submodule R S.X₂,
        Monotone H ∧ (∀ x : S.X₂, ∃ e : E, x ∈ H e) ∧
        ∀ e : E,
          let K : E → Submodule R S.X₁ := fun i ↦ (H i).comap S.f.hom
          let U := (⨆ i : {j : E // j < e}, K i.val).comap (K e).subtype
          U = ⊤ ∨ ∃ q : K e →ₗ[R] (kernel ((P e).π.f 0) : ModuleCat.{v} R),
            Function.Surjective q ∧ q.ker = U := by sorry

end ModuleCat
