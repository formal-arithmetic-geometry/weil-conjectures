/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-! # Cancelling one split top differential of a sheaf complex

Source: Stacks Project, Tag 068V, explicit split cancellation in the bounded
finite-projective specialization; the identity-pair argument of Tag 00MT.
(blueprint: lem-pc-split-top-differential-cancellation)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- One split top differential can be removed without changing homotopy type.

Source: Stacks Project, Tag 068V, explicit split cancellation; Tag 00MT,
contractible identity-pair argument.
(blueprint: lem-pc-split-top-differential-cancellation).

Proof: Let δ = B.d m (m+1) and choose a section σ with σ ≫ δ = 𝟙. Replace the term
in degree m by ker δ, retain the terms below m, and put zero in every degree above
m. Factor the incoming differential through ker δ using d squared = 0. These
maps define a cochain complex D. The inclusion ker δ into B.X m and the identity
in lower degrees define D to B. The endomorphism 𝟙 - δ ≫ σ factors through ker δ
and defines the reverse chain map, zero above m and identity below m. The two
chain-map equations at the changed degrees follow from d squared = 0 and σ ≫ δ = 𝟙.
Their composite on D is the identity. On B, the difference from the identity is
the boundary of the homotopy whose only nonzero component is σ from degree m+1
to degree m. Above m+1 all terms of B are zero by the support hypothesis, so this
homotopy proves the identity in every degree. Thus D is homotopy equivalent to B.
The kernel is a direct summand of B.X m; direct summands preserve flatness,
quasi-coherence and finite presentation (the latter by local finite presentations,
or equivalently the finite-projective criterion on affine opens). Other terms
are unchanged or zero. Since m is natural, replacing the degree m term and
removing higher degrees retains the lower bound zero. The case m = 0 removes
degree one and introduces no negative term; zero terms and the empty scheme
satisfy the same identities. No residue vanishing or affineness is required. -/
theorem exists_split_top_differential_cancellation (S : Scheme.{u})
    (B : CochainComplex S.Modules ℤ) (m : ℕ)
    (hBge : B.IsStrictlyGE 0) (hBle : B.IsStrictlyLE (m + 1 : ℕ))
    (hBflat : ∀ n : ℤ, (B.X n).IsFlatOver (𝟙 S))
    (hBqc : ∀ n : ℤ, (B.X n).IsQuasicoherent)
    (hBfp : ∀ n : ℤ, (B.X n).IsFinitePresentation)
    (hsplit : IsSplitEpi (B.d (m : ℤ) (m + 1 : ℕ))) :
    ∃ D : CochainComplex S.Modules ℤ,
      D.IsStrictlyGE 0 ∧ D.IsStrictlyLE m ∧
      (∀ n : ℤ, (D.X n).IsFlatOver (𝟙 S)) ∧
      (∀ n : ℤ, (D.X n).IsQuasicoherent) ∧
      (∀ n : ℤ, (D.X n).IsFinitePresentation) ∧
      Nonempty (HomotopyEquiv D B) := by sorry

end AlgebraicGeometry.Scheme.Modules
