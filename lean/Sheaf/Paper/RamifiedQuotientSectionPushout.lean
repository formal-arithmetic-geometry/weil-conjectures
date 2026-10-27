/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.Paper.ConstantScalarTowerAdjunction

/-! # The ramified finite quotient square on coefficient sections

Source: the quotient-ideal calculation in Step 1 of
`lem-pur-finite-quotient-module-balancing`.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.PurStrictScalar
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The square of actual constant-to-finite coefficient maps is a pushout on sections.
This statement concerns only rings, without a module or a tensor comparison witness.

Source: Step 1 of `lem-pur-finite-quotient-module-balancing`; Stacks Project,
Modules on Sites, lemmas `lemma-constant-exact`, `lemma-tensor-with-finitely-presented`,
and `lemma-completion-flat` (Tag 093M); and the constant quotient cone of
`def-weil-completed-integral-coefficients`.
(blueprint: lem-pur-ramified-quotient-section-pushout).

Proof: put r=n+1, A=O_E and B=O_F. Taking rth powers of the ramification
identity gives map(A→B,(t^r))=(v^(er)). The limit-lift equation identifies
constant-to-completion followed by projection with the constant quotient map.
For a constant ring sheaf, the principal quotient map is surjective on sections:
a set-theoretic section of the discrete quotient gives a section after applying
the constant sheaf functor to sets and its comparison with underlying ring sheaves.
Its kernel on sections is the principal ideal of the constant section t^r.
Indeed the same constant-set construction applies to the surjection A→(t^r),
while preservation of finite limits identifies the latter constant set with the
kernel of the quotient map. The corresponding assertion holds for B and v^(er).
The image ideal in B(U) is therefore precisely the kernel of B(U)→B_n(U),
because the discrete ramification identity writes the two generators as multiples
of one another and these identities remain true on constant sections. Thus B_n(U)
is B(U) modulo the extension of the kernel of A(U)→A_n(U). The quotient universal
property gives the pushout, with lower map the specified ramified quotient lift;
commutativity is checked on discrete representatives, then sheafified. This also
works when U is empty (all section rings are zero), n=0, or e=1. No assertion that
evaluation preserves arbitrary sheaf colimits is used. -/
theorem ramifiedQuotient_sectionPushout (W : Scheme.{u}) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e) (n : ℕ) :
    let g := integralConstantToCompletionOfUniverses l E W ≫
      (adicLisseForget W).map
        (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) W)
    let p := integralConstantToCompletionOfUniverses l F W ≫
      (adicLisseForget W).map
        (PurCompactSupport.projection l F (e * (n + 1))
          (Nat.mul_pos hepos (Nat.le_add_left 1 n)) W)
    ∀ U : W.ProEtᵒᵖ, IsPushout ((constantMap l E F i W).hom.app U)
      (CommRingCat.ofHom (show ((constants l E).ring W).obj.obj U →+*
        ((PurCompactSupport.finite l E (n + 1) (Nat.le_add_left 1 n)).ring W).obj.obj U
        from (g.hom.app U).hom))
      (CommRingCat.ofHom (show ((constants l F).ring W).obj.obj U →+*
        ((PurCompactSupport.finite l F (e * (n + 1))
          (Nat.mul_pos hepos (Nat.le_add_left 1 n))).ring W).obj.obj U
        from (p.hom.app U).hom))
      (((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
        (Nat.le_add_left 1 n)).map W).hom.app U) := by
  sorry

end WeilConjectures.PurStrictScalar
