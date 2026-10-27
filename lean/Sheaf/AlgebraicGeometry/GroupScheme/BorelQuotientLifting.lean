/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.Borel
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Lifting Borel subgroups along quotients

Source: Milne, Algebraic Groups (2017), Proposition 17.20, printed pp.357–358,
and Theorem 5.39 with Remark 5.40, printed p.108.
(blueprint: lem-sfb-borel-quotient-lifting)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Every Borel subgroup of a faithfully flat quotient lifts to a Borel subgroup,
and the restricted quotient is faithfully flat and finitely presented.
Source: Milne, Proposition 17.20, printed pp.357–358; Theorem 5.39 and
Remark 5.40, printed p.108. (blueprint: lem-sfb-borel-quotient-lifting)

Proof plan: apply `lem-sfb-quotient-borel-torus-images` to obtain a Borel `B`
whose scheme-theoretic image is the prescribed `C`, with faithfully flat map
`r : B ⟶ C`. Apply `lem-sfb-algebraic-group-homomorphism-factorization` to `r`.
Both groups are affine of finite type; their diagonals are closed immersions,
because the multiplication map on their coordinate rings is surjective
(`def-weil-closed-immersion`, `def-weil-proper-morphism`). The factorization is
a faithfully flat finitely presented map followed by a closed immersion
`Spec (A/J) ⟶ Spec A`. Faithful flatness of `A ⟶ S` implies injectivity:
tensor `aA ↪ A` with `S` when `a` maps to zero; flatness makes the resulting
zero map injective, and detection of zero modules gives `aA = 0`. Thus `J = 0`,
the closed immersion is an isomorphism, and `r` is locally of finite presentation,
quasi-compact and quasi-separated. No condition on the kernel is used. -/
theorem exists_borelGroupScheme_lift {F : Type u} [Field F] [IsAlgClosed F]
    (G H : Over (Spec (.of F))) [GrpObj G] [GrpObj H]
    [IsAffine G.left] [IsAffine H.left]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [LocallyOfFiniteType H.hom] [QuasiCompact H.hom]
    [Smooth G.hom] [ConnectedSpace G.left] [Smooth H.hom] [ConnectedSpace H.left]
    (q : G ⟶ H) [IsMonHom q] (hq : q.left.appTop.hom.FaithfullyFlat)
    (C : Over (Spec (.of F))) [GrpObj C] (iC : C ⟶ H) (hC : IsBorelGroupScheme iC) :
    ∃ (B : Over (Spec (.of F))) (_ : GrpObj B) (iB : B ⟶ G),
      IsBorelGroupScheme iB ∧ ∃ r : B ⟶ C,
        IsMonHom r ∧ iB ≫ q = r ≫ iC ∧ r.left.appTop.hom.FaithfullyFlat ∧
          LocallyOfFinitePresentation r.left ∧ QuasiCompact r.left ∧ QuasiSeparated r.left := by
  sorry

end AlgebraicGeometry
