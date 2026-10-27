/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T6
-/
module

public import Sheaf.AlgebraicGeometry.PGLLinearizedPolarization
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # Restricting a linearized action to an invariant scheme-theoretic image

Source: MFK, GIT, Chapter 1, Theorem 1.10 and Appendix 1.C; Alper,
arXiv:1005.2398v3, Remark 9.1.5 and Lemma 9.2.5(3).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.PGLLinearization

variable {k : Type u} [Field k]

/-- The action and line linearization restrict to the scheme-theoretic image
of a quasi-compact invariant subscheme. For a projective polarization, its
semistable geometric points are precisely those semistable in the ambient scheme.

Source: MFK, Chapter 1, Theorem 1.10 and Appendix 1.C; Alper,
arXiv:1005.2398v3, Remark 9.1.5 and Lemma 9.2.5(3)
(blueprint: lem-sfb-pgl-invariant-image-restriction).

Proof: Write X for the scheme-theoretic image and i for its closed immersion
into Z. The equality of kernel ideals identifies this closed subscheme
with the scheme-theoretic image of j. The map J -> X is quasi-compact and
schematically dominant. GL_r is
flat over k, so J times GL_r is schematically dominant in X times GL_r by
lemma-nagata-dense-flat-pullback. Invariance of J implies that the pullback of
the ideal of X by the universal action vanishes on J times GL_r. Density makes
it vanish on X times GL_r. The closed-immersion universal property therefore
factors the action through X. Its identities follow by cancellation of i;
the line isomorphisms are the original ones conjugated by pullbackComp, so
pullback associativity transfers their cocycle and naturality identities.
Scalars act trivially on both the scheme and line.

An invariant ambient section restricts to an invariant section on X, giving
one implication for semistability. Conversely, take a positive-degree invariant
section b on X nonzero at a geometric point. Projective polarization section
algebra gives eventual surjectivity of restriction of sections. Choose a>0
so that b^a has degree beyond this threshold. The equivariant surjection
of finite-dimensional section spaces induces a surjection of their symmetric
algebras. PGL power lifting produces an invariant polynomial lifting a positive
power of b^a. Equivariant multiplication of sections gives an invariant section
on Z restricting to that power, still nonzero at the point. This proves the
other implication. The argument allows empty and nonreduced schemes and uses
power lifting rather than exactness of invariants in positive characteristic. -/
theorem invariant_image_restriction
    (r : ℕ) (hr : 1 ≤ r) (Z : Over (Spec (.of k)))
    (hprojective : IsHProjective Z.hom)
    (hfiniteType : LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom)
    (L : Z.left.Modules) [L.IsInvertible] (hample : IsAmple Z.hom L)
    (D : Action k r Z L) (J : Over (Spec (.of k))) (j : J ⟶ Z)
    (hqc : QuasiCompact j.left) (hinvariant : D.IsInvariantSubscheme j)
    (X : Over (Spec (.of k))) (i : X ⟶ Z) (hclosed : IsClosedImmersion i.left)
    (himage : i.left.ker = j.left.ker) :
    ∃ E : Action k r X ((Scheme.Modules.pullback i.left).obj L),
      D.IsRestriction i E ∧
      ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
        (x : fieldTest k Ω ⟶ X),
        E.IsSemistable Ω x ↔ D.IsSemistable Ω (x ≫ i) := by
  sorry

end AlgebraicGeometry.PGLLinearization
