/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T6
-/
module

public import Sheaf.AlgebraicGeometry.PGLLinearizedPolarization
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Gluing affine invariant quotients of a stable semistable open

Source: MFK, GIT, Chapter 1, Theorem 1.10; Alper,
arXiv:1005.2398v3, Remark 9.1.5 and Section 8.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.PGLLinearization

variable {k : Type u} [Field k]

/-- When every semistable point is stable, the affine invariant quotients glue
to a geometric quotient of the semistable open by Proj of the invariant ring.
This assertion concerns the quotient map; finite generation and projectivity
of its target are separate algebraic assertions.

Source: MFK, Chapter 1, Theorem 1.10; Alper, arXiv:1005.2398v3,
Remark 9.1.5 and Section 8
(blueprint: lem-sfb-pgl-semistable-affine-quotient-gluing).

Proof: For every positive homogeneous invariant s, the nonvanishing locus X_s
is affine of finite type by projectivePolarizationSectionAlgebra, with coordinate
ring S_(s). These opens lie in J and cover it, since J is exactly the semistable
open on geometric points. Naturality and the line linearization restrict the
action to each X_s. The invariant coordinate ring is R_(s), where R=S^G.
For injectivity use the localization equality criterion in the subring R of S.
For surjectivity, write an invariant fraction a/s^n. Its coaction defect becomes
zero after inverting s, so a power s^m kills the defect. Then s^m*a is an
invariant homogeneous numerator and a/s^n=(s^m*a)/s^(n+m). This works for zero
divisors as well. Apply affine_pgl_finite_stabilizer_quotient on X_s. Closed
orbits restrict to the invariant open and stabilizers are unchanged. Identify
the target with Spec R_(s)=D_+(s) in Proj R. The constant-map equation makes
these maps morphisms over k.

On X_(st), both quotient maps are induced by the same fraction inclusion, so
they agree and glue by Scheme.Cover.glueMorphisms. On the t-chart, the pullback
of D_+(s) is the nonvanishing locus of s^deg(t)/t^deg(s); hence the inverse image
of D_+(s) is exactly X_s. Affine surjectivity and invariance now give global
surjectivity and invariance. An invariant map to any algebraic space descends
uniquely on each D_+(s) by the affine categorical property. On D_+(st), uniqueness
for the affine quotient of X_(st) makes the descents equal. The fppf sheaf
condition, restricted to this Zariski cover, glues them uniquely. No separation
hypothesis on the target is used. Finally, a geometric point of Proj lies in
some D_+(s), and the affine theorem lifts it to X_s. Two geometric points with
equal image lie in the same X_s by the inverse-image equality, where the affine
orbit theorem supplies a group element; invariance gives the converse. Empty
semistable loci and zero localizations are included. -/
theorem semistable_affine_quotient_gluing
    (r : ℕ) (hr : 1 ≤ r) (X : Over (Spec (.of k)))
    (hprojective : IsHProjective X.hom)
    (hfiniteType : LocallyOfFiniteType X.hom ∧ QuasiCompact X.hom)
    (L : X.left.Modules) [L.IsInvertible] (hample : IsAmple X.hom L)
    (E : Action k r X L) (J : Over (Spec (.of k))) (i : J ⟶ X)
    (hopen : IsOpenImmersion i.left)
    (hss : ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
      (x : fieldTest k Ω ⟶ X),
      E.IsSemistable Ω x ↔ ∃ y : fieldTest k Ω ⟶ J, y ≫ i = x)
    (hstable : ∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
      (x : fieldTest k Ω ⟶ J), E.IsStable Ω (x ≫ i))
    (φ : k →+* E.CoefficientRing)
    (hc : ∀ c : k, E.coefficientVal (φ c) = constantSection (Z := X) (L := L) c) :
    ∃ q : J ⟶ E.projOver φ,
      Surjective q.left ∧
      (∀ (T : Over (Spec (.of k))) (g : Matrices k r T) (x y : T ⟶ J),
        y ≫ i = E.act T g (x ≫ i) → y ≫ q = x ≫ q) ∧
      (∀ (B : AlgebraicSpace (Spec (.of k))) (f : yoneda.obj J ⟶ B.obj.obj),
        E.IsInvariantMap i B f →
          ∃! a : yoneda.obj (E.projOver φ) ⟶ B.obj.obj, yoneda.map q ≫ a = f) ∧
      (∀ (Ω : Type u) [Field Ω] [Algebra k Ω] [IsAlgClosed Ω],
        Function.Surjective (fun x : fieldTest k Ω ⟶ J ↦ x ≫ q) ∧
        ∀ x y : fieldTest k Ω ⟶ J,
          (x ≫ q = y ≫ q ↔ ∃ g : Matrix.GeneralLinearGroup (Fin r) Ω,
            E.act _ (fieldMatrix Ω g) (x ≫ i) = y ≫ i)) := by
  sorry

end AlgebraicGeometry.PGLLinearization
