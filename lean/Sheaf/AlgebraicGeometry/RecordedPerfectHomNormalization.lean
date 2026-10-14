/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.RecordedPerfectHomTransport
public import Sheaf.AlgebraicGeometry.PerfectHomTransport

/-! # Change of the counit normalization in perfect Hom transport

Source: Stacks Project, Cohomology, Tags 06YJ and 0D5S.
(blueprint: lem-pc-recorded-perfect-hom-normalization).
-/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]


/-- Two composition systems for the same derived pullbacks differ by conjugation
with the universal change-of-counit automorphisms of the direct pullbacks.
No perfectness, finite presentation or filtered diagram is involved.
Source: Stacks Project, Cohomology, Tags 06YJ and 0D5S; uniqueness of the
left-derived universal functor and its composition comparison.
(blueprint: lem-pc-recorded-perfect-hom-normalization).

Proof: write ε₀ for the counits selected with the old composition family and ε₁
for the retained original counits. For every arrow p use leftDerivedUnique to
construct e_p with Qh(e_p.hom) followed by ε₀(p) equal to ε₁(p). Its inverse
satisfies the inverse equation by cancellation. Substitute these equations into
the defining composite-counit expressions for both composition lifts. Naturality
of e_f at ε₀(g) and the functor associators identifies the two expressions.
The left-derived uniqueness property implies
c₁(f,g) = (e_g whiskered by Lf) followed by (Lg whiskered by e_f), then
c₀(f,g), then e_(fg) inverse. Transport through baseChangeMap_fst gives the
corresponding formula for the inverse composition comparison. In its conjugation
on Hom, the two components of e_(baseChangeMap) cancel by naturality at a.
The remaining expression is exactly the equation below. Equality transport is
compatible with e by equality induction. Zero objects and identity arrows use the
same cancellation; no representatives or arbitrary geometric witnesses are chosen. -/
theorem exists_recordedPerfectHom_normalization :
    ∃ e : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), derivedPullback f ≅ derivedPullback f,
      ∀ {X S : Scheme.{u}} (s : X ⟶ S) {T T' : Over S} (g : T' ⟶ T)
        (P Q : schemeDerivedCategory X)
        (a : (derivedPullback (pullback.fst s T.hom)).obj P ⟶
          (derivedPullback (pullback.fst s T.hom)).obj Q),
        recordedPerfectHomMap s g a =
          (e (pullback.fst s T'.hom)).hom.app P ≫
            perfectHomMap s g ((e (pullback.fst s T.hom)).inv.app P ≫ a ≫
              (e (pullback.fst s T.hom)).hom.app Q) ≫
                (e (pullback.fst s T'.hom)).inv.app Q := by sorry

end AlgebraicGeometry
