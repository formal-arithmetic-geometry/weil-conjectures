/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Transpose of a normalized adjunction square

Source: Stacks Project, Cohomology on Sites, Tag 07A6 (lemma-adjoint), and
Categories, Tag 0037 (definition-adjoint). The square calculation is agent-written,
extracted from Steps 4–5 of lem-weil-pbc-ringed-slice-pullback-mate-normalization;
it is not a verbatim Stacks assertion.
(blueprint: lem-weil-pbc-normalized-adjunction-square-transpose)
-/

@[expose] public section

set_option autoImplicit false

universe vA vB vAv vBv vE vF vEv vFv uA uB uAv uBv uE uF uEv uFv

namespace CategoryTheory.Adjunction

/-- The transpose of the left comparison is determined by global Hom normalization,
the unit square, and the right augmentation square. All comparison transformations
are arbitrary; only the two restriction factorizations are natural isomorphisms.

Source: Stacks Project, Tag 07A6 (lemma-adjoint), normalized Hom bijections;
Tag 0037 (definition-adjoint), unit formula. Agent-written square calculation
extracted from Steps 4–5 of lem-weil-pbc-ringed-slice-pullback-mate-normalization.
(blueprint: lem-weil-pbc-normalized-adjunction-square-transpose)

Proof:
1. Apply global Hom normalization with I = F(A) and h the identity. The Hom-unit
formula of lem-weil-pbc-adjunction-of-natural-bijection gives
eta(qA(A)); R(alpha(A)) = qA(eta0(A)); iota(F(A)).
2. Expand the local transpose using the same Hom-unit formula and functoriality
of Rv. Substitute the unit-square hypothesis at X = qA(A).
3. Naturality of beta at alpha(A) moves Rv(s(alpha(A))) past beta. Combine the
first two factors using functoriality of r to obtain r of the global transpose,
followed by beta(qB(F(A))) and Rv(zeta(F(A))).
4. Substitute step 1 and then the right augmentation square at I = F(A). This
leaves r(qA(eta0(A))); rho(G(F(A))); qAv(tau(F(A))); iotaV(s0(F(A))).
5. Naturality of rho at eta0(A) replaces the first two factors by rho(A) followed
by qAv(r0(eta0(A))). Functoriality of qAv combines this with qAv(tau(F(A))),
giving the asserted equality. No inverse comparison map is used. -/
theorem normalizedAdjunctionSquare_transpose
    {A : Type uA} {B : Type uB} {Av : Type uAv} {Bv : Type uBv}
    {E : Type uE} {F : Type uF} {Ev : Type uEv} {Fv : Type uFv}
    [Category.{vA} A] [Category.{vB} B] [Category.{vAv} Av] [Category.{vBv} Bv]
    [Category.{vE} E] [Category.{vF} F] [Category.{vEv} Ev] [Category.{vFv} Fv]
    (qA : A ⥤ E) (qB : B ⥤ F) (qAv : Av ⥤ Ev) (qBv : Bv ⥤ Fv)
    (r0 : A ⥤ Av) (s0 : B ⥤ Bv) (r : E ⥤ Ev) (s : F ⥤ Fv) (Gv : Bv ⥤ Av)
    {F0 : A ⥤ B} {G0 : B ⥤ A} {L : E ⥤ F} {R : F ⥤ E}
    {Lv : Ev ⥤ Fv} {Rv : Fv ⥤ Ev}
    (adj0 : F0 ⊣ G0) (adjD : L ⊣ R) (adjV : Lv ⊣ Rv)
    (alpha : qA ⋙ L ⟶ F0 ⋙ qB) (iota : G0 ⋙ qA ⟶ qB ⋙ R)
    (iotaV : Gv ⋙ qAv ⟶ qBv ⋙ Rv) (tau : G0 ⋙ r0 ⟶ s0 ⋙ Gv)
    (theta : r ⋙ Lv ⟶ L ⋙ s) (beta : R ⋙ r ⟶ s ⋙ Rv)
    (rho : qA ⋙ r ≅ r0 ⋙ qAv) (zeta : qB ⋙ s ≅ s0 ⋙ qBv)
    (hHom : ∀ (a : A) (i : B) (h : F0.obj a ⟶ i),
      adjD.homEquiv (qA.obj a) (qB.obj i) (alpha.app a ≫ qB.map h) =
        qA.map (adj0.homEquiv a i h) ≫ iota.app i)
    (hUnit : ∀ x : E,
      adjV.unit.app (r.obj x) ≫ Rv.map (theta.app x) =
        r.map (adjD.unit.app x) ≫ beta.app (L.obj x))
    (hAugmentation : ∀ i : B,
      r.map (iota.app i) ≫ beta.app (qB.obj i) ≫ Rv.map (zeta.hom.app i) =
        rho.hom.app (G0.obj i) ≫ qAv.map (tau.app i) ≫ iotaV.app (s0.obj i))
    (a : A) :
    adjV.homEquiv (r.obj (qA.obj a)) (qBv.obj (s0.obj (F0.obj a)))
        (theta.app (qA.obj a) ≫ s.map (alpha.app a) ≫ zeta.hom.app (F0.obj a)) =
      rho.hom.app a ≫ qAv.map (r0.map (adj0.unit.app a) ≫ tau.app (F0.obj a)) ≫
        iotaV.app (s0.obj (F0.obj a)) := by
  sorry

end CategoryTheory.Adjunction
