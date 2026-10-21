/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import WeilConjectures.RingTheory.ProEtale.ClosedLiftMap
public import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.RingTheory.ProEtale.ClosedLiftAdjunction
import WeilConjectures.RingTheory.HenselianOfEtaleSectionLifting

/-! # Henselianity of the ind-etale closed lift

Source: Bhatt--Scholze, The pro-etale topology for schemes, Definition 2.2.10,
Lemma 2.2.12 and the proof of Lemma 6.1.2; Stacks Project, Tags 097P and 09XI
(blueprint: lem-zl-henselian-indetale-closed-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Algebra.ClosedLift

-- Use the adjunction formula to express its existence and uniqueness before quotienting.
private theorem lift_unique
    (A Cbar D : Type u) [CommRing A] [CommRing Cbar] [CommRing D] (I : Ideal A)
    [Algebra A Cbar] [Algebra (A ⧸ I) Cbar] [IsScalarTower A (A ⧸ I) Cbar]
    [Algebra.IndEtale (A ⧸ I) Cbar] [Algebra A D] [Algebra.IndEtale A D]
    (q : D →ₐ[A] Cbar) :
    ∃! f : D →ₐ[A] ClosedLift A Cbar, (toAlgHom A Cbar).comp f = q := by
  obtain ⟨β, hβ⟩ := exists_natural_homEquiv A I
  let : Algebra (A ⧸ I) (D ⧸ I.map (algebraMap A D)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let qbar : D ⧸ I.map (algebraMap A D) →ₐ[A ⧸ I] Cbar :=
    { __ := Ideal.Quotient.lift _ q.toRingHom (by
        change I.map (algebraMap A D) ≤ RingHom.ker q.toRingHom
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        change q (algebraMap A D a) = 0
        rw [q.commutes, IsScalarTower.algebraMap_apply A (A ⧸ I) Cbar,
          Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero])
      commutes' := by
        intro a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact (q.commutes a).trans (IsScalarTower.algebraMap_apply A (A ⧸ I) Cbar a) }
  let e := β (CommAlgCat.of A D) (CommAlgCat.of A Cbar)
  have he (f : D →ₐ[A] ClosedLift A Cbar) (d : D) :
      e f (Ideal.Quotient.mk _ d) = toAlgHom A Cbar (f d) :=
    (hβ (CommAlgCat.of A D) (CommAlgCat.of A Cbar)).2.1 f d
  obtain ⟨f, hf⟩ := e.surjective qbar
  have hq : (toAlgHom A Cbar).comp f = q := by
    ext d
    exact (he f d).symm.trans (DFunLike.congr_fun hf (Ideal.Quotient.mk _ d))
  refine ⟨f, hq, ?_⟩
  intro g hg
  apply e.injective
  ext d
  obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
  rw [he, he]
  exact DFunLike.congr_fun (hg.trans hq.symm) d

/-- The specified closed lift of an ind-etale quotient algebra is henselian along the
extended ideal. The compatible `A`-algebra structure is the one induced from `A ⧸ I`.
Source: Bhatt--Scholze, Definition 2.2.10, Lemma 2.2.12 and proof of Lemma 6.1.2;
Stacks Project, Tags 097P and 09XI
(blueprint: lem-zl-henselian-indetale-closed-lift).

Proof plan:
1. Put `C = ClosedLift A Cbar`, `J = I.map (algebraMap A C)`, and let `rho` be the
quotient map. By lem-exc-closed-lift-filtered, the defining colimit is filtered, so
C is ind-etale over A. By lem-exc-closed-lift-reduction the specified reduction
`theta : C/J -> Cbar` is an isomorphism with `theta rho = toAlgHom A Cbar`.
2. For an etale C-algebra E and a C-algebra map `sigma : E -> C/J`, E is finitely
presented by lem-weil-pbc-etale-algebra-finite-presentation-localization, hence is
ind-etale over C via its constant presentation. Composition stability in
lem-weil-pbc-ind-etale-stability makes E ind-etale over A.
3. Set `q = theta sigma`. It kills IE, so it descends to an A/I-algebra map
`E/IE -> Cbar`. Surjectivity of lem-exc-closed-lift-adjunction gives an A-algebra
map `tau : E -> C` satisfying `toAlgHom A Cbar tau = q`, by its formula on classes.
4. Injectivity of that same adjunction, now with source C, shows `tau u = id`:
both maps have the same composite with `toAlgHom A Cbar`. Thus tau is C-linear.
Since theta is injective, `theta rho tau = q = theta sigma` gives `rho tau = sigma`.
5. Every etale section therefore lifts. Apply
lem-weil-pbc-etale-section-lifting-henselian-pair with ring C and ideal J.
It gives the henselian pair, equivalently unique lifting of idempotents in every
finite C-algebra modulo J. No finiteness or completeness assumption on A or I is used. -/
theorem henselianRing
    (A Cbar : Type u) [CommRing A] [CommRing Cbar] (I : Ideal A)
    [Algebra A Cbar] [Algebra (A ⧸ I) Cbar] [IsScalarTower A (A ⧸ I) Cbar]
    [Algebra.IndEtale (A ⧸ I) Cbar] :
    HenselianRing (Algebra.ClosedLift A Cbar)
      (I.map (algebraMap A (Algebra.ClosedLift A Cbar))) := by
  let C := ClosedLift A Cbar
  let J := I.map (algebraMap A C)
  have h (E : Type u) [CommRing E] [Algebra C E] [Algebra.Etale C E]
      (σ : E →ₐ[C] C ⧸ J) :
      ∃ τ : E →ₐ[C] C, (Ideal.Quotient.mkₐ C J).comp τ = σ := by
    let : Algebra A E := ((algebraMap C E).comp (algebraMap A C)).toAlgebra
    have : IsScalarTower A C E := IsScalarTower.of_algebraMap_eq' rfl
    have : Algebra.IndEtale C E := by
      rw [Algebra.IndEtale.iff_ind_etale]
      exact CategoryTheory.ObjectProperty.le_ind _ _ (inferInstance : Algebra.Etale C E)
    have : Algebra.IndEtale A E := Algebra.IndEtale.trans A C E
    let θ : C ⧸ J →ₐ[A] Cbar :=
      { __ := reduction A Cbar I
        commutes' a := (toAlgHom A Cbar).commutes a }
    let q : E →ₐ[A] Cbar := θ.comp (σ.restrictScalars A)
    obtain ⟨τ, hτ, -⟩ := lift_unique A Cbar E I q
    have hbase : τ.comp (IsScalarTower.toAlgHom A C E) = AlgHom.id A C := by
      obtain ⟨f, -, hu⟩ := lift_unique A Cbar C I (toAlgHom A Cbar)
      apply (hu _ ?_).trans (hu _ (AlgHom.comp_id _)).symm
      ext c
      change toAlgHom A Cbar (τ (algebraMap C E c)) = toAlgHom A Cbar c
      rw [← AlgHom.comp_apply, hτ]
      change θ (σ (algebraMap C E c)) = _
      rw [σ.commutes]
      rfl
    let τC : E →ₐ[C] C :=
      { __ := τ.toRingHom
        commutes' c := DFunLike.congr_fun hbase c }
    refine ⟨τC, ?_⟩
    ext e
    apply (bijective_reduction A Cbar I).1
    change toAlgHom A Cbar (τ e) = θ (σ e)
    exact DFunLike.congr_fun hτ e
  exact (henselianRing_of_etale_section_lifting.{u, u} C J h).2.1

end Algebra.ClosedLift
