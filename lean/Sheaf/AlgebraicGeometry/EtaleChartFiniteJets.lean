/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.MvPolynomial.Ideal

/-!
# Finite jets of an étale chart at a rational point

Source: Stacks Project, Tag 039M and its residue-degree remark; Tag 0AGX.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.EtaleChartTaylor

/-- Evaluation in the centered chart coordinates identifies every polynomial jet with
its stalk jet. This is a finite-level statement: it constructs no power series map.

Source: Stacks Project, etale.tex, Tag 039M and the following residue-degree remark;
more-algebra.tex, Tag 0AGX; schemes.tex, Tag 01HV.
(blueprint: lem-trf-etale-chart-rational-point-finite-jets)

Proof: Base change the étale chart to L. In its affine target put P = L[X_i] and
q = (X_i-c_i), where c_i is the structural residue of the coordinate. Evaluation
has kernel q: translation by the c_i reduces this to the constant coefficient map.
The target stalk is P_q, and the stalk map P_q -> B is flat and unramified.
Both stalks are Noetherian: P is a polynomial ring in finitely many variables over
a field, and the chart is locally of finite type over this locally Noetherian scheme.
Unramifiedness gives m_(P_q) B = m_B. The structural rationality hypothesis identifies
both residue fields with L, compatibly with the stalk map. Tag 0AGX gives the induced
isomorphism of completions. Reduction modulo the r-th powers of the maximal ideals
(the kernels of the completion projections) therefore gives P_q/q^r P_q = B/m_B^r.
Localization gives P/q^r = P_q/q^r P_q: every polynomial outside q has a nonzero
constant term after translation, and its inverse modulo q^r is the finite geometric
series. Compose these quotient isomorphisms. The centered variables also generate
the stalk maximal ideal, since they generate
that of P_q and unramifiedness gives its extension equal to m_B.
The map sends the class of a polynomial
f in the centered variables to the class of its evaluation at the centered germs,
because each map used is induced by the actual chart stalk map. For r = 0 both
quotients are the zero ring. The argument also applies with no variables. -/
theorem rational_point_finite_jets
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    {U : Scheme.{u}} (p : U ⟶ Spec (.of k)) (n : ℕ)
    (t : U ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of k))) [Etale t]
    (ht : t ≫ (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)) ↘ Spec (.of k)) = p)
    (b : (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L))) : Scheme.{u})) :
    let V : Scheme.{u} := pullback p (Spec.map (CommRingCat.ofHom (algebraMap k L)))
    let ι : L →+* V.presheaf.stalk b :=
      ((Scheme.ΓSpecIso (.of L)).inv ≫
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap k L)))).appTop ≫
          V.presheaf.germ ⊤ b trivial).hom
    let ρ := (V.residue b).hom.comp ι
    ∀ hb : Function.Bijective ρ,
    let z : Fin n → V.presheaf.stalk b := fun i ↦
      let x := V.presheaf.germ ⊤ b trivial
        ((pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≫ t).appTop
          (AffineSpace.coord (Spec (.of k)) (ULift.up i)))
      x - ι ((RingEquiv.ofBijective ρ hb).symm (V.residue b x))
    IsNoetherianRing (V.presheaf.stalk b) ∧
      Ideal.map (MvPolynomial.eval₂Hom ι z) (MvPolynomial.idealOfVars (Fin n) L) =
        IsLocalRing.maximalIdeal (V.presheaf.stalk b) ∧
      ∀ r : ℕ, ∃ e :
          (MvPolynomial (Fin n) L ⧸ MvPolynomial.idealOfVars (Fin n) L ^ r) ≃+*
            (V.presheaf.stalk b ⧸ IsLocalRing.maximalIdeal (V.presheaf.stalk b) ^ r),
        ∀ f : MvPolynomial (Fin n) L,
          e (Ideal.Quotient.mk _ f) =
            Ideal.Quotient.mk _ (MvPolynomial.eval₂ ι z f) := by sorry

end AlgebraicGeometry.EtaleChartTaylor
