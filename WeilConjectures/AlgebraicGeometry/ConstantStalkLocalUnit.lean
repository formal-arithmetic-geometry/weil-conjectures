/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantStalkLocalUnitFoundation

import WeilConjectures.AlgebraicGeometry.ConstantStalkLocalUnitPoint
import WeilConjectures.AlgebraicGeometry.ConstantStalkLocalUnitResultE
import WeilConjectures.AlgebraicGeometry.ConstantStalkLocalUnitResultQbar

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open WeilConjectures.CondensedModule
open scoped CategoryTheory.Obj

namespace WeilConjectures

/-- The native constant Weil stalk is the coefficient unit in degree zero, its local
Frobenius is the identity, its scalar alternating trace is one, and the coefficient-unit
coordinates commute with E → Qbar. Every associated geometric point is included by its
two defining projections, with an arbitrary embedding of F_(q^n) into k over k0.

Source: literature/blueprint/latest/blueprint/sec-zeta-weil/sk-thm-weil-final/
prop-every-iterate-trace.md, constant-sheaf clause
(blueprint: lem-zl-constant-stalk-local-unit).

Proof: by pullback uniqueness the two defining projections identify z with the lift
(x ∘ Spec ι, id) of ConstantStalkLocalUnitPoint.embeddingPoint. Its semilinear return
is lem-zl-constant-stalk-local-unit-point. For Λ = E the clauses of Result are
lem-zl-constant-stalk-local-unit-result-e (steps 1-4 below); for Λ = Qbar, with the
constant-section compatibility and the scalar-unit square, they are
lem-zl-constant-stalk-local-unit-result-qbar (steps 1-5).
(1) Apply lem-zl-condensed-point-module-comparison to the regular module. Its
multiplication comparison a tensor t ↦ a alpha_xbar(t) is precisely stalkIso.
(2) The strict structure of sk-def-sf-weil-complexes is the coefficient-unit comparison.
The unit coherence of lem-fix-condensed-pullback-coherence identifies every positive
iterate with the unit comparison for the power. Comparing the two paths in the return
square carries this arrow to e_h on the point unit.
(3) By lem-pe-point-module-pullback-equivalence the source reparametrization is e_h inverse
on that regular module, so the local return is the identity before taking sections.
The adjunction-unit description in lem-wf-condensed-fibre-comparison-coherence agrees:
Gamma(e_h) I_h = 1, without using faithfulness of terminal evaluation.
(4) Terminal sections are exact by lem-weil-point-proetale-sections-exact. The calculation
of det-pe-condensed-point-coefficients identifies the constants with E and Qbar, respectively.
Thus the evaluated complex is the regular scalar module in degree zero, with identity
operator. Homology is zero off zero and one-dimensional in zero, so LinearMap.trace is
one in degree zero and zero elsewhere, and the alternating sum is one.
(5) The coefficient maps and their adjoints commute with E → Qbar by
det-def-sfb-coefficient-change. The scalar/pullback comparison of det-prop-scalar-six-pullback
is compatible with the multiplication coordinate on the regular module, giving the displayed
square. Constant sections send a to its image in Qbar; hence the normalized scalar
coordinates and the local identity operators are compatible with coefficient extension. -/
theorem constant_stalk_local_unit
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (iota : D.extensionSubfield n hn →+* D.k)
    (_hι : iota.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k)
    (z : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left)
    (_hz₀ : z ≫ pullback.fst Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
        Spec.map (CommRingCat.ofHom iota) ≫ x.left)
    (_hzs : z ≫ (D.geometricFiber Y₀).hom = 𝟙 _) :
    ∃ h : z ≫ localPositivePower (D.geometricFrobenius Y₀).hom (n - 1) =
        localPositivePower (frobeniusPointIso D).hom (n - 1) ≫ z,
      ConstantStalkLocalUnit.Result (Profinite.continuousMapRingObj.{u} E) E
        (Profinite.continuousMapConstRingHom E) D (D.geometricFrobenius Y₀) z (n - 1) h ∧
      ConstantStalkLocalUnit.Result (Profinite.padicAlgClRingObj.{u} ell) (PadicAlgCl ell)
        (Profinite.PadicAlgCl.constRingHom ell) D (D.geometricFrobenius Y₀) z (n - 1) h ∧
      (∀ a : E,
        Γ.map (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ell E)
          (Profinite.continuousMapConstRingHom E a) =
            Profinite.PadicAlgCl.constRingHom ell (algebraMap E (PadicAlgCl ell) a)) ∧
      ConstantStalkLocalUnit.ScalarCompatible (Profinite.continuousMapRingObj.{u} E)
        (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ell E) z := by
  have hz : z = ConstantStalkLocalUnitPoint.embeddingPoint D Y₀ n hn x iota _hι := by
    apply pullback.hom_ext
    · simpa [ConstantStalkLocalUnitPoint.embeddingPoint] using _hz₀
    · simpa [ConstantStalkLocalUnitPoint.embeddingPoint] using
        (show z ≫ pullback.snd Y₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) = 𝟙 _ from by
          exact _hzs)
  subst z
  let h := ConstantStalkLocalUnitPoint.embeddingPoint_return D Y₀ n hn x iota _hι
  refine ⟨h, ?_⟩
  exact ⟨constant_stalk_result_E D ell _hEll E Y₀ n hn x iota _hι h,
    (constant_stalk_result_Qbar D ell _hEll E Y₀ n hn x iota _hι h).1,
    (constant_stalk_result_Qbar D ell _hEll E Y₀ n hn x iota _hι h).2⟩

end WeilConjectures
