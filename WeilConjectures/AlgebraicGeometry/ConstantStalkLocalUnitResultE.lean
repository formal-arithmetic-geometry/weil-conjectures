/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantStalkLocalUnitFoundation
public import WeilConjectures.AlgebraicGeometry.ConstantStalkLocalUnitPoint

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open WeilConjectures.CondensedModule
open scoped CategoryTheory.Obj
namespace WeilConjectures

/-- The finite coefficient case Λ = E (continuous-function condensed ring) of the native
constant stalk calculation at the embedded geometric point.
Source: literature/blueprint/latest/blueprint/sec-zeta-weil/sk-thm-weil-final/
prop-every-iterate-trace.md, constant-sheaf clause
(blueprint: lem-zl-constant-stalk-local-unit-result-e).
Proof: (1) Apply lem-zl-condensed-point-module-comparison to the regular module at x̄. Its
multiplication comparison a ⊗ t ↦ a α_x̄(t) is precisely stalkIso.
(2) The strict structure τ₀ = unitWeilModule.str of sk-def-sf-weil-complexes is the
coefficient-unit comparison e_g. The unit equation e_f P_f(e_g) c_{f,g} = e_{gf} of
lem-fix-condensed-pullback-coherence identifies nativeIterate with e_{g^n}; comparing the two
paths of the return square (hypothesis h) carries it to e_h, h = σ^n, on the point unit.
(3) By lem-pe-point-module-pullback-equivalence the point reparametrization of nativeReturn
is e_h⁻¹ on the regular module, so the conjugated local operator is the identity; the
adjunction-unit form of lem-wf-condensed-fibre-comparison-coherence agrees (Γ(e_h) I_h = 1).
(4) Terminal sections are exact over the separably closed point
(lem-weil-point-proetale-sections-exact, nativeSections_colimits), and
det-pe-condensed-point-coefficients identifies Γ of the point unit with Λ(*); the constant
section 1 is a basis, so b with b.inv = constantSection exists. The evaluated complex is
Λ[0] with identity operator: homology is one-dimensional in degree 0 and zero elsewhere,
the traces are 1 and 0, and the alternating finsum is 1.
Here Λ(*) = C(*, E) = E by def-sfb-padic-subfield-condensed-ring. -/
theorem constant_stalk_result_E
    (D : FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime] (_hEll : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom] (n : ℕ) (hn : 1 ≤ n) (x : D.extensionPoints Y₀ n hn)
    (iota : D.extensionSubfield n hn →+* D.k)
    (_hι : iota.comp (D.extensionEmbedding n hn) = algebraMap D.k₀ D.k)
    (h : ConstantStalkLocalUnitPoint.embeddingPoint D Y₀ n hn x iota _hι ≫
        localPositivePower (D.geometricFrobenius Y₀).hom (n - 1) =
      localPositivePower (frobeniusPointIso D).hom (n - 1) ≫
        ConstantStalkLocalUnitPoint.embeddingPoint D Y₀ n hn x iota _hι) :
    ConstantStalkLocalUnit.Result (Profinite.continuousMapRingObj.{u} E) E
      (Profinite.continuousMapConstRingHom E) D (D.geometricFrobenius Y₀)
      (ConstantStalkLocalUnitPoint.embeddingPoint D Y₀ n hn x iota _hι) (n - 1) h := by
  sorry

end WeilConjectures
