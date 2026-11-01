/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SixFunctors.FiniteExceptional.FiniteExceptional

/-! # Intrinsic identification of finite exceptional reduction maps

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/thm-pur-finite-reduction-of-purity.proof.md,
Step 2 and Step 4
(blueprint: lem-pur-finite-reduction-exceptional-q-identification).

The finite exceptional full-subcategory maps are compared with the intrinsic
small pro-etale operations at positive coefficient levels.  The predecessor
indices `k` and `j` represent levels `k+1` and `j+1`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Finite exceptional counits and compact-support quotient maps agree with the
intrinsic finite-reduction maps, and the finite exceptional quotient map b, read in
intrinsic coordinates, satisfies the reduced smooth counit identity.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-finite-reduction-of-purity.proof.md, Step 2 and Step 4
(blueprint: lem-pur-finite-reduction-exceptional-q-identification).
The indices `j ≤ k` are the predecessors of the node's levels `m = j+1 ≤ n = k+1`.
The finite functors F_r, G_r, Q_T are restrictions of the intrinsic compact-support,
exceptional and reduction functors through the full inclusions `domain.ι`, so the
realization isomorphisms φ_r, γ_r are identities and b' = γ⁻¹ ∘ b ∘ Q(γ) is `ι.map b`.
The fourth clause is the node's equal-index case b_{n,n} = id (up to self-reduction).
Proof:
1. Reduction preserves the finite-Tor constructible domains by bounded flat models
(lem-sf-flat-model, lem-sf-reduction-flat-model); by def-sf-finite-exceptional-constructions
F_r, G_r, Q_T are restrictions of the intrinsic functors, so every map has the stated
source and target.
2. lem-route-finite-reduction-exceptional-finite-model-counit-normalization identifies
the transported finite counit with `smoothExceptionalCounit` (def-pur-smooth-trace),
with no inserted isomorphism: first clause.
3. lem-route-finite-reduction-exceptional-finite-model-support-mate identifies the
proper/open tensor comparison with the coefficient mate and its finite-Tor restriction
with q. By def-pur-finite-reduction-comparisons q' is the scalar adjunct of
ρ ∘ F'(u_K); lem-coef-compact-support-coefficient-mate-normalization at N = Q_X K,
s = u_K gives Res_Y(γ_K) ∘ u = ρ ∘ F'(u_K), and injectivity of the scalar Hom
bijection gives q' = γ = q: second clause.
4. The counit equation of lem-coef-finite-exceptional, rewritten with Steps 2 and 3,
is the third clause. Identity quotients give the equal-index clause, including zero
objects and empty schemes. -/
theorem finiteReductionExceptionalQIdentification
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : IntermediateField (Padic C.l) C.Qbar)
    [FiniteDimensional (Padic C.l) E]
    (j k : ℕ) (h : j ≤ k) {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    (∀ (L : (FiniteExceptional.domain C.l E Y k).FullSubcategory),
      (FiniteExceptional.domain C.l E Y k).ι.map
          ((FiniteExceptional.adjunction C.l E D C.different f
            (@HasCompactification.compactification X Y f
              (hasCompactification_of_finiteType_over_field D.k X Y f)) k).counit.app L) =
      ({ field := D, coefficients := C, extension := E,
          level := k + 1, level_pos := Nat.succ_pos k } :
        PurityFiniteSetting.{u}).smoothExceptionalCounit f L.obj) ∧
    (∀ (K : (FiniteExceptional.domain C.l E X k).FullSubcategory),
      (FiniteExceptional.domain C.l E Y j).ι.map
          ((FiniteExceptional.q C.l E D C.different f
            (@HasCompactification.compactification X Y f
              (hasCompactification_of_finiteType_over_field D.k X Y f)) h).hom.app K) =
      ({ field := D, coefficients := C, extension := E,
          level := k + 1, level_pos := Nat.succ_pos k } :
        PurityFiniteSetting.{u}).finiteReductionCompactSupportComparison
        (j + 1) (Nat.succ_pos j) (Nat.succ_le_succ h) f K.obj) ∧
    (∀ (L : (FiniteExceptional.domain C.l E Y k).FullSubcategory),
      ({ field := D, coefficients := C, extension := E,
          level := k + 1, level_pos := Nat.succ_pos k } :
        PurityFiniteSetting.{u}).finiteReductionCompactSupportComparison
          (j + 1) (Nat.succ_pos j) (Nat.succ_le_succ h) f
          ((({ field := D, coefficients := C, extension := E,
               level := k + 1, level_pos := Nat.succ_pos k } :
            PurityFiniteSetting.{u}).compositionExceptional f).obj L.obj) ≫
        ((({ field := D, coefficients := C, extension := E,
             level := k + 1, level_pos := Nat.succ_pos k } :
          PurityFiniteSetting.{u}).finiteReductionSetting (j + 1)
            (Nat.succ_pos j)).smoothCompactSupport f).map
          ((FiniteExceptional.domain C.l E X j).ι.map
            ((FiniteExceptional.b C.l E D C.different f
              (@HasCompactification.compactification X Y f
                (hasCompactification_of_finiteType_over_field D.k X Y f)) h).app L)) ≫
        (({ field := D, coefficients := C, extension := E,
            level := k + 1, level_pos := Nat.succ_pos k } :
          PurityFiniteSetting.{u}).finiteReductionSetting (j + 1)
            (Nat.succ_pos j)).smoothExceptionalCounit f
          ((({ field := D, coefficients := C, extension := E,
               level := k + 1, level_pos := Nat.succ_pos k } :
            PurityFiniteSetting.{u}).finiteReduction (j + 1) (Nat.succ_pos j)
              (Nat.succ_le_succ h) Y).obj L.obj) =
      (({ field := D, coefficients := C, extension := E,
          level := k + 1, level_pos := Nat.succ_pos k } :
        PurityFiniteSetting.{u}).finiteReduction (j + 1) (Nat.succ_pos j)
          (Nat.succ_le_succ h) Y).map
        (({ field := D, coefficients := C, extension := E,
            level := k + 1, level_pos := Nat.succ_pos k } :
          PurityFiniteSetting.{u}).smoothExceptionalCounit f L.obj)) ∧
    (∀ (L : (FiniteExceptional.domain C.l E Y k).FullSubcategory),
      ((FiniteExceptional.b C.l E D C.different f
        (@HasCompactification.compactification X Y f
          (hasCompactification_of_finiteType_over_field D.k X Y f)) (le_refl k)).app L) ≫
          (FiniteExceptional.G C.l E D C.different f
            (@HasCompactification.compactification X Y f
              (hasCompactification_of_finiteType_over_field D.k X Y f)) k).map
            ((FiniteExceptional.selfReduction C.l E Y k).hom.app L) =
        (FiniteExceptional.selfReduction C.l E X k).hom.app
          ((FiniteExceptional.G C.l E D C.different f
            (@HasCompactification.compactification X Y f
              (hasCompactification_of_finiteType_over_field D.k X Y f)) k).obj L)) := by
  sorry

end WeilConjectures.PurityFiniteSetting
