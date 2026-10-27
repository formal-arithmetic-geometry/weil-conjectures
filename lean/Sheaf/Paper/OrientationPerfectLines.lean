/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H9
-/
module

public import Sheaf.Paper.SixFunctorOrientation
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Sheaf.Paper.CoefficientEvaluationNaturality

/-! # Invertibility of the orientation's shifted coefficient lines

Source: blueprint sk-thm-sf-dual-perfect, proof Steps 1--3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The geometric line criterion: both objects lie in the finite-Tor domain,
and the source is invertible for its recorded tensor. The isomorphism fixes the
source and target; its value imposes no further condition on invertibility.
Source: blueprint sk-thm-sf-dual-perfect, proof Steps 1--3
(blueprint: lem-sf-orientation-perfect-lines). -/
def SfOrientationLineOnDomain
    {B : Type*} [Category B] {P : ObjectProperty B}
    {Q : ObjectProperty (Bᵒᵖ × B)} {H : Q.FullSubcategory ⥤ B}
    (M : SixFunctorClosedDomain P Q H) {L W : B} (_gamma : L ≅ W) : Prop :=
  ∃ (hL : P L) (_hW : P W),
    @IsInvertible _ _ M.closed.monoidal (⟨L, hL⟩ : P.FullSubcategory)

private theorem sf_line_on_domain_transport
    {B : Type*} [Category B] {P : ObjectProperty B}
    {Q : ObjectProperty (Bᵒᵖ × B)} {H : Q.FullSubcategory ⥤ B}
    (M : SixFunctorClosedDomain P Q H)
    (hp : ∀ {A A' : B}, (A ≅ A') → P A → P A')
    {L W T : B} (gamma : L ≅ W) (e : L ≅ T)
    (ht : SfCoefficientTwistEvaluation M T) : SfOrientationLineOnDomain M gamma := by
  let _ := M.closed.monoidal
  obtain ⟨hT, hi, _⟩ := ht
  have hL := hp e.symm hT
  have hW := hp gamma hL
  let e' : (⟨L, hL⟩ : P.FullSubcategory) ≅ ⟨T, hT⟩ := ObjectProperty.isoMk P e
  obtain ⟨I, ⟨a⟩, ⟨b⟩⟩ := hi
  refine ⟨hL, hW, I, ⟨?_, ?_⟩⟩
  · exact ⟨M.closed.tensor.mapIso (Iso.prod e' (Iso.refl I)) ≪≫ a⟩
  · exact ⟨M.closed.tensor.mapIso (Iso.prod (Iso.refl I) e') ≪≫ b⟩

private theorem sf_finite_domain_iso
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {m : ℕ}
    (S : SixFunctorDatum D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m)))
    (X : SixFunctorSpace D) {A B : sixFunctorFiniteCategory D C E (m + 1)
      (Nat.succ_le_succ (Nat.zero_le m)) X} (e : A ≅ B)
    (hA : S.toSixFunctorOperationDatum.finiteTorDomain X A) :
    S.toSixFunctorOperationDatum.finiteTorDomain X B := by
  refine ⟨B.property, ?_⟩
  obtain ⟨a, b, hab, ht⟩ := hA.2
  refine ⟨a, b, hab, ?_⟩
  intro L P hL
  apply ht L P
  obtain ⟨hL⟩ := hL
  exact ⟨hL ≪≫ ((intrinsicFiniteTorsionConstructible C.l E (m + 1)
    (Nat.succ_le_succ (Nat.zero_le m)) X.obj.left).ι.mapIso e).symm⟩

private theorem sf_integral_domain_iso
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {m : ℕ}
    (S : SixFunctorDatum D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m)))
    (X : SixFunctorSpace D) {A B : sfIntegralConstructibleCategory C.l E X.obj.left}
    (e : A ≅ B) (hA : S.toSixFunctorOperationDatum.integralFiniteTorDomain X A) :
    S.toSixFunctorOperationDatum.integralFiniteTorDomain X B := by
  refine ⟨B.property, ?_⟩
  obtain ⟨a, b, hab, ht⟩ := hA.2
  refine ⟨a, b, hab, fun n ↦ ⟨(ht n).1, ?_⟩⟩
  intro L P hL
  apply (ht n).2 L P
  obtain ⟨hL⟩ := hL
  exact ⟨hL ≪≫ ((scalarReductionDerivedExtension C.l E X.obj.left n).mapIso
    ((sfIntegralConstructible C.l E X.obj.left).ι.mapIso e)).symm⟩

/-- The shifted coefficient line and its exceptional image lie in the actual
finite-Tor domains, and the source line is invertible in each recorded tensor.
This concerns the line only, independently of perfect K, theta, biduality or the
anti-equivalence.
Source: blueprint sk-thm-sf-dual-perfect, proof Steps 1--3
(blueprint: lem-sf-orientation-perfect-lines).

Proof: At integral coefficients, the single-functor shift isomorphism identifies
sfOrientationIntegralLine with the signed Tate coefficient shifted by 2d.
The coefficient evaluation theorem at (m,t)=(d,2d) supplies its finite-Tor
membership and tensor inverse. Transport both along that shift isomorphism.
At finite coefficients apply the recorded integral reduction to this same
isomorphism and use the finite shifted-line clause of coefficient evaluation.
At rational coefficients apply localization and its shift comparison; at common
coefficients apply the base-stage inclusion and its shift comparison. These give
the corresponding shifted-line clauses and preserve the two tensor contractions.
Membership is invariant under isomorphism. Finally each displayed orientation
is an isomorphism, so the exceptional target belongs to the same domain as the
source. All transports use full-subcategory lifts of these actual maps. -/
theorem sfOrientationPerfectLines
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum} {E : Type u}
    [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E] {m : ℕ}
    {S : SixFunctorDatum D C E (m + 1) (Nat.succ_le_succ (Nat.zero_le m))}
    (O : SfOrientationDatum S) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] (d : ℕ) [SmoothOfRelativeDimension d f.hom.left]
    (c : Compactification f.hom.left) :
    SfOrientationLineOnDomain (S.finiteClosed X) (SixFunctorOrientation O f d c) ∧
    SfOrientationLineOnDomain (S.integralClosed X)
      (SixFunctorOrientation.integralComponent O f d c) ∧
    SfOrientationLineOnDomain (S.rationalClosed X)
      (SixFunctorOrientation.rationalComponent O f d c) ∧
    SfOrientationLineOnDomain (S.commonClosed X)
      (SixFunctorOrientation.commonComponent O f d c) := by
  let _ := dlAdicGeometricResidueInvertible D C X.obj.left
  obtain ⟨_, _, _, _, hf, hi, hr, hc⟩ := sfCoefficientEvaluationNaturality S X
  let e : sfOrientationIntegralLineOn D C E X d ≅
      sfEvaluationIntegralLine D C E X (d : ℤ) (2 * (d : ℤ)) :=
    ObjectProperty.isoMk _ (sfOrientationIntegralShiftIso C.l E X.obj.left d ≪≫
      (((sfIntegralConstructible C.l E X.obj.left).ι.commShiftIso
        (2 * (d : ℤ))).app (sfIntegralTwistingCoefficient C.l E X.obj.left d)).symm)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact sf_line_on_domain_transport (S.finiteClosed X) (sf_finite_domain_iso S X)
      (SixFunctorOrientation O f d c)
      ((sixFunctorIntegralReduction D C E m X).mapIso e) (hf _ _)
  · exact sf_line_on_domain_transport (S.integralClosed X) (sf_integral_domain_iso S X)
      (SixFunctorOrientation.integralComponent O f d c) e (hi _ _)
  · let F := sfRationalConstructibleLocalization C.l E X.obj.left
    let e' := F.mapIso e ≪≫
      (F.commShiftIso (2 * (d : ℤ))).app (sfIntegralTwistingCoefficient C.l E X.obj.left d)
    exact sf_line_on_domain_transport (S.rationalClosed X) (fun _ _ ↦ trivial)
      (SixFunctorOrientation.rationalComponent O f d c) e' (hr _ _)
  · let F := sfRationalConstructibleLocalization C.l
      (AlgebraicallyClosedCoefficients.Coefficient C.l C.Qbar
        (Padic.finiteCoefficientBase C.l C.Qbar)) X.obj.left
    let G := GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := C.l) (Ω := C.Qbar) (Y := X.obj.left)
      (Padic.finiteCoefficientBase C.l C.Qbar)
    let E₀ := AlgebraicallyClosedCoefficients.Coefficient C.l C.Qbar
      (Padic.finiteCoefficientBase C.l C.Qbar)
    let e₀ : sfOrientationIntegralLineOn D C E₀ X d ≅
        sfEvaluationIntegralLine D C E₀ X (d : ℤ) (2 * (d : ℤ)) :=
      ObjectProperty.isoMk _ (sfOrientationIntegralShiftIso C.l E₀ X.obj.left d ≪≫
        (((sfIntegralConstructible C.l E₀ X.obj.left).ι.commShiftIso
          (2 * (d : ℤ))).app (sfIntegralTwistingCoefficient C.l E₀ X.obj.left d)).symm)
    let e' := G.mapIso (F.mapIso e₀ ≪≫
      (F.commShiftIso (2 * (d : ℤ))).app
        (sfIntegralTwistingCoefficient C.l _ X.obj.left d)) ≪≫
      (G.commShiftIso (2 * (d : ℤ))).app (sfRationalTwistingCoefficient C.l _ X.obj.left d)
    exact sf_line_on_domain_transport (S.commonClosed X) (fun _ _ ↦ trivial)
      (SixFunctorOrientation.commonComponent O f d c) e' (hc _ _)

end WeilConjectures
