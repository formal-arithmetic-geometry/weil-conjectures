/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralDualizingRoosModel
import WeilConjectures.SixFunctors.Integral.IntegralDualizingFiniteBounds
import WeilConjectures.SixFunctors.Integral.IntegralDualizingExceptionalPresentation
import WeilConjectures.SixFunctors.Integral.IntegralDualizingAdjunctionGlobalHom

/- Stage-2 statement delivery metadata: Q117, 2026-10-18. -/
/-!
# The integral dualizing object and its adjunction

Source: current blueprint `sec-smooth-purity/sk-lem-sp-tower`, order 2990
(blueprint: prop-coef-integral-dualizing).

All coefficients are ordinary module sheaves over the completed coefficient sheaf.
The mapping complexes retain the coefficient-module action. Compact support is the
actual strict reduction-tower functor followed by total right derived inverse limit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/--
Fix the finite-field datum, a prime different from its characteristic, a finite coefficient
extension, and a separated finite-type scheme over the algebraic closure. There is a bounded
constructible derived-complete integral object `ω`, presented by a normalized DVR tower whose
finite terms are the exceptional inverse images of the coefficient units. Every reduction is
identified with the corresponding finite term and has Tor amplitude `[-2d,0]`. For every
constructible integral `K`, the value `C` of integral compact support at the coefficient point
has the asserted adjunction bijection with `ω` and the coefficient unit.

Source: blueprint node `prop-coef-integral-dualizing`, order 2145
(blueprint: prop-coef-integral-dualizing).

Proof: construct the coherent finite-dualizing tower and obtain the exceptional
adjunction with its complete coherent presentation. Take ω to be its right-adjoint value
at the coefficient unit, so constructibility and derived completeness hold by membership
in the integral constructible category. The presentation and the published limit have
Roos triangles with the same middle arrow. Complete the identity square on the two
product objects to a triangle morphism; its first component is an isomorphism by
Mathlib's two-out-of-three theorem. This gives the required limit identification.
Compose the presentation's canonical reduction isomorphisms with the finite-term
identifications and apply the finite dualizing Tor bounds. The direct global Hom theorem
applies to ω itself. The degree-zero clause is the ordinary adjunction, lifted through
the fully faithful constructible inclusions and conjugated by the compact-support and
coefficient-unit isomorphisms. No completeness-predicate conversion, separate effectivity
argument, or transport of the enriched comparison to a separately chosen limit is needed.
-/
theorem prop_coef_integral_dualizing
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    ∃ (ω : sfIntegralConstructibleCategory l E X)
      (T : NormalizedDVRTower l E X D hl),
      (∀ n : ℕ, Nonempty (T.M n ≅ integralDualizingFiniteTerm (l := l) (E := E)
        (D := D) (X := X) n)) ∧
      (∃ (e : ∀ n : ℕ, T.M n ≅ integralDualizingFiniteTerm (l := l) (E := E)
        (D := D) (X := X) n),
        (∀ {m n : ℕ} (h : n ≤ m),
          T.tau h ≫ (normalizedDVRRes l E X h).map (e n).hom =
            (e m).hom ≫
              (Adjunction.ofIsRightAdjoint (normalizedDVRRes l E X h)).homEquiv _ _
                (integralDualizingFiniteComparison l E D X hl h))) ∧
      Nonempty (ω.obj ≅ (integralDualizingLimit l E X).obj T.tower) ∧
      IntegralDualizingLimitPresentation l E D hl X T ω.obj ∧
      (∀ n : ℕ, HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension l E X n).obj ω.obj) (-(2 * (d : ℤ))) 0) ∧
      Nonempty (integralDualizingGlobalHom l E X ω.obj ≅
        (integralDualizingCompactSections l E D hl X).op ⋙
          coefficientDerivedDual (integralDualizingCoefficients l E)) ∧
      ∀ K : sfIntegralConstructibleCategory l E X,
        Nonempty ((K.obj ⟶ ω.obj) ≃
          ((integralDualizingLimit l E (Spec (.of D.k))).obj
            ((integralDualizingCompactTower l E D hl X).obj K.obj) ⟶
              (DerivedCategory.singleFunctor (scalarReductionSource l E (Spec (.of D.k))) 0).obj
                (SheafOfModules.unit
                  (completedIntegralCoefficientSheafUnrestricted l E (Spec (.of D.k)))))) := by
  obtain ⟨T, e, he, p, δ, htriangle⟩ := integralDualizing_roos_model D l hl E X
  obtain ⟨A, hpresentation⟩ :=
    integralDualizing_exceptional_presentation D l hl E X T e he
  let ω := A.right.obj A.unit
  let : HasCountableProducts (completedIntegralDerivedCategory l E X D hl) :=
    integralOperationsDerivedCountableProducts l E X
  obtain ⟨q, ε, htriangleω, hred, hcoherent⟩ := hpresentation
  have hlimit : Nonempty (ω.obj ≅ (integralDualizingLimit l E X).obj T.tower) := by
    let U := CategoryTheory.Pretriangulated.Triangle.mk q
      (towerTransitionEndomorphism
        (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)) ε
    let V := CategoryTheory.Pretriangulated.Triangle.mk p
      (towerTransitionEndomorphism
        (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)) δ
    obtain ⟨a, ha₁, ha₃⟩ :=
      CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism₁
        U V htriangleω htriangle (𝟙 _) (𝟙 _) (by simp [U, V])
    let f : U ⟶ V := CategoryTheory.Pretriangulated.Triangle.homMk U V a (𝟙 _) (𝟙 _)
      ha₁ (by simp [U, V]) ha₃
    have : IsIso f.hom₂ := by
      dsimp [f, CategoryTheory.Pretriangulated.Triangle.homMk]
      infer_instance
    have : IsIso f.hom₃ := by
      dsimp [f, CategoryTheory.Pretriangulated.Triangle.homMk]
      infer_instance
    have : IsIso a := CategoryTheory.Pretriangulated.isIso₁_of_isIso₂₃
      f htriangleω htriangle inferInstance inferInstance
    exact ⟨asIso a⟩
  have hbounds (n : ℕ) := integralDualizing_finite_bounds D l hl E X d hd n
    ((scalarReductionDerivedExtension l E X n).obj ω.obj)
    (@asIso _ _ _ _ (normalizedDVRCounitComparison l E X D hl T ω.obj q n)
      (hred n) ≪≫ e n)
  refine ⟨ω, T, (fun n ↦ ⟨e n⟩), ⟨e, he⟩, hlimit,
    ⟨q, ε, htriangleω, hred, hcoherent⟩,
    (fun n ↦ (hbounds n).2.2), integralDualizing_adjunction_global_hom D l hl E X A, ?_⟩
  exact fun K ↦ ⟨A.homEquiv K⟩

end WeilConjectures
