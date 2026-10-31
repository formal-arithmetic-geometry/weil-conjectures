/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedVerdierBiduality
public import WeilConjectures.SixFunctors.RationalVerdierScalarComparison
import WeilConjectures.SixFunctors.RationalVerdierDomain
import WeilConjectures.SixFunctors.ModCondensedCachedInstances

/-! # Native condensed rational Verdier duality

The single-field clause of the current rational Verdier theorem, together with
canonical evaluation and biduality equations for a specified scalar comparison.
(blueprint: lem-coef-rational-verdier-condensed-single-field).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite
open scoped MonoidalCategory
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace WeilConjectures

set_option synthInstance.maxHeartbeats 200000 in
-- Constructing the derived coefficient unit requires the native monoidal instances.
set_option maxHeartbeats 1600000 in
-- Retaining the full native duality package elaborates several derived instances.
/-- Evaluation biduality and exact anti-equivalence for the actual condensed finite
coefficient field. The dualizing object is the exceptional image of the coefficient
unit, and the equivalence restricts the actual internal Hom into this object.
Source: latest blueprint thm-coef-rational-verdier, first two paragraphs;
sk-thm-pd-verdier-duality, rational coefficient case
(blueprint: lem-coef-rational-verdier-condensed-single-field).

Proof: specialize condensed_verdier_biduality to the continuous-function condensed
ring identified with E. Choose a generator of the principal maximal ideal only to discharge the
auxiliary integral coefficient parameters of that theorem; the conclusion contains
neither this generator nor a finite quotient. The rational coefficient identification
is the supplied monoid isomorphism. Retain its exceptional adjunction, coefficient
unit, preservation, evaluation biduality, restricted equivalence and exactness. -/
theorem coef_rational_verdier_condensed
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (hk : Finite k ∨ IsAlgClosed k) (hcd : BaseFieldFiniteCD l k)
    (E : PadicAlgCl.FiniteIntermediateField l)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1)))
    (T : Over (Spec (.of k))) [LocallyOfFiniteType T.hom]
    [QuasiCompact T.hom] [IsSeparated T.hom] :
    dctfPred Λ T.left = constantModelBoundedConstructible Λ T.left ∧
    dctfPred Λ (Spec (.of k)) = constantModelBoundedConstructible Λ (Spec (.of k)) ∧
    ∃ (h : ∀ K : moduleDerived Λ T.left, dctfPred Λ T.left K →
        dctfPred Λ (Spec (.of k))
          ((condensedVerdierAmbientSupport Λ T).obj K))
      (G : ConstantModelConstructibleFiniteTor Λ (Spec (.of k)) ⥤
        ConstantModelConstructibleFiniteTor Λ T.left)
      (_adj : condensedVerdierSupport Λ T h ⊣ G)
      (N : ConstantModelConstructibleFiniteTor Λ (Spec (.of k))),
      N.obj = 𝟙_ (moduleDerived Λ (Spec (.of k))) ∧
      (∀ K : moduleDerived Λ T.left, dctfPred Λ T.left K →
        dctfPred Λ T.left (((derivedHom Λ T.left).flip.obj (G.obj N).obj).obj (op K))) ∧
      (∀ K : moduleDerived Λ T.left, dctfPred Λ T.left K →
        IsIso ((condensedVerdierBiduality Λ T.left (G.obj N).obj).app K)) ∧
      (∃ e : (ConstantModelConstructibleFiniteTor Λ T.left)ᵒᵖ ≌
          ConstantModelConstructibleFiniteTor Λ T.left,
        Nonempty (e.functor ⋙ (dctfPred Λ T.left).ι ≅
          (dctfPred Λ T.left).ι.op ⋙ (derivedHom Λ T.left).flip.obj (G.obj N).obj)) ∧
      (∀ (Λ' : ScalarSixRing.{u}) (a : (⟨Λ⟩ : ScalarSixRing.{u}) ⟶ Λ')
        (_ha : ListedCoefficientMap l a),
        RationalVerdierScalarCompatibility a T.left (G.obj N)) ∧
      ∃ s : ((derivedHom Λ T.left).flip.obj (G.obj N).obj).CommShift ℤ,
        ∀ U : Triangle (moduleDerived Λ T.left)ᵒᵖ,
          dctfPred Λ T.left U.obj₁.unop → dctfPred Λ T.left U.obj₂.unop →
          dctfPred Λ T.left U.obj₃.unop → U ∈ distTriang (moduleDerived Λ T.left)ᵒᵖ →
          Triangle.mk
            (((derivedHom Λ T.left).flip.obj (G.obj N).obj).map U.mor₁)
            (((derivedHom Λ T.left).flip.obj (G.obj N).obj).map U.mor₂)
            ((((derivedHom Λ T.left).flip.obj (G.obj N).obj).map U.mor₃) ≫
              (s.commShiftIso (1 : ℤ)).hom.app U.obj₁) ∈ distTriang (moduleDerived Λ T.left) := by
  classical
  let : CompactSpace T.left := QuasiCompact.compactSpace_of_compactSpace T.hom
  let : QuasiSeparatedSpace T.left := quasiSeparatedSpace_of_quasiSeparated T.hom
  refine ⟨coef_rational_verdier_domain l E Λ hΛ T.left,
    coef_rational_verdier_domain l E Λ hΛ (Spec (.of k)), ?_⟩
  let π := Submodule.IsPrincipal.generator
    (IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1))
  have hπ : Ideal.span {π} =
      IsLocalRing.maximalIdeal (PadicAlgCl.integers l E.1) :=
    Ideal.span_singleton_generator _
  obtain ⟨h, G, adj, N, hN, hD, hδ, he, hexact⟩ :=
    condensed_verdier_biduality Λ l k hk hcd E π hπ 1
      (Or.inr (Or.inr (Or.inl hΛ))) T
  refine ⟨h, G, adj, N, hN, hD, hδ, he, ?_, hexact⟩
  intro Λ' a ha
  exact coef_rational_verdier_scalar_comparison l k hcd a ha T (G.obj N)

end WeilConjectures
