/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.GeneralChartComparisons

/-! # Identity and composition of chart epsilon -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.ChartComparisons

/-- The source-etale exceptional comparison respects the pullback identity and
composition constraints.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1
(blueprint: lem-pur-chart-epsilon-pasting).

Proof: use associativity and identity of the canonical compact-support compositor.
The adjunction Hom bijections are injective, so transposing its associativity and
identity gives the corresponding equations for the specified exceptional compositor.
Substitute the counit-normalized etale identification. Its identity and composition
laws and naturality at the inner exceptional compositor show that the two composites
of epsilon agree. Conjugate by diagonalDualizingComparison and the canonical site
pullback comparison; their identity and composition coherence cancels all intermediate
factors. Finally insert omegaCongr for the supplied chart projection equalities.
Proof irrelevance identifies the equality transports under associativity. This gives
the displayed laws including all open restrictions, rank zero and empty charts. -/
theorem chart_epsilon_pasting (P : PurityFiniteSetting.{u})
    {V : Scheme.{u}} [IsAffine V] {d : ℕ}
    (aV : V ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aV] [QuasiCompact aV]
    :
    (∀ (C : Chart V d) (N : Etale.EtaleCompactSupportNormalization P.Coefficient),
      eps P aV (Map.id C) N ≪≫
        (ProEtale.leftDerivedUpperStarId (ModuleCat.{u + 1} P.Coefficient) C.X).app
          (omega P C.proj aV) = Iso.refl _) ∧
    (∀ (C B A : Chart V d) (v : Map C B) (e : Map B A)
      (N : Etale.EtaleCompactSupportNormalization P.Coefficient),
      eps P aV (v.comp e) N ≪≫
        (ProEtale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          v.hom e.hom).app (omega P A.proj aV) = eps P aV v N ≪≫
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) v.hom).leftDerivedFunctor.mapIso
          (eps P aV e N)) := by
  sorry

end WeilConjectures.PurityFiniteSetting.ChartComparisons
