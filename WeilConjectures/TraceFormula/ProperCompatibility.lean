/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ProperCompatibilityExchange

/-!

# Proper pushforward compatibility of the trace class

For a proper pushforward diagram `(f, g) : (C, c) ⟶ (D, b)` with induced proper map of fixed
loci `h`, the Borel–Moore pushforward of the trace class of `u` is the trace class of the pushed
correspondence: `h_* Tr_c(u) = Tr_b([f, g]_! u)` (blueprint `thm-trf-trace-proper-compatibility`,
`sk-p-proper`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence.ProperPushforwardDiagram

variable {c : Correspondence ℓ K} {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (P : c.ProperPushforwardDiagram Y) (Fc : c.FixedLocus)
  (Fb : P.pushforward.FixedLocus)

set_option maxHeartbeats 3000000 in
-- composite functors on bounded constructible complexes are unfolded
/-- The point `T_b = 𝔱 ∘ ũ` of the pushed correspondence is obtained from that of `c` by
transport along `g` (blueprint `thm-trf-trace-proper-compatibility`, Step 3):
`T_b = Ri_{b*} τ_h ∘ Rg_* T_c ∘ η_g`. -/
lemma mate_comp_traceMap_pushforward :
    P.pushforward.mate ≫ P.pushforward.traceMap Fb =
      ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ P.g).unit.app (𝟙_ _) ≫
          (boundedConstructibleLowerStar _ ℓ P.g).map
            (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ P.g)).inv) ≫
        (boundedConstructibleLowerStar _ ℓ P.g).map (c.mate ≫ c.traceMap Fc) ≫
        (boundedConstructibleLowerStarComp _ ℓ Fc.ι P.g).hom.app (dualizingComplex' ℓ Fc.F) ≫
        eqToHom (by rw [← P.fixMap_ι]) ≫
        (boundedConstructibleLowerStarComp _ ℓ (P.fixMap Fc Fb) Fb.ι).inv.app
          (dualizingComplex' ℓ Fc.F) ≫
        (boundedConstructibleLowerStar _ ℓ Fb.ι).map
          (lowerStarDualizingComplexTrace ℓ (P.fixMap Fc Fb)) := by
  have e4 := Adjunction.homEquiv_comp_mateEquiv_of_eq
    (boundedConstructibleUpperShriekAdjunction _ ℓ c.support)
    (boundedConstructibleUpperShriekAdjunction _ ℓ P.pushforward.support)
    (lowerStarLowerShriekCompIso ℓ P.g_comp_support).hom
    ((boundedConstructibleUpperStarLowerStarAdjunction _ ℓ P.g).unit.app (𝟙_ _) ≫
      (boundedConstructibleLowerStar _ ℓ P.g).map
        (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ P.g)).inv)
    c.kernelClass (evaluationKernel ℓ K)
    ((boundedConstructibleLowerStarComp _ ℓ (diag X) (prod.map P.f P.f)).hom.app
          (dualizingComplex' ℓ X) ≫
        eqToHom (by rw [P.diag_comp_prodMap]) ≫
        (boundedConstructibleLowerStarComp _ ℓ P.f (diag Y)).inv.app (dualizingComplex' ℓ X) ≫
        (boundedConstructibleLowerStar _ ℓ (diag Y)).map (lowerStarDualizingComplexTrace ℓ P.f))
    (c.mate ≫ c.traceMap Fc) Fc.supportIso.hom
    (by rw [Category.assoc]; exact (mate_comp_traceMap_comp_supportIso c Fc).symm) _
    (lowerStarUpperShriekExchange ℓ P.g_comp_support) (by unfold lowerStarUpperShriekExchange; rfl)
    (P.lowerStar_map_supportIso_comp_exchange Fc Fb)
  have e1 := mate_comp_traceMap_comp_supportIso P.pushforward Fb
  rw [P.kernelClass_pushforward] at e1
  simp only [Category.assoc, P.kernelPushforward_comp_evaluationKernel] at e1
  have e5 := e1.trans e4
  rw [← cancel_mono Fb.supportIso.hom]
  simpa only [Category.assoc] using e5

/-- **Proper pushforward compatibility of the trace class** (blueprint
`thm-trf-trace-proper-compatibility`, `sk-p-proper`; Varshavsky 1.2.5): for a proper pushforward
diagram `(f, g) : (C, c) ⟶ (D, b)` with induced proper map of fixed loci `h`,
`h_* Tr_c(u) = Tr_b([f, g]_! u)`. No properness over `s` and no cartesian leg square are needed.
The special case `f = 𝟙` is blueprint `lem-trf-proper-pushforward-trace-class`. The proof goes
through the exchange of the trace maps (`lem-trf-trace-map-exchange`) and of the trace-class
sources (`lem-trf-trace-source-exchange`). -/
theorem traceClassPushforward_eq :
    P.traceClassPushforward Fc Fb = P.pushforward.traceClass Fb :=
  sorry


end Correspondence.ProperPushforwardDiagram

end AlgebraicGeometry.ProEtale.CondensedRing
