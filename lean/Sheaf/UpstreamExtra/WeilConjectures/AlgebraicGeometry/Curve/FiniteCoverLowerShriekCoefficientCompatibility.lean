module

public import WeilConjectures.AlgebraicGeometry.Curve.FiniteCoverLowerShriekCoefficientCompatibility

/-! Declarations of ours that lived in the upstream file `WeilConjectures.AlgebraicGeometry.Curve.FiniteCoverLowerShriekCoefficientCompatibility` (moved out by the scheduled sync, tools/upstream_verbatim.py, 2026-10-20: upstream files are verbatim in live). -/

/-! # Conditional coefficient hypotheses after a finite cover

Source: Stacks Project, Tag 03SD, `lemma-vanishing-easier`, first paragraph;
Tag 095R, `lemma-finite-pushforward-constructible`.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.IsCurve

theorem finiteCoverLowerShriek_constructible_pending {k : Type u}
    [Field k] [IsAlgClosed k] {X U V : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (r : ℕ) [Fact r.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    [Scheme.IsFiniteLocallyConstantSheaf G] (v : V ⟶ U) [IsFinite v] [Etale v] :
    Scheme.IsConstructibleSheaf
      ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) j).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj
          ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj G))) := by
  exact finiteCoverLowerShriek_constructible f j r G v


end AlgebraicGeometry.IsCurve
