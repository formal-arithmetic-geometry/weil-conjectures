module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ConstructibleTorsionCurveSheaf
import Sheaf.AlgebraicGeometry.Curve.RetractAssertions
import Sheaf.AlgebraicGeometry.FinitePushforwardConstructibleNoetherian

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.IsCurve

/-- Descend the eight curve assertions along the supplied unit retraction.

Write `H` for the sheaf in `hH`.  Applying the open-immersion lower-shriek
functor to the unit and to `ρ` gives maps between the lower-shriek of `G` and the
lower-shriek of `H`; functoriality and `hρ` make the composite on the `G` side the
identity. Hence `j_! G` is a retract of `j_! H`.
Put F = j_!G and K = j_!(v_*v^*G). Both are killed by r and are constructible,
by finite locally constant pullback, finite pushforward on the noetherian curve,
and extension by zero. If F is p-primary and nonzero, a nonzero stalk is killed
by r and a power of p, so primality forces p = r; hence K is p-primary.
If F has invertible-order torsion and is nonzero, a nonzero stalk has order r,
so r is invertible in k; hence K has invertible-order torsion. If F is zero,
restriction to U gives G = 0, and pullback and finite pushforward give K = 0.
Thus every conditional coefficient hypothesis needed to apply hH passes from F to K.
Cohomology preserves the retraction, so vanishing and finiteness descend. The field-extension and
open-restriction maps for `G` are retracts of the corresponding maps for `H`, so
their bijectivity or surjectivity descends as well.  Applying these closure facts
to the eight conjuncts of `hH` proves the conclusion.  This is exactly the final
retract step of 03SD; no additional property of the degree or connectedness of
`v` is required once `hH`, `ρ`, and `hρ` are supplied.
(blueprint: k1-filtered-finite-cover-lower-shriek-transfer-retract) -/
theorem filteredFiniteCoverLowerShriekTransfer_retract {k : Type u} [Field k] [IsAlgClosed k]
    {X U V : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (r : ℕ) [Fact r.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    [Scheme.IsFiniteLocallyConstantSheaf G] (v : V ⟶ U) [IsFinite v] [Etale v]
    (hH : IsCurve.Assertions (ULift.{u + 1} (ZMod r)) f
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) j).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj
          ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj G))))
    (ρ : (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj
      ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).obj G) ⟶ G)
    (hρ : (Etale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) v).unit.app G ≫ ρ = 𝟙 G) :
    IsCurve.Assertions (ULift.{u + 1} (ZMod r)) f
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))) j).obj G) := by
  sorry

end AlgebraicGeometry.IsCurve
