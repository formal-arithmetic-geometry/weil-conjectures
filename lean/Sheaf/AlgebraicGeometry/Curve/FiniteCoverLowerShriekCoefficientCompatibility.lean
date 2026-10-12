/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.FiniteEtalePushforwardLocallyConstant
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Conditional coefficient hypotheses after a finite cover

Source: Stacks Project, Tag 03SD, `lemma-vanishing-easier`, first paragraph;
Tag 095R, `lemma-finite-pushforward-constructible`.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.IsCurve

/-- The coefficient hypotheses needed for retract descent pass to the finite-cover sheaf.
This statement contains no cohomology assertions and does not assume a unit retraction.

Source: Stacks Project, Tag 03SD, `lemma-vanishing-easier`, first paragraph;
Tag 095R, `lemma-finite-pushforward-constructible`.
(blueprint: v1-finite-cover-lower-shriek-coefficient-compatibility)

Proof: Write F = j_!G and K = j_!(v_*v^*G). Pullback preserves finite locally constant
sheaves. A finite etale map is etale-locally a finite disjoint union of copies of its base;
a common trivializing refinement for the finitely many summands shows that v_*v^*G is
finite locally constant. This part is already stated as
`Scheme.finiteLocallyConstant_lowerStar_of_finite_etale`
(lem-weil-pbc-etale-finite-pushforward-locally-constant), whose finite-ring hypothesis
holds for R = ULift(ZMod r). The open U is Noetherian because it is open in a finite-type
curve over a field. Thus v_*v^*G is constructible; extension by zero preserves
constructibility (equivalently use Tag 095R for finite pushforward).
Every stalk of every R-module sheaf is killed by r, since r is zero in R.
If F is zero, the fully faithful extension by zero gives G zero; pullback and direct
image preserve zero, so K is zero and both torsion implications hold. Otherwise,
conservativity of geometric stalks gives a nonzero element x in a stalk of F.
If F is p-primary then p^n kills x for some n. When p differs from r, Bezout for r
and p^n would give x = 0, a contradiction. Thus p = r, and r itself kills every
stalk element of K, proving primary torsion with exponent one.
If F has invertible-order torsion, some positive n invertible on Spec k kills x.
The same Bezout argument shows r divides n. Writing n = r*m, invertibility of n
implies invertibility of r in the commutative ring of global sections of Spec k.
Since r kills every stalk element of K, choosing n = r proves invertible-order torsion.
These arguments also handle the empty open, empty cover, and zero G. -/
theorem finiteCoverLowerShriek_coefficient_compatibility {k : Type u}
    [Field k] [IsAlgClosed k] {X U V : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] [IsReduced X]
    (j : U ⟶ X) [IsOpenImmersion j] (r : ℕ) [Fact r.Prime]
    (G : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod r))))
    [Scheme.IsFiniteLocallyConstantSheaf G] (v : V ⟶ U) [IsFinite v] [Etale v] :
    let R := ULift.{u + 1} (ZMod r)
    let F := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj G
    let K := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} R) v).obj
        ((Etale.upperStar (ModuleCat.{u + 1} R) v).obj G))
    Scheme.IsConstructibleSheaf K ∧
      (Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) F →
        Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) K) ∧
      (∀ (p : ℕ) [Fact p.Prime] [CharP k p],
        Scheme.IsPrimaryTorsionSheaf R F p → Scheme.IsPrimaryTorsionSheaf R K p) := by
  sorry

end AlgebraicGeometry.IsCurve
