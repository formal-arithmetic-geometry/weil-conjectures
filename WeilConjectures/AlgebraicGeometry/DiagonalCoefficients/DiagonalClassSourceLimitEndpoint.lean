/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalClassPullbackFrame

/-! # The closed-source limit endpoint
Source: the latest blueprint, diagonal coefficient changes, paragraph (3).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
open DiagonalTrace
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor diagonalCompletedSource

/-- Closed-support and generator normalization of the source-limit endpoint.
There is no completed diagonal arrow in this statement.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3),
closed base change and the supported constant-source endpoint.
(blueprint: lem-diagonal-class-source-limit-endpoint).

Proof: pull the global unit of the prime to both projective lines and surfaces.
Use the canonical monoidal unit pullbacks and the Cartesian integral Tate-line
comparisons to construct the two unit and line endpoints. The projective diagonal
is a closed immersion and its Cartesian pullback is the new diagonal. Apply
closed-support base change to its regular condensed coefficient module, with the
coefficient restrictions transported along the canonical constant-ring square.
Its forward map is the ordinary exchange followed by the regular-module unit
pullback, so it is exactly sourcePullbackMap. This constructs SourcePullback.
Apply diagonalClassPullbackFrame_exists to this ordinary supported data. It
provides the normalized reduction, constant/limit adjunction, scalar and realization
comparisons, and retains the supported data as its data field.

Compare the ordinary source cones at every quotient: the generator equation
for s₀, the normalized quotient equation for the reduction square, and the
scalar-unit adjunction equation give the same map. Cancel the quotient
projection after scalar extension; the ordinary limit universal property then
identifies the full cones. Transpose the pulled cone under the normalized
constant/derived-limit adjunction. On K-injective resolutions its counit is the
ordinary cone, so both transposes agree as full strict-system morphisms.
The regular resolving-class equation identifies the reduction comparison used
here with the supplied one. Localize with the exact single comparisons.
Finally hs and hs' identify the supported realized endpoint with the closed
exchange above. Full faithfulness of the derived realization identifies its
transport with frame.sourceComparison. This proves limit_endpoint.
All cone comparisons are comparisons of ordinary sheaf morphisms or full
adjunction transposes; there is no detection of derived maps by evaluation.
The construction also applies to the empty base and to the prime two. -/
theorem diagonalClassSourceLimitEndpoint_exists (l : ℕ) [Fact l.Prime]
    (Y Y' : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    (g : Y' ⟶ Y) (geometry : BaseSquares g)
    (hY : IsUnit (l : Γ(Y, ⊤))) (hY' : IsUnit (l : Γ(Y', ⊤)))
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y')))
    (d : ClassLimitPresentation l Y hY D) (d' : ClassLimitPresentation l Y' hY' D')
    (eP : CompletedRealization l (ProjectiveLine Y))
    (eW : CompletedRealization l (diagonalSurface Y))
    (eP' : CompletedRealization l (ProjectiveLine Y'))
    (eW' : CompletedRealization l (diagonalSurface Y'))
    (s : eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : eW'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y')
    (hs : HEq (eW.underlying.inv.app (diagonalCompletedSource l Y) ≫ s.hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (eP.underlying.inv.app (SheafOfModules.unit
          (Scheme.purTwistRing (ProjectiveLine Y)
            (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≫ eP.unitIso.hom.hom)))
    (hs' : HEq (eW'.underlying.inv.app (diagonalCompletedSource l Y') ≫ s'.hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y')).map
        (eP'.underlying.inv.app (SheafOfModules.unit
          (Scheme.purTwistRing (ProjectiveLine Y')
            (Scheme.purTwistZlCompletion (ProjectiveLine Y') l))) ≫ eP'.unitIso.hom.hom))) :
    Nonempty (DiagonalClassSourceEndpoint (g := g) (d := d) (d' := d') s s') := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
