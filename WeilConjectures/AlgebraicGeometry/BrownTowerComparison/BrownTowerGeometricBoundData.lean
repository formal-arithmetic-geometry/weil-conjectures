/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.BrownTowerComparison.BrownTowerGeometricSiteData
/-! # Common-bound part of geometric Brown transport -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
namespace BrownTowerComparison
variable {O : Type (u + 1)} [CommRing O] {t : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}

/-- The common exceptional bound and normalization field, after the site data
have been fixed. Source: Zheng Lemma 5.22 and the final step of the geometric
transport construction.
(blueprint: lem-route-brown-tower-geometric-transport-core-exists).
-/
structure GeometricTransportBoundData (S : StrictEtaleCompactSupport O t c)
    (G : EtaleTowerBrownAdjunction S) (H : FiniteEvaluation S G)
    (D : GeometricTransportSiteData S G H) where
  [finite : ∀ n : ℕ, Finite (Ring O t n)]
  bound : ∀ (C : DerivedCategory (ProSystem Y O t)), D.siteY.Origin C →
    IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology Y) O t D.siteY.proEvaluation C →
    (∀ n, FiniteCoefficientAdjoints.ctf (Ring O t n) Y
      ((D.siteY.realization n).derived.obj
        ((D.siteY.proEvaluation.evaluation n).obj C))) →
    ∀ a : ℤ,
    (∀ n, ((finiteExceptional S G H D.siteX D.siteY n).obj
      ((D.siteY.proEvaluation.evaluation n).obj C)).IsGE a) →
    (G.right.obj (D.siteY.direct.obj C)).IsGE a ∧
    (D.siteX.inverse.obj (G.right.obj (D.siteY.direct.obj C))).IsGE a ∧
    IsNormalizedCoefficientSystem.{u + 1, u, u + 1, u + 2}
      (J := Scheme.ProEt.topology X) O t D.siteX.proEvaluation
      (D.siteX.inverse.obj (G.right.obj (D.siteY.direct.obj C)))

/-- The common-bound reflection and normalization are supplied by the exact
faithful finite site inverse images and the coefficient-mate compatibility.
The proof is Zheng Lemma 5.22: evaluate the Brown right adjoint levelwise,
reflect the supplied common lower bound through the site inverse image, and
transport the normalized transition mates. -/
theorem geometricTransportBoundData_exists
    (S : StrictEtaleCompactSupport O t c)
    (G : EtaleTowerBrownAdjunction S)
    (H : FiniteEvaluation S G)
    (D : GeometricTransportSiteData S G H) :
    Nonempty (GeometricTransportBoundData S G H D) := by
  sorry

end BrownTowerComparison
end AlgebraicGeometry
