/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyCoefficientTransport

/-! # The fixed module/Ext comparison respects h-maps

Source: Stacks Project, Tags 01FB and 03FD.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section
set_option autoImplicit false

/-- The resolution comparison respects h-maps in its original Ext universe.
Source: Stacks Project, Tag 01FB (coefficient factorization) and Tag 03FD (comparison).
(blueprint: lem-pbc-module-ext-resolution-hmap).

Proof: Apply the coefficient-transport theorem to the fixed resolution equivalences.
Their coefficient naturality supplies its first hypothesis, and the existing edge-map
compatibility supplies its second. The transport theorem factors the general module
h-map through the identity edge coefficient, applies those two squares, and uses the
abelian coefficient factorization. No universe change enters this statement. -/
theorem moduleCohomologyExtResolutionEquiv_hmap {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (φ : F ⟶ (pushforward g).obj G)
    (q : ℕ) (x : (RingedSpace.moduleCohomology X.toRingedSpace q).obj F) :
    moduleCohomologyExtResolutionEquiv Y G q (moduleCohomologyFMap g φ q x) =
      Sheaf.H.map (coeff g φ) q
        (Sheaf.H.mapFunctor (invImage g) (constIso g).symm
          ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) q
          (moduleCohomologyExtResolutionEquiv X F q x)) := by
  exact moduleCohomology_transport_coefficient g F G φ q
    (fun M ↦ moduleCohomologyExtResolutionEquiv X M q)
    (moduleCohomologyExtResolutionEquiv Y G q)
    (moduleCohomologyExtResolutionEquiv_naturality X q F _ φ)
    (moduleCohomologyExtResolutionEquiv_edge g G q) x

end
end AlgebraicGeometry.Scheme.Modules
