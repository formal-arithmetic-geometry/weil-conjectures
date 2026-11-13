/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportGraphDerivedIsoSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumCompositionCounit
import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportSumCompositorComponent

/-! # Support and sum compositors under the constructed graph comparison

Source: Stacks Project, More on Etale Cohomology, Tags 0F7J, 0F7K and 0F50.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The actual proper/open compositor becomes nested sum composition under the graph maps.
Source: Stacks Project, Tags 0F7J, 0F7K and 0F50. -/
theorem etaleSupportSumCompositor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X T : Scheme.{u}} [IsNoetherian U] [IsNoetherian X] [IsNoetherian T]
    (e : U ⟶ X) (v : X ⟶ T)
    [Etale e] [Etale v] [IsSeparated e] [IsSeparated v]
    [QuasiCompact e] [QuasiCompact v]
    (c : Compactification e) (d : Compactification v) (k : Compactification (e ≫ v)) :
    (Functor.isoWhiskerRight
        (rightDerivedLowerShriekOfCompactificationIso A c (k.ofComp d).restrict) _ ≪≫
      rightDerivedLowerShriekOfCompactificationCompIso A d (k.ofComp d) ≪≫
      rightDerivedLowerShriekOfCompactificationIso A (d.comp (k.ofComp d)) k).hom ≫
        (canonicalEtaleCompactSupportComparison A (e ≫ v) k).hom =
      NatTrans.hcomp (canonicalEtaleCompactSupportComparison A e c).hom
          (canonicalEtaleCompactSupportComparison A v d).hom ≫
        (derivedEtaleSumCompIso A e v).hom := by
  ext M
  exact etaleSupportSumCompositor_app A e v c d k M

end AlgebraicGeometry.Etale
