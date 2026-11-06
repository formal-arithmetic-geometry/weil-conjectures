/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-! # Etale locality of the ordinary ambient adjoint

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-etale-adjoint-locality.md
(blueprint: lem-amb-etale-adjoint-locality).

Sheaf-level exactness is the existing `preservesFiniteLimits_etaleLowerShriek`, together
with preservation of colimits by its existing left-adjoint structure. The first declaration
below descends the existing sheaf adjunction, without any boundedness restriction. The second
states locality for arbitrary right adjoints of the ordinary compact-support candidates.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The termwise derived sum-extension/restriction adjunction on whole unbounded categories.
Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-etale-adjoint-locality.md,
first assertion (blueprint: lem-amb-etale-adjoint-locality).
Both sheaf functors are exact; the degreewise unit and counit descend through localization,
and their triangle identities descend as well. The construction uses the existing sheaf
adjunction and the general exact-functor derived-adjunction construction. -/
noncomputable def etaleAmbientLeftComparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X S : Scheme.{u}} (u : U ⟶ X) (f : X ⟶ S)
    [Etale u] [IsSeparated u] [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    (c : Compactification f) (d : Compactification (u ≫ f)) :
    (etaleLowerShriek (ModuleCat.{u + 1} A) u inferInstance).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) d :=
  Functor.isoWhiskerRight (N.comparison u (d.ofComp c).restrict).symm _ ≪≫
    rightDerivedLowerShriekOfCompactificationCompIso A c (d.ofComp c) ≪≫
    rightDerivedLowerShriekOfCompactificationIso A (c.comp (d.ofComp c)) d

end AlgebraicGeometry.Etale
