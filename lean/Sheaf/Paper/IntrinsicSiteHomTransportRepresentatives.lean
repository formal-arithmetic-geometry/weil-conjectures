/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom

/-! # Representative-level intrinsic Hom transport

Source: Stacks Project, Tags 00YV, 08J7 and 0A95; coefficient-presentation
transport in Step 2 of lem-sf-tensor-exchange-ctf-domains.
(blueprint: lem-sf-intrinsic-site-hom-transport)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Representative-level coefficient transport.  The source and target derived objects
are fixed representatives, with the second representative K-injective.  The arbitrary
object statement is obtained by the usual representative and localization argument.

Source: Stacks Project, Tags 00YV, 08J7 and 0A95; coefficient-presentation transport
in Step 2 of lem-sf-tensor-exchange-ctf-domains.

Proof: apply the exact associated-module-sheaf realization to the Hom object computed
on the chosen representatives.  The sheaf-Hom and tensor adjunctions identify the
resulting Hom complex with the intrinsic constant-ring Hom complex, and exactness of
the
realization preserves the K-injective computation.  The comparison is natural in both
representatives and hence descends through the derived quotient.
-/
theorem intrinsicSiteHom_transport_representatives (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (Lc Ic : CochainComplex
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ)
    [Ic.IsKInjective] :
    Nonempty
      ((finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj
          (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).obj
            (op (DerivedCategory.Q.obj Lc))).obj (DerivedCategory.Q.obj Ic)) ≅
        (derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
          (proEtaleConstantRing X A)).obj
          (op ((finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj
            (DerivedCategory.Q.obj Lc)),
            (finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj
              (DerivedCategory.Q.obj Ic))) := by
  sorry

end AlgebraicGeometry.ProEtale
