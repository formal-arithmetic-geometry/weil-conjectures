/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom

/-! # Chain-level intrinsic Hom transport

Source: Stacks Project, Tags 00YV, 08J7 and 0A95; coefficient-presentation
transport in Step 2 of lem-sf-tensor-exchange-ctf-domains.
(blueprint: lem-sf-intrinsic-site-hom-transport-chain)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- The realized fixed-coefficient derived Hom is represented by the intrinsic
Hom complex on the chosen K-injective representatives.

Source: Stacks Project, Tags 00YV, 08J7 and 0A95; coefficient-presentation
transport in Step 2 of lem-sf-tensor-exchange-ctf-domains.

Proof: apply the exact associated-module-sheaf realization termwise to the
fixed-coefficient Hom complex. The sheaf-Hom/tensor adjunction identifies each
term and its signed differential with the intrinsic constant-ring Hom complex;
exactness of the realization then carries the localized representative to the
localized intrinsic complex.
(blueprint: lem-sf-intrinsic-site-hom-transport-chain) -/
theorem intrinsicSiteHom_transport_chain (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (Lc Ic : CochainComplex
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ)
    [Ic.IsKInjective] :
    Nonempty
      ((finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj
          (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).obj
            (op (DerivedCategory.Q.obj Lc))).obj (DerivedCategory.Q.obj Ic)) ≅
        DerivedCategory.Q.obj
          (homComplex.{u + 1, u, u + 1, u + 1}
            (R := proEtaleConstantRing X A)
            (((finiteCoefficientIntrinsicRealization X A).mapHomologicalComplex
              (.up ℤ)).obj Lc)
            (((finiteCoefficientIntrinsicRealization X A).mapHomologicalComplex
              (.up ℤ)).obj Ic))) := by
  sorry

end AlgebraicGeometry.ProEtale
