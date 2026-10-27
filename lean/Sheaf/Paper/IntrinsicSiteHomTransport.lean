/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K9
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom

/-! # Internal Hom in the intrinsic finite-coefficient presentation

Source: Stacks Project, Tags 00YV, 08J7 and 0A95; the coefficient-presentation
transport in Step 2 of lem-sf-tensor-exchange-ctf-domains.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

/-- Constant-scalar realization identifies the two ambient derived internal Homs.
There are no geometric finiteness or constructibility hypotheses.

Source: Stacks Project, Tags 00YV, 08J7 and 0A95; coefficient-presentation
transport in Step 2 of lem-sf-tensor-exchange-ctf-domains
(blueprint: lem-sf-intrinsic-site-hom-transport).

Proof: restriction along the constant-scalar sheafification unit is the inverse
of the exact associated-module-sheaf realization. On every slice this exact
equivalence identifies the ordinary sheaf Hom by its adjunction to tensor:
both tensors are sheafifications of the same balanced pure tensors. Apply the
equivalence termwise to a K-injective resolution of the second argument.
An exact equivalence preserves K-injectivity, since the inverse equivalence
preserves acyclic complexes. The ordinary sheaf-Hom identification on all
slices identifies the Hom complexes and their signed differentials. Thus these
complexes compute both the fixed-scalar derived Hom and the recorded intrinsic
Hom-complex localization. Localization and independence of K-injective
resolutions give the displayed isomorphism for arbitrary unbounded inputs.
The zero ring and empty site are included: the same equivalence and chain
identifications apply. -/
theorem intrinsicSiteHom_transport (X : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A]
    (K L : DerivedCategory
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Nonempty
      ((finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj
          (((derivedHom (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).obj (op K)).obj L) ≅
        (derivedInternalHomOfUniverses.{u + 1, u, u} (ProEt.topology X)
          (proEtaleConstantRing X A)).obj
          (op ((finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj K),
            (finiteCoefficientIntrinsicRealization X A).mapDerivedCategory.obj L)) := by
  sorry

end AlgebraicGeometry.ProEtale
