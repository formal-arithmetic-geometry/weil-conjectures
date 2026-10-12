/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceComparison
import Sheaf.AlgebraicGeometry.EtaleInjectiveSectionsComparison
import Sheaf.AlgebraicGeometry.StrictLocalCohomologyGerms
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # Computing source derived sections on an injective representative

Source: Stacks Project, Tags 03Q8 and 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-strict-local-injective-source-transition).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The canonical cycle comparison commutes with neighbourhood restriction.
Source: Stacks Project, Tag 03Q8, computation of direct images by injective complexes;
Tag 03Q9, restrictions of the complex of sections.
(blueprint: lem-weil-pbc-strict-local-injective-source-transition).

Proof: write M for the complex underlying J and L for f_*M. The right-derived unit
on M is natural and invertible. Under its comparison with Rf_*K, precomposition by
the free sheaf of a neighbourhood map is precomposition in HomComplex(Z[V][0], L).
The localization bijection on Hom into the K-injective complex L commutes with
this precomposition: apply Qh to the corresponding chain maps and use functoriality.
Evaluation of the free generator commutes with the neighbourhood map by Yoneda
naturality. Hence the induced map on the complex of sections is L's restriction
map. Direct image evaluates this as restriction on the base-changed neighbourhood.
The localization-restriction comparison for each etale projection is the unique
comparison of two left adjoints to the same direct image; its unit compatibility
identifies this map with sectionsPullbackNat followed by upperStarComp.inv.
This is exactly the chain map defining termwiseSectionsRestriction. Naturality of
the Hom-complex homology isomorphism and of homologyFunctorFactors gives the stated
square. Transport by q is natural and therefore preserves it. No cone leg or mate
is involved. Identity transitions reduce to identity chain maps; zero complexes
and all integer degrees use the same computation. -/
theorem strictLocalInjectiveSourceIso_transition {X S : Scheme.{v}}
    (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ)
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    ∀ {i j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)} (a : i ⟶ j),
        (strictLocalCohomologyNeighbourhoodFunctor s
          ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).map a.op ≫
          (strictLocalInjectiveSourceIso f s K n J q i).hom =
          (strictLocalInjectiveSourceIso f s K n J q j).hom ≫
            termwiseSectionsRestriction ((strictLocalNeighbourhoodDiagram f s).map a)
              ((strictLocalNeighbourhoodProjection f s).app j)
              ((strictLocalNeighbourhoodProjection f s).app i)
              ((Category.comp_id _).symm.trans
                ((strictLocalNeighbourhoodProjection f s).naturality a).symm)
              (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) n := by sorry

end AlgebraicGeometry.Etale
