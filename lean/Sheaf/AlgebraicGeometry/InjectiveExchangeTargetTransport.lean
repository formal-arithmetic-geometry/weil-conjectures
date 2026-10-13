/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.AlgebraicGeometry.StrictLocalInjectiveSourceComparison
public import WeilConjectures.SixFunctors.BaseChange.Square

/-! # Target localization and derived-unit transport

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-injective-exchange-target-transport).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Transport the localized underived exchange and target unit to unbounded categories.

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph; the exact
localization comparisons and defining unit compatibility of
`Functor.rightDerivedFunctorPlusCompatibility`.
(blueprint: lem-weil-pbc-injective-exchange-target-transport).

Proof: map the bounded-below composite through the inclusion and use its
compatibility with mapDerivedCategoryPlusFactorsh. The first factor is the
homotopy version of the exact comparison for U and cancels against its
complex-level inverse, because the homotopy quotient comparison is identity.
The next factor is Q of the termwise underived exchange. The defining
right-derived uniqueness isomorphism carries the bounded-below target unit to
the unbounded target unit; naturality carries the following target transport
through this isomorphism, leaving its inverse as the last factor. The inverse
exact pullback comparison maps to the unbounded inverse comparison. Full
faithfulness identifies the image of q'.inv with quotientCompQhIso.hom followed
by q.inv. Insert the canonical quotient comparisons on D and its direct image
to express these identities in the stated complex-level form. No target unit
is inverted, so no acyclicity of the pulled-back complex is assumed. -/
theorem injectiveExchange_target_transport {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    let M₁ := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let M : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :=
      ⟨M₁, ((InjectiveObject.ι _).mapCochainComplexPlus.obj J).property⟩
    let H := (HomotopyCategory.Plus.quotient _).obj M
    let q' : K ≅ DerivedCategory.Plus.Qh.obj H :=
      DerivedCategory.Plus.ι.preimageIso (Y := DerivedCategory.Plus.Q.obj M)
        (q ≪≫ (DerivedCategory.quotientCompQhIso _).symm.app M.obj)
    let R := lowerStar AddCommGrpCat.{v + 1} f
    let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
    let P := upperStar AddCommGrpCat.{v + 1}
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))
    let F := lowerStar AddCommGrpCat.{v + 1}
      (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
    let M₀ := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let L := (R.mapHomologicalComplex (.up ℤ)).obj M₀
    let D := (P.mapHomologicalComplex (.up ℤ)).obj M₀
    let T := P.mapDerivedCategoryPlus.obj K
    let sq := (IsPullback.of_hasPullback f
      (Scheme.strictHenselizationStructuralMap s)).toCommSq
    let a : (U.mapHomologicalComplex (.up ℤ)).obj L ⟶
        (F.mapHomologicalComplex (.up ℤ)).obj D :=
      (NatTrans.mapHomologicalComplex
      (baseChangeMap AddCommGrpCat.{v + 1} sq) (.up ℤ)).app M₀
    U.mapDerivedCategoryFactors.inv.app
      ((R.mapHomologicalComplex (.up ℤ)).obj M.obj) ≫
      DerivedCategory.Plus.ι.map
        (U.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj H) ≫
          DerivedCategory.Plus.Qh.map
            ((NatTrans.mapHomotopyCategoryPlus
              (baseChangeMap AddCommGrpCat.{v + 1} sq)).app H) ≫
          F.rightDerivedFunctorPlusUnit.app (P.mapHomotopyCategoryPlus.obj H) ≫
          F.rightDerivedFunctorPlus.map
            (P.mapDerivedCategoryPlusFactorsh.inv.app H ≫
              P.mapDerivedCategoryPlus.map q'.inv)) =
    DerivedCategory.Q.map a ≫
      (DerivedCategory.quotientCompQhIso _).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj D) ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj D) ≫
      F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).hom.app D) ≫
      F.rightDerivedFunctor.map
        (P.mapDerivedCategoryFactors.inv.app M₀ ≫ P.mapDerivedCategory.map q.inv) ≫
      F.rightDerivedFunctorPlusCompatibility.inv.app T := by sorry

end AlgebraicGeometry.Etale
