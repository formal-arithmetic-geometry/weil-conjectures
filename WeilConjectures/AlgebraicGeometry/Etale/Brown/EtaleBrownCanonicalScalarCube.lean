/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Brown.EtaleBrownCanonicalRestrictionCube
import WeilConjectures.CategoryTheory.Adjunction.MateCube
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate

/-! # Scalar mate of the normalized Brown restriction cube

Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks 06YY and 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived
attribute [local instance] CoefficientSystemOrdinaryImage.inverseAdditive
  CoefficientSystemOrdinaryImage.rightAdditive
  CoefficientSystemOrdinaryImage.systemInverseAdditive
  CoefficientSystemOrdinaryImage.systemRightAdditive

set_option maxHeartbeats 1600000 in
-- Compare four independently normalized adjunctions.
/-- The scalar mate of the exact ordinary restriction square respects normalized
Brown inverse-image realizations.
Source: Zheng, Construction 4.1 and Lemma 5.16; Stacks 03CY, 06YY and 07A4.
(blueprint: lem-pur-etale-brown-canonical-scalar-cube).

Proof: first compare ordinary restriction and inverse image in the two coefficient
encodings. After forgetting to set sheaves, the ordinary restriction comparisons
are identities; the equation for A.restrictInverseUnderlying and the ordinary
Hom-transpose equations identify the two inverse-image composites on every
section. Faithfulness of the underlying functor gives the ordinary cube. Apply
termwise cochain prolongation and exact localization. The representative equations
for the canonical restriction model, the Brown restriction comparisons, and the
assumed inverse comparison identify all four localized faces; fully faithful
precomposition by Q therefore gives the restriction cube on all derived objects.
Take the scalar-adjunction inverse mates of that cube. The scalar normalization
of RV and RW identifies their inverse mates with the displayed scalar comparisons.
The geometric restriction/pullback comparison has inverse mate scalarPullbackIso
by its canonical normalization. The inverse-mate cube identity now gives the
ordered equation below, including the exact-to-left-derived pullback comparisons.
This calculation uses no properness, finiteness or invertibility of any proper
projection mate, and works for identity maps and zero coefficient rings. -/
theorem strictEtaleBrownCanonicalScalarCube
    (O : Type (u + 1)) [CommRing O] (t : O)
    {V W : Scheme.{u}} (g : V ⟶ W)
    (A : StrictEtaleOrdinaryImage O t g)
    (PW : StrictEtaleEvaluation W O t) (PV : StrictEtaleEvaluation V O t)
    (B : CoefficientSystemDerivedImage (J := W.smallEtaleTopology)
      (K := V.smallEtaleTopology) O t _ _ _ A PW PV)
    (RV : StrictEtaleBrownRealization O t V PV)
    (RW : StrictEtaleBrownRealization O t W PW)
    (rg : ∀ k, StrictEtaleBrownImageRealization O t g k A (B.level k) RV RW)
    (hinverse : ∀ k (K : CochainComplex (strictEtaleLevel W O t k) ℤ),
      letI : (strictEtaleBrownConstant O t V k).Additive := RV.val.ordinaryAdditive k
      letI : (strictEtaleBrownConstant O t W k).Additive := RW.val.ordinaryAdditive k
      letI : Functor.PreservesZeroMorphisms
          ((A.lift k).modules ⋙ strictEtaleBrownConstant O t V k) :=
        Functor.preservesZeroMorphisms_comp _ _
      (rg k).inverse.hom.app (DerivedCategory.Q.obj K) ≫
          (RV.derived k).map ((B.level k).inverseFactors.hom.app K) ≫
          (RV.factors k).hom.app
            (((A.lift k).modules.mapHomologicalComplex (.up ℤ)).obj K) =
        (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k))
          g).mapDerivedCategory.map ((RW.factors k).hom.app K) ≫
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t k))
            g).mapDerivedCategoryFactors.hom.app
            (((strictEtaleBrownConstant O t W k).mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex
              (strictEtaleBrownOrdinaryInverse O t g k A (B.level k) (rg k))
              (.up ℤ)).app K))
    {m n : ℕ} (h : m ≤ n) :
    let pn := (rg n).inverse.symm ≪≫ isoWhiskerLeft (RW.derived n)
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).symm
    let pm := (rg m).inverse.symm ≪≫ isoWhiskerLeft (RW.derived m)
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) g).symm
    let τ := ((mateEquiv (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj).symm
      (.mk _ _ _ _ (strictEtaleBrownCanonicalRestriction O t g A PW PV B h).hom))
    ∀ X : DerivedCategory (strictEtaleLevel W O t n),
      (Etale.scalarExtension (strictEtaleBrownRingMap O t h) V).map (pn.inv.app X) ≫
          (RV.scalar h).inv.app ((B.level n).inverse.obj X) ≫
          (RV.derived m).map (τ.app X) =
        (Etale.scalarPullbackIso (strictEtaleBrownRingMap O t h) g).inv.app
            ((RW.derived n).obj X) ≫
          (Etale.upperStar (ModuleCat.{u + 1} (strictEtaleBrownRing O t m))
            g).leftDerivedFunctor.map ((RW.scalar h).inv.app X) ≫
          pm.inv.app ((PW.scalar h).derived.obj X) := by
  dsimp only
  let an := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology (strictEtaleBrownRingMap O t h))
  let av := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars V.smallEtaleTopology (strictEtaleBrownRingMap O t h))
  let pn := (rg n).inverse.symm ≪≫ isoWhiskerLeft (RW.derived n)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t n)) g).symm
  let pm := (rg m).inverse.symm ≪≫ isoWhiskerLeft (RW.derived m)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (strictEtaleBrownRing O t m)) g).symm
  let δ := strictEtaleBrownCanonicalRestriction O t g A PW PV B h
  let τ := ((mateEquiv (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj).symm
    (.mk _ _ _ _ δ.hom))
  have ht : (mateEquiv (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj
      (.mk _ _ _ _ τ)) = δ.hom :=
    ((mateEquiv _ _).apply_symm_apply _)
  have hs : (mateEquiv an av (.mk _ _ _ _
      (Etale.scalarPullbackIso (strictEtaleBrownRingMap O t h) g).inv)) =
        (Etale.scalarRestrictionPullbackIso (strictEtaleBrownRingMap O t h) g).hom := by
    have he := congrArg Iso.inv
      (Etale.scalarPullback_eq (strictEtaleBrownRingMap O t h) g)
    change ((mateEquiv an av).symm (.mk _ _ _ _
      (Etale.scalarRestrictionPullbackIso (strictEtaleBrownRingMap O t h) g).hom)) =
        (Etale.scalarPullbackIso (strictEtaleBrownRingMap O t h) g).inv at he
    rw [← he]
    exact ((mateEquiv _ _).apply_symm_apply _)
  have hc := strictEtaleBrownCanonicalRestrictionCube O t g A PW PV B RV RW rg hinverse h
  intro Y
  apply mateEquiv_app_cube_converse (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj an av
    τ (Etale.scalarPullbackIso (strictEtaleBrownRingMap O t h) g).inv
    (RW.scalar h).inv (RV.scalar h).inv pn.inv pm.inv ?_ Y
  intro X
  change pn.inv.app _ ≫ (RV.derived n).map
      ((mateEquiv (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj
        (.mk _ _ _ _ τ)).app X) ≫
      (mateEquiv (PV.scalar h).derivedAdj av (.mk _ _ _ _ (RV.scalar h).inv)).app _ =
    _ ≫ (mateEquiv an av (.mk _ _ _ _
      (Etale.scalarPullbackIso (strictEtaleBrownRingMap O t h) g).inv)).app _ ≫ _
  rw [show (mateEquiv (PW.scalar h).derivedAdj (PV.scalar h).derivedAdj
      (.mk _ _ _ _ τ)) = .mk _ _ _ _ δ.hom from ht,
    show (mateEquiv (PV.scalar h).derivedAdj av (.mk _ _ _ _ (RV.scalar h).inv)) =
      .mk _ _ _ _ (RV.val.restriction h).hom from RV.property.2.2 h,
    show (mateEquiv (PW.scalar h).derivedAdj an (.mk _ _ _ _ (RW.scalar h).inv)) =
      .mk _ _ _ _ (RW.val.restriction h).hom from RW.property.2.2 h,
    show (mateEquiv an av (.mk _ _ _ _
      (Etale.scalarPullbackIso (strictEtaleBrownRingMap O t h) g).inv)) =
      .mk _ _ _ _ (Etale.scalarRestrictionPullbackIso
        (strictEtaleBrownRingMap O t h) g).hom from hs]
  exact hc X

end AlgebraicGeometry
