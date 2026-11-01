/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-! # Canonical finite-discrete compact-support encoding data

Source: latest blueprint det-def-sf-operations (iv), (vi), and the
sk-thm-sf-tensor-hom Complement; Stacks 03CY and 015F.
(blueprint: def-sf-finite-discrete-compact-support-encoding).

The five definitions expose the existing normalized construction as data. The
underived pushforward comparison is identity on additive sections. Its adjunction
mates give pullback and open extension; exact derivation and K-injective derivation
give the two derived comparisons. Their composite uses the same compactification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The canonical inverse-image comparison, obtained from the section-normalized direct-image
comparison by uniqueness of left adjoints.
Source: blueprint finite coefficient identification, steps 11--12; Stacks 015F and 03EK.
(blueprint: def-sf-finite-discrete-compact-support-encoding). -/
def encodingPullbackIso {T U : Scheme.{u}} (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) :
    CondensedRing.upperStar (coefficient A) f ⋙ (eU.ordinary.trans eU.fixed).functor ≅
      (eT.ordinary.trans eT.fixed).functor ⋙
        upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let R := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  let i : CondensedRing.lowerStar (coefficient A) f ⋙ ET.functor ≅ EU.functor ⋙ R :=
    encodingPushforwardNatIso A T U f eT eU
  let k := Iso.isoCompInverse (H := ET) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EU) k
  let a := ET.toAdjunction.comp
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
  let b := (CondensedRing.upperStarLowerStarAdjunction (coefficient A) f).comp
    EU.toAdjunction
  exact (a.leftAdjointUniq (b.ofNatIsoRight kr)).symm

/-- The canonical open-extension comparison, obtained by uniqueness of left adjoints to the
already identified restriction functors.
Source: blueprint finite coefficient identification, steps 11--12; Stacks 015F and 03EK.
(blueprint: def-sf-finite-discrete-compact-support-encoding). -/
def encodingOpenShriekIso {T U : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (eT : Encoding A T) (eU : Encoding A U) :
    CondensedRing.openImmersionLowerShriek (coefficient A) j ⋙
        (eT.ordinary.trans eT.fixed).functor ≅
      (eU.ordinary.trans eU.fixed).functor ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let i := encodingPullbackIso A j eT eU
  let k := Iso.isoCompInverse (H := EU) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := ET) k
  let a := (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
    (coefficient A) j).comp ET.toAdjunction
  let b := EU.toAdjunction.comp
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)
  exact a.leftAdjointUniq (b.ofNatIsoRight kr.symm)

/-- The K-injective derived direct-image comparison induced by the section-normalized underived
comparison.
Source: blueprint finite coefficient identification, steps 11--12; Stacks 015F and 03EK.
(blueprint: def-sf-finite-discrete-compact-support-encoding). -/
def encodingDerivedPushforwardIso {T U : Scheme.{u}} (f : U ⟶ T)
    (eT : Encoding A T) (eU : Encoding A U) :
    (CondensedRing.lowerStar (coefficient A) f).rightDerivedFunctor ⋙
        eT.fixedDerived.functor ≅
      eU.fixedDerived.functor ⋙
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).rightDerivedFunctor := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let F := CondensedRing.lowerStar (coefficient A) f
  let G := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f
  letI : ET.functor.Additive := inferInstanceAs
    (eT.ordinary.functor ⋙ eT.fixed.functor).Additive
  letI : EU.functor.Additive := inferInstanceAs
    (eU.ordinary.functor ⋙ eU.fixed.functor).Additive
  change F.rightDerivedFunctor ⋙ ET.functor.mapDerivedCategory ≅
    EU.functor.mapDerivedCategory ⋙ G.rightDerivedFunctor
  exact (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      F ET.functor).symm ≪≫
    Functor.rightDerivedFunctorNatIso (encodingPushforwardNatIso A T U f eT eU) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso EU.functor G

/-- The termwise derived comparison for the exact open-extension functors, induced by their
canonical underived comparison.
Source: blueprint finite coefficient identification, steps 11--12; Stacks 015F and 03EK.
(blueprint: def-sf-finite-discrete-compact-support-encoding). -/
def encodingDerivedOpenShriekIso {T U : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] (eT : Encoding A T) (eU : Encoding A U) :
    (CondensedRing.openImmersionLowerShriek (coefficient A) j).mapDerivedCategory ⋙
        eT.fixedDerived.functor ≅
      eU.fixedDerived.functor ⋙
        (openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).mapDerivedCategory := by
  let ET := eT.ordinary.trans eT.fixed
  let EU := eU.ordinary.trans eU.fixed
  let F := CondensedRing.openImmersionLowerShriek (coefficient A) j
  let G := openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j
  letI : ET.functor.Additive := inferInstanceAs
    (eT.ordinary.functor ⋙ eT.fixed.functor).Additive
  letI : EU.functor.Additive := inferInstanceAs
    (eU.ordinary.functor ⋙ eU.fixed.functor).Additive
  change F.mapDerivedCategory ⋙ ET.functor.mapDerivedCategory ≅
    EU.functor.mapDerivedCategory ⋙ G.mapDerivedCategory
  exact (Functor.mapDerivedCategoryCompIso F ET.functor).symm ≪≫
    Functor.mapDerivedCategoryNatIso (encodingOpenShriekIso A j eT eU) ≪≫
    Functor.mapDerivedCategoryCompIso EU.functor G

/-- The explicit canonical compactification comparison, made available as data.
The composite is specified directly: reassociate, compare
derived direct image on K-injective representatives, compare exact extension by zero,
and reassociate. No isomorphism is selected from the theorem's `Nonempty` conclusion.
Source: blueprint coefficient identification, steps 11--12; Stacks 015F and 03EK.
(blueprint: def-sf-finite-discrete-compact-support-encoding). -/
def encodingCompactificationIso
    (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    CondensedRing.rightDerivedLowerShriekOfCompactification (coefficient A) c ⋙
        (E Y).fixedDerived.functor ≅
      (E X).fixedDerived.functor ⋙
        rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (encodingDerivedPushforwardIso A c.g (E Y) (E c.Z)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (encodingDerivedOpenShriekIso A c.i (E c.Z) (E X)) _ ≪≫
    Functor.associator _ _ _


end AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary
