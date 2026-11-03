/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.UpperStarDerived
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp

/-! # The concrete finite native coefficient encoding of compact support

Source: prop-trf-exceptional-kunneth.proof.md, lisse paragraph, coefficient transport
through the same proper/open compactification.
(blueprint: lem-sf-etale-finite-support-encoding)

The coefficient object is the published continuousMapRingObj, in exactly the universe
of EtaleFiniteExceptionalDatum. The equivalences and their operation comparisons are
constructions, with no choice of witnesses from a mere existence theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

variable (A : Type) [CommRing A] [Finite A] [TopologicalSpace A]
  [DiscreteTopology A] [IsTopologicalRing A]

/-- The finite coefficient identification at the point is the specified
constant-function map, with its unique inverse, rather than an unspecified ring
isomorphism. Source: the finite coefficient-identification step
(blueprint: lem-sf-etale-finite-support-encoding). -/
def finiteEncodingPointRingIso :
    Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
        ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} A))) ≅
      Profinite.continuousMapRingObj.{u} A :=
  asIso (Profinite.constRingSheafToContinuousMapRingObj A)

/-- The point comparison respects the actual coefficient ring structures.
Source: the finite coefficient-identification step
(blueprint: lem-sf-etale-finite-support-encoding).
Proof: it is the existing monoidal constant-function comparison. -/
theorem finiteEncodingPointRingIso_isMonHom :
    IsMonHom (finiteEncodingPointRingIso.{u} A).hom := by
  change IsMonHom (Profinite.constRingSheafToContinuousMapRingObj A)
  infer_instance

/-- The specified point comparison fixes constant scalar sections.
Source: the finite coefficient-identification step
(blueprint: lem-sf-etale-finite-support-encoding).
Proof: apply the constant-section equation for the constant-function map. -/
theorem finiteEncodingPointRingIso_constant (a : A) :
    Sheaf.constRingSheafSection (coherentTopology Profinite.{u})
        (ULift.up a : ULift.{u + 1} A) ≫ (finiteEncodingPointRingIso A).hom =
      (Profinite.continuousMapConstRingHom.{u} A a).hom := by
  exact Profinite.constRingSheafSection_comp_constRingSheafToContinuousMapRingObj A a

/-- Derive the section-preserving proper direct-image comparison.
Source: finite coefficient transport (blueprint: lem-sf-etale-finite-support-encoding). -/
def finiteEncodingDerivedPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.lowerStar (Profinite.continuousMapRingObj A) f).rightDerivedFunctor ⋙
        (finiteCoefficientDerivedEquivalence Y A).functor ≅
      (finiteCoefficientDerivedEquivalence X A).functor ⋙
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).rightDerivedFunctor :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj A) f)
      (finiteCoefficientModEquivalence Y A).functor).symm ≪≫
    Functor.rightDerivedFunctorNatIso (lowerStarFiniteCoefficientModEquivalenceIso f A) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso
      (finiteCoefficientModEquivalence X A).functor
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)

/-- The open-extension mate of the fixed coefficient pullback comparison.
Source: finite coefficient transport (blueprint: lem-sf-etale-finite-support-encoding). -/
def finiteEncodingOpenShriek {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] :
    CondensedRing.openImmersionLowerShriek (Profinite.continuousMapRingObj A) j ⋙
        (finiteCoefficientModEquivalence Y A).functor ≅
      (finiteCoefficientModEquivalence X A).functor ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1} A)) j := by
  let EX := finiteCoefficientModEquivalence X A
  let EY := finiteCoefficientModEquivalence Y A
  let i := upperStarFiniteCoefficientModEquivalenceIso j A
  let k := Iso.isoCompInverse (H := EX) i ≪≫ Functor.associator _ _ _
  let kr := Iso.inverseCompIso (G := EY) k
  let a := (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
    (Profinite.continuousMapRingObj A) j).comp EY.toAdjunction
  let b := EX.toAdjunction.comp
    (openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)
  exact a.leftAdjointUniq (b.ofNatIsoRight kr.symm)

/-- Derive the exact open-extension comparison levelwise.
Source: finite coefficient transport (blueprint: lem-sf-etale-finite-support-encoding). -/
def finiteEncodingDerivedOpenShriek {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] :
    (CondensedRing.openImmersionLowerShriek
        (Profinite.continuousMapRingObj A) j).mapDerivedCategory ⋙
          (finiteCoefficientDerivedEquivalence Y A).functor ≅
      (finiteCoefficientDerivedEquivalence X A).functor ⋙
        (openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) j).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (finiteEncodingOpenShriek A j) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- The native finite-coefficient equivalence commutes with the support functor for
one fixed compactification. The proper comparison is the derived section-preserving
pushforward comparison. The open comparison is the mate of the actual pullback
comparison. Thus this construction uses the same two factors on both sides.

Source: lisse paragraph, coefficient-identification step of the étale comparison.
(blueprint: lem-sf-etale-finite-support-encoding)

Proof: derive the direct-image comparison through the exact coefficient equivalences,
which preserve K-injective complexes. The pullback comparison conjugates the two
open extension adjunctions, giving their left-adjoint uniqueness isomorphism. Derive
it levelwise, since open extension is exact. Whisker the proper comparison by the
native open factor and the open comparison by the ordinary proper factor. The three
associators identify their composite with the two compactification functors.
-/
def finiteEncodingCompactSupport {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.continuousMapRingObj A) c ⋙
          (finiteCoefficientDerivedEquivalence Y A).functor ≅
      (finiteCoefficientDerivedEquivalence X A).functor ⋙
        rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) c :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (finiteEncodingDerivedPushforward A c.g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (finiteEncodingDerivedOpenShriek A c.i) _ ≪≫
    Functor.associator _ _ _

/-- The finite open-extension comparison preserves the specified counit after
transporting the right adjoint by the fixed coefficient pullback comparison.
Source: finite coefficient transport, open counit normalization
(blueprint: lem-sf-etale-finite-support-encoding).

Proof: both composite adjunctions have the same right adjoint after the displayed
transport. The open comparison is their left-adjoint uniqueness isomorphism.
Apply the counit equation for that uniqueness isomorphism. -/
theorem finiteEncodingOpenShriek_counit {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] :
    let EX := finiteCoefficientModEquivalence X A
    let EY := finiteCoefficientModEquivalence Y A
    let i := upperStarFiniteCoefficientModEquivalenceIso j A
    let k := Iso.isoCompInverse (H := EX) i ≪≫ Functor.associator _ _ _
    let kr := Iso.inverseCompIso (G := EY) k
    let a := (CondensedRing.openImmersionLowerShriekUpperStarAdjunction
      (Profinite.continuousMapRingObj A) j).comp EY.toAdjunction
    let b := EX.toAdjunction.comp
      (openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} A)) j)
    Functor.whiskerLeft
        (EY.inverse ⋙ CondensedRing.upperStar (Profinite.continuousMapRingObj A) j)
        (finiteEncodingOpenShriek A j).hom ≫ (b.ofNatIsoRight kr.symm).counit =
      a.counit := by
  dsimp only
  exact Adjunction.leftAdjointUniq_hom_counit _ _

/-- The compact-support comparison is the proper comparison on the open extension,
followed by the proper direct image of the open comparison, as actual morphisms.
Source: finite coefficient transport, proper/open normalization
(blueprint: lem-sf-etale-finite-support-encoding).

Proof: evaluate the five factors in finiteEncodingCompactSupport. The associators
have identity components; removing these identities gives exactly the two factors.
-/
theorem finiteEncodingCompactSupport_hom_app {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X))) :
    (finiteEncodingCompactSupport A c).hom.app K =
      (finiteEncodingDerivedPushforward A c.g).hom.app
          ((CondensedRing.openImmersionLowerShriek
            (Profinite.continuousMapRingObj A) c.i).mapDerivedCategory.obj K) ≫
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) c.g).rightDerivedFunctor.map
          ((finiteEncodingDerivedOpenShriek A c.i).hom.app K) := by
  simp [finiteEncodingCompactSupport]

/-- The inverse compact-support comparison has the reverse proper/open formula.
This is the direction used when taking the exceptional base-change mate.
Source: finite coefficient transport, inverse exchange normalization
(blueprint: lem-sf-etale-finite-support-encoding).

Proof: evaluate the inverse five-factor composite. Its associators have identity
components, leaving the proper image of the inverse open comparison followed by
the inverse proper comparison. -/
theorem finiteEncodingCompactSupport_inv_app {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj A) X))) :
    (finiteEncodingCompactSupport A c).inv.app K =
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) c.g).rightDerivedFunctor.map
          ((finiteEncodingDerivedOpenShriek A c.i).inv.app K) ≫
        (finiteEncodingDerivedPushforward A c.g).inv.app
          ((CondensedRing.openImmersionLowerShriek
            (Profinite.continuousMapRingObj A) c.i).mapDerivedCategory.obj K) := by
  simp [finiteEncodingCompactSupport]

end AlgebraicGeometry.ProEtale
