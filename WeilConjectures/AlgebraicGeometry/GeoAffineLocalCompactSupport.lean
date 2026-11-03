/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GeoAffineLocalTransport
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceAmbientAdjunctionCore
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal

/-!
# Classical compact support and exceptional adjunctions

Source: the finite-comparison transport in the opening step and clause (2) of
`sk-lem-geo-affine-local`.
(blueprint: lem-geo-affine-local-compact-support-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory Limits AlgebraicGeometry Scheme

namespace AlgebraicGeometry.ProEtale

/-- Compare the two compactification composites on all unbounded finite-coefficient objects.
Source: the opening comparison step of `sk-lem-geo-affine-local`
(blueprint: lem-geo-affine-local-compact-support-transport).

Proof: give the proper compactifying scheme its structure over k. Properness and finite
type of the base make it finite type and quasi-compact over k. The canonical unbounded
proper-direct-image mate is invertible by finite comparison. Compose its inverse with
the derived comparison of exact open extension. Both sides are the compactification
composite Rp_*D(j_!), without a boundedness restriction. -/
theorem nonempty_classicalCompactSupportNative
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (hEll : IsUnit (algebraMap ℤ k (ell : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, (ell : A) ^ n = 0)
    {P S : Scheme.{u}} [S.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (S ↘ Spec (CommRingCat.of k))]
    {f : P ⟶ S} (c : Compactification f) :
    Nonempty (Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) P).mapDerivedCategory ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c) := by
  let : c.Z.Over (Spec (CommRingCat.of k)) := ⟨c.g ≫ (S ↘ Spec (CommRingCat.of k))⟩
  have := c.isProper
  have : LocallyOfFiniteType (c.Z ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType (c.g ≫ (S ↘ Spec (CommRingCat.of k))))
  have : QuasiCompact (c.Z ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (QuasiCompact (c.g ≫ (S ↘ Spec (CommRingCat.of k))))
  let B := ModuleCat.{u + 1} A
  let t : (Etale.lowerStar B c.g).rightDerivedFunctor ⋙
        (comparisonUpperStar B S).mapDerivedCategory ⟶
      (comparisonUpperStar B c.Z).mapDerivedCategory ⋙
        (ProEtale.lowerStar B c.g).rightDerivedFunctor :=
    { app := unboundedDirectImageComparisonMap A c.g
      naturality := fun _ _ h ↦ unboundedDirectImageComparisonMap_naturality A c.g h }
  have ht (K : EtaleD c.Z A) : IsIso (t.app K) :=
    unboundedDirectImageComparison k hbase hEll A hA c.g K
  have : ∀ K, IsIso (t.app K) := ht
  have : IsIso t := NatIso.isIso_of_isIso_app t
  let o : (Etale.openImmersionLowerShriek B c.i).mapDerivedCategory ⋙
        (comparisonUpperStar B c.Z).mapDerivedCategory ≅
      (comparisonUpperStar B P).mapDerivedCategory ⋙
        (ProEtale.openImmersionLowerShriek B c.i).mapDerivedCategory :=
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.mapDerivedCategoryNatIso (openImmersionLowerShriekComparisonUpperStarIso B c.i) ≪≫
      Functor.mapDerivedCategoryCompIso _ _
  exact ⟨Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (asIso t) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight o _ ≪≫
    Functor.associator _ _ _⟩

/-- Every specified compactification admits a classical exceptional adjunction with its
native compact-support formula and counit-normalized uniqueness.
Source: the opening existence step in clause (2)
(blueprint: lem-geo-affine-local-compact-support-transport).

Proof: apply the ordinary unbounded exceptional-adjoint existence theorem. Compose the
adjunction with the inverse source and forward target equivalences. The compact-support
comparison just proved identifies the left functor with the native pro-etale functor.
The right-adjoint Hom bijection proves the normalized uniqueness field. -/
theorem nonempty_classicalExceptionalData
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (hEll : IsUnit (algebraMap ℤ k (ell : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ n : ℕ, (ell : A) ^ n = 0)
    {P S : Scheme.{u}} [S.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (S ↘ Spec (CommRingCat.of k))]
    {f : P ⟶ S} (c : Compactification f)
    (CP : ClassicalComparisonData P A) (CS : ClassicalComparisonData S A) :
    Nonempty (ClassicalExceptionalAdjunctionData P S A f c CP CS
      (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)) := by
  obtain ⟨e⟩ := nonempty_classicalCompactSupportNative ell k hbase hEll A hA c
  have := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  exact ⟨classicalExceptionalDataOfAdjunction c CP CS _ (Adjunction.ofIsLeftAdjoint _) e⟩

/-- Exact etale extension, expressed by the specified compactification and conjugated
through the finite classical equivalences.
Source: clause (2), the first two Hom bijections
(blueprint: lem-geo-affine-local-compact-support-transport). -/
def classicalEtaleSumDataOfNative
    {U X : Scheme.{u}} {A : Type (u + 1)} [CommRing A] [Finite A]
    (g : U ⟶ X) [Etale g] [IsSeparated g] [QuasiCompact g]
    (c : Compactification g) (CU : ClassicalComparisonData U A)
    (CX : ClassicalComparisonData X A)
    (e : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c) :
    ClassicalEtaleSumData U X A g c CU CX where
  left := CU.equivalence.inverse ⋙
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
      CX.equivalence.functor
  right := CX.equivalence.inverse ⋙
    (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙ CU.equivalence.functor
  adjunction :=
    let a := (Etale.derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A)
      g inferInstance).ofNatIsoLeft (Etale.canonicalEtaleCompactSupportComparison A g c).symm
    ((((CU.equivalence.symm.toAdjunction.comp a).comp CX.equivalence.toAdjunction).ofNatIsoLeft
      (eqToIso rfl)).ofNatIsoRight (eqToIso rfl))
  right_eq := rfl
  left_native := classicalTransportNative CU CX _ _ e
  right_native := (classicalUpperStarDataOfComparison CU CX g).ambient

/-- The ordinary affine purity functor has precisely the native pro-etale formula.
Source: clause (1), transport through the finite classical comparison
(blueprint: lem-geo-affine-local-compact-support-transport).

Proof: the exact comparison commutes with pullback. Its derived tensor comparison
commutes with tensoring by the finite Tate complex, using the braiding to express tensor
on the right. Finally the comparison commutes with shifts. Pasting these three squares
identifies the displayed ordinary and native pullback-twist-shift functors. -/
theorem nonempty_classicalAffineRightNative
    (P S : Scheme.{u}) (f : P ⟶ S)
    (A : Type (u + 1)) [CommRing A] [Finite A] (ell r d : ℕ)
    (hA : ((ell ^ r : ℕ) : A) = 0) :
    Nonempty (etaleAffineRight P S f A ell r d hA ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) P).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory ⋙
        nativeAffineRight P S f A ell r d hA) := by
  let B := ModuleCat.{u + 1} A
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory (Sheaf P.smallEtaleTopology B)
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory (Sheaf (Scheme.ProEt.topology P) B)
  let V := (comparisonUpperStar B P).mapDerivedCategory
  let K := (DerivedCategory.singleFunctor _ 0).obj
    (Scheme.finiteEtaleTateTwist P (ell ^ r) A hA d)
  let te : Etale.derivedTensorRight B P K ⋙ V ≅ V ⋙ derivedTensorRight P A (V.obj K) :=
    Functor.isoWhiskerRight (BraidedCategory.tensorLeftIsoTensorRight K).symm V ≪≫
      derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso B K ≪≫
      Functor.isoWhiskerLeft V (BraidedCategory.tensorLeftIsoTensorRight (V.obj K))
  let pe := Functor.isoWhiskerRight
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory B f) V ≪≫
    (unboundedDirectImagePullbackIso A f).symm
  exact ⟨Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _
      (Functor.isoWhiskerLeft _ (V.commShiftIso (2 * (d : ℤ)))) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight te _) ≪≫
    Functor.isoWhiskerLeft _ (Functor.associator _ _ _) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight pe _ ≪≫ Functor.associator _ _ _⟩

/-- Transport an ordinary affine adjunction with the specified native comparisons.
Source: clause (1), finite classical comparison
(blueprint: lem-geo-affine-local-compact-support-transport). -/
def classicalAffineDataOfAdjunction
    {P S : Scheme.{u}} {A : Type (u + 1)} [CommRing A]
    {f : P ⟶ S} (c : Compactification f) (ell r d : ℕ)
    (hA : ((ell ^ r : ℕ) : A) = 0)
    (CP : ClassicalComparisonData P A) (CS : ClassicalComparisonData S A)
    (a : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣
      etaleAffineRight P S f A ell r d hA)
    (left : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) P).mapDerivedCategory ⋙
        ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
    (right : etaleAffineRight P S f A ell r d hA ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) P).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory ⋙
        nativeAffineRight P S f A ell r d hA) :
    ClassicalAffineAdjunctionData P S A f c ell r d hA CP CS
      (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
      (nativeAffineRight P S f A ell r d hA) where
  left := CP.equivalence.inverse ⋙
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
      CS.equivalence.functor
  right := CS.equivalence.inverse ⋙
    etaleAffineRight P S f A ell r d hA ⋙ CP.equivalence.functor
  adjunction := (CP.equivalence.symm.toAdjunction.comp a).comp CS.equivalence.toAdjunction
  left_native := rfl
  right_native := rfl
  left_eq := rfl
  left_etale := classicalTransportModel CP CS _ _ rfl
  left_etale_normalization := rfl
  right_eq := rfl
  right_etale := classicalTransportModel CS CP _ _ rfl
  right_etale_normalization := rfl
  left_formula := classicalTransportNative CP CS _ _ left
  right_formula := classicalTransportNative CS CP _ _ right

/-- The four-Hom comparison using precisely the specified compact-support compositor.
Source: clause (2), last Hom bijection and counit-preserving Yoneda identification
(blueprint: lem-geo-affine-local-compact-support-transport). -/
def classicalCanonicalCompositeOfSum
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X S : Scheme.{u}} (g : U ⟶ X) (f : X ⟶ S)
    [Etale g] [IsSeparated g] [QuasiCompact g] [QuasiCompact f]
    (c : Compactification f) (cu : Compactification (g ≫ f)) (cx : Compactification g)
    (CU : ClassicalComparisonData U A) (CX : ClassicalComparisonData X A)
    (CS : ClassicalComparisonData S A)
    (F : ProEtaleD X A ⥤ ProEtaleD S A) (FU : ProEtaleD U A ⥤ ProEtaleD S A)
    (a : ClassicalExceptionalAdjunctionData X S A f c CX CS F)
    (au : ClassicalExceptionalAdjunctionData U S A (g ≫ f) cu CU CS FU)
    (sum : ClassicalEtaleSumData U X A g cx CU CX)
    (hsum : sum.left = CU.equivalence.inverse ⋙
      Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cx ⋙
        CX.equivalence.functor)
    (hadj : sum.adjunction =
      let ordinaryAdj :=
        (Etale.derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) g
          inferInstance).ofNatIsoLeft (Etale.canonicalEtaleCompactSupportComparison A g cx).symm
      ((((CU.equivalence.symm.toAdjunction.comp ordinaryAdj).comp
        CX.equivalence.toAdjunction).ofNatIsoLeft (eqToIso hsum.symm)).ofNatIsoRight
          (eqToIso sum.right_eq.symm))) :
    ClassicalCanonicalComposite A g f c cu cx CU CX CS F FU a au sum := by
  let st := classicalTransportModel CU CX _ sum.left hsum
  let t : CU.equivalence.functor ⋙ (sum.left ⋙ a.left) ≅
      CU.equivalence.functor ⋙ au.left :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight st _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ a.left_etale ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (classicalCompactSupportCompositor A g f cx c cu) _ ≪≫
      au.left_etale.symm
  let W := (Functor.whiskeringLeft (EtaleD U A) (ClassicalD U A) (ClassicalD S A)).obj
    CU.equivalence.functor
  let e : sum.left ⋙ a.left ≅ au.left := W.preimageIso t
  refine
    { sum_eq := hsum
      sum_etale := st
      sum_normalization := rfl
      sum_adjunction_normalization := hadj
      comparison := classicalCompositeComparisonOfIso a.adjunction au.adjunction sum.adjunction e
      compact_support_normalization := ?_ }
  intro K
  change (W.map (W.preimage t.hom)).app K = _
  rw [W.map_preimage]
  simp only [t, st, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp]
  exact Category.id_comp _

/-- Descend the canonical derived upper-star compositor through the classical equivalences.
Source: clause (2), further etale localization
(blueprint: lem-geo-affine-local-compact-support-transport).

Proof: precompose with the fully faithful source equivalence. Paste the three normalized
pullback models with the inverse ordinary upper-star compositor, and lift this isomorphism
through precomposition. Its component formula is the defining formula for that lift. -/
def classicalUpperStarCompositor
    (A : Type (u + 1)) [CommRing A]
    {V U X : Scheme.{u}} (v : V ⟶ U) (g : U ⟶ X)
    (cx : Compactification g) (cV : Compactification v)
    (cVU : Compactification (v ≫ g))
    (CX : ClassicalComparisonData X A) (CU : ClassicalComparisonData U A)
    (CV : ClassicalComparisonData V A)
    (sumU : ClassicalEtaleSumData U X A g cx CU CX)
    (sumV : ClassicalEtaleSumData V U A v cV CV CU)
    (sumVU : ClassicalEtaleSumData V X A (v ≫ g) cVU CV CX) :
    sumU.right ⋙ sumV.right ≅ sumVU.right :=
  let t : CX.equivalence.functor ⋙ (sumU.right ⋙ sumV.right) ≅
      CX.equivalence.functor ⋙ sumVU.right :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (sumU.pullbackModel sumU.right_eq) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (sumV.pullbackModel sumV.right_eq) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Etale.unboundedEtaleUpperStarCompIso A v g).symm _ ≪≫
      (sumVU.pullbackModel sumVU.right_eq).symm
  let W := (Functor.whiskeringLeft (EtaleD X A) (ClassicalD X A) (ClassicalD V A)).obj
    CX.equivalence.functor
  W.preimageIso t

/-- The descended compositor has the required component normalization.
Source: clause (2), canonical inverse-image composition
(blueprint: lem-geo-affine-local-compact-support-transport). -/
theorem classicalUpperStarCompositor_normalization
    (A : Type (u + 1)) [CommRing A]
    {V U X : Scheme.{u}} (v : V ⟶ U) (g : U ⟶ X)
    (cx : Compactification g) (cV : Compactification v)
    (cVU : Compactification (v ≫ g))
    (CX : ClassicalComparisonData X A) (CU : ClassicalComparisonData U A)
    (CV : ClassicalComparisonData V A)
    (sumU : ClassicalEtaleSumData U X A g cx CU CX)
    (sumV : ClassicalEtaleSumData V U A v cV CV CU)
    (sumVU : ClassicalEtaleSumData V X A (v ≫ g) cVU CV CX) (K : EtaleD X A) :
    (classicalUpperStarCompositor A v g cx cV cVU CX CU CV sumU sumV sumVU).hom.app
        (CX.equivalence.functor.obj K) =
      sumV.right.map ((sumU.pullbackModel sumU.right_eq).hom.app K) ≫
        (sumV.pullbackModel sumV.right_eq).hom.app
          ((Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory.obj K) ≫
        CV.equivalence.functor.map
          ((Etale.unboundedEtaleUpperStarCompIso A v g).inv.app K) ≫
        (sumVU.pullbackModel sumVU.right_eq).inv.app K := by
  unfold classicalUpperStarCompositor
  let W := (Functor.whiskeringLeft (EtaleD X A) (ClassicalD X A) (ClassicalD V A)).obj
    CX.equivalence.functor
  change (W.map (W.preimage _)).app K = _
  rw [W.map_preimage]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp]
  exact Category.id_comp _

/-- The affine adjunction itself, before the additional base-change normalizations.
Source: clause (1), the projective-line/open-chart induction
(blueprint: lem-geo-affine-local-compact-support-transport).

Proof: use the ordinary affine-space adjunction constructed by iterating the projective-line
trace and open-chart adjunctions. Replace exact derived pullback by its left-derived model
using the canonical comparison. The left native square and the right tensor/pullback/shift
square give the two native formulas after conjugation by the classical equivalences. -/
theorem nonempty_classicalAffineData
    (ell : ℕ) [Fact ell.Prime]
    (k : Type u) [Field k] (hbase : Finite k ∨ IsAlgClosed k)
    (hEll : IsUnit (algebraMap ℤ k (ell : ℤ)))
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (r : ℕ) (hpos : 0 < ell ^ r) (hA : ((ell ^ r : ℕ) : A) = 0)
    (S : Scheme.{u}) [S.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (S ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (S ↘ Spec (CommRingCat.of k))]
    [IsNoetherian S] (hS : IsUnit (((ell ^ r : ℕ) : Γ(S, ⊤)))) (d : ℕ)
    (CS : ClassicalComparisonData S A)
    (CP : ClassicalComparisonData (AffineSpace (ULift.{u} (Fin d)) S) A)
    (c : Compactification (AffineSpace (ULift.{u} (Fin d)) S ↘ S)) :
    Nonempty (ClassicalAffineAdjunctionData (AffineSpace (ULift.{u} (Fin d)) S) S A
      (AffineSpace (ULift.{u} (Fin d)) S ↘ S) c ell r d hA CP CS
      (ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c)
      (nativeAffineRight (AffineSpace (ULift.{u} (Fin d)) S) S
        (AffineSpace (ULift.{u} (Fin d)) S ↘ S) A ell r d hA)) := by
  let P := AffineSpace (ULift.{u} (Fin d)) S
  let f : P ⟶ S := P ↘ S
  obtain ⟨a⟩ := Etale.affineSpaceAmbientAdjunction_of_compactification
    (ell ^ r) hpos A hA S hS d c
  let a' : Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣
      etaleAffineRight P S f A ell r d hA :=
    a.ofNatIsoRight (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerRight
        (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm _)
  obtain ⟨left⟩ := nonempty_classicalCompactSupportNative ell k hbase hEll A
    ⟨r, by simpa only [Nat.cast_pow] using hA⟩ c
  obtain ⟨right⟩ := nonempty_classicalAffineRightNative P S f A ell r d hA
  exact ⟨classicalAffineDataOfAdjunction c ell r d hA CP CS a' left right⟩

end AlgebraicGeometry.ProEtale
