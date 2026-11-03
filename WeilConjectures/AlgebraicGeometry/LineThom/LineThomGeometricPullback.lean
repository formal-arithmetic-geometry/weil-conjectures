/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RankOneDivisorClassIntegral
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOpenProper.CondensedOpenProperPasting

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.RightDerivedSingleCounit
import WeilConjectures.AlgebraicGeometry.AffineSpace.ZeroSectionComplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Geometric pullback of the line Thom arrow

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Steps 1--2
(blueprint: lem-pur-line-thom-geometric-pullback).
The global class is the reviewed divisor class through supported Hom. The fibre
class is independently the coordinate Kummer boundary in the same coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.Admissible
namespace AlgebraicGeometry.ProEtale.LineThom

/-- Equality in the normalized full comparison is equality of the retained etale arrows.
This applies to the two compact-support expressions in the geometric equation,
using their specified finite etale antecedents and comparison isomorphisms.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Step 2, retained finite etale arrows
(blueprint: lem-pur-line-thom-geometric-pullback).
Proof: cancel the two specified comparison isomorphisms from the displayed
identity. Comparison inverse image is fully faithful on bounded-below etale
complexes, so its map on the Hom set is injective. Apply that injectivity to the
actual arrows. This never replaces an antecedent by a different preimage and
never tests only induced cohomology maps. -/
theorem retained_finite_arrow_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    (S : Scheme.{u})
    {K L : DerivedCategory.Plus (Sheaf (ProEt.topology S) (ModuleCat.{u + 1} A))}
    (wK : Scheme.FixedEtaleOriginWitness S A K)
    (wL : Scheme.FixedEtaleOriginWitness S A L)
    (f g : wK.complex.obj ⟶ wL.complex.obj)
    (h : wK.iso.inv ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.map f ≫
          wL.iso.hom =
      wK.iso.inv ≫
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory.map g ≫
          wL.iso.hom) : f = g := by
  apply (ProEtale.bijective_comparisonUpperStar_mapDerivedCategory_map
    (A := ModuleCat.{u + 1} A) wK.complex.obj wL.complex.obj wL.complex.property).injective
  apply (cancel_epi wK.iso.inv).mp
  apply (cancel_mono wL.iso.hom).mp
  simpa only [Category.assoc] using h

/-- Closed derived pushforward has its usual supported right adjoint.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Step 2, the closed adjunction
(blueprint: lem-pur-line-thom-geometric-pullback).
Proof: closed extension is exact and fully faithful. The right adjoint is the
derived functor of sections with support, obtained from the localization triangle
for the complementary open. Its universal property gives the adjunction on the
full ordinary derived category. This construction needs no purity isomorphism. -/
theorem closedPush_isLeftAdjoint (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    [QuasiCompact i.openComplement.ι] :
    (moduleObjectDerivedPushforward Λ.X i).IsLeftAdjoint := by
  let j := i.openComplement.ι
  have hij : Set.range i.base = (Set.range j.base)ᶜ := by
    exact i.range_eq_compl_range_openComplement_ι
  let _ := closedSupport_lowerStarExact Λ.X i j hij
  have : (CondensedRing.lowerStar Λ.X i).mapDerivedCategory.IsLeftAdjoint :=
    (closedSupportDerivedAdjunction Λ.X i j hij).isLeftAdjoint
  exact Functor.isLeftAdjoint_of_iso
    (CondensedRing.lowerStar Λ.X i).rightDerivedFunctorIsoMapDerivedCategory.symm

/-- Ri! is fixed by the right-adjoint universal property of actual closed pushforward.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Step 2 (blueprint: lem-pur-line-thom-geometric-pullback). -/
def closedExceptional (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    [QuasiCompact i.openComplement.ι] :=
  letI := closedPush_isLeftAdjoint Λ i
  (moduleObjectDerivedPushforward Λ.X i).rightAdjoint

/-- The chosen right adjoint comes with its defining adjunction.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Step 2 (blueprint: lem-pur-line-thom-geometric-pullback). -/
def closedAdjunction (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    [QuasiCompact i.openComplement.ι] :
    moduleObjectDerivedPushforward Λ.X i ⊣ closedExceptional Λ i :=
  letI := closedPush_isLeftAdjoint Λ i
  Adjunction.ofIsLeftAdjoint _

/-- Exact closed pushforward identifies its single object with total pushforward.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
thm-pur-rank-one-thom.proof.md, proper-section normalization, Step 1
(blueprint: lem-pur-line-thom-geometric-pullback).
Proof: closed direct image is exact for the pulled-back coefficients; apply its
exact-to-derived comparison. The specified closedSingleMap is this comparison
because both are adjoint to the ordinary closed counit. -/
theorem closedSingleMap_isIso (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    [LocallyOfFinitePresentation i] :
    IsIso (closedSingleMap Λ i) := by
  let _ := CondensedRing.preservesFiniteColimits_lowerStar_of_isFinite Λ.X i
  let L := CondensedRing.upperStar Λ.X i
  let R := CondensedRing.lowerStar Λ.X i
  let a := CondensedRing.upperStarLowerStarAdjunction Λ.X i
  let ad := a.derivedAdjunction.ofNatIsoLeft L.leftDerivedFunctorIsoMapDerivedCategory
  have h := a.single_rightDerived_counit (unit Λ D)
  have hm : closedSingleMap Λ i =
      ad.homEquiv _ _ ((L.mapDerivedCategorySingleFunctor 0).hom.app _ ≫
        (DerivedCategory.singleFunctor _ 0).map (a.counit.app (unit Λ D))) := by
    simp only [ad, Adjunction.homEquiv_ofNatIsoLeft_apply, closedSingleMap,
      CondensedRing.derivedUpperStarLowerStarAdjunction,
      CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory]
    rfl
  have he : closedSingleMap Λ i = R.singleRightDerivedUnit.app (unit Λ D) := by
    rw [hm]
    apply (ad.homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    exact h.symm
  rw [he, Functor.singleRightDerivedUnit_app]
  infer_instance

/-- The proper-section map on an arbitrary full derived object, not only on the unit.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
thm-pur-rank-one-thom.proof.md, proper-section composition in Step 1
(blueprint: lem-pur-line-thom-geometric-pullback). -/
def sectionMap (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {T S : Scheme.{u}} {f : T ⟶ S} (i : S ⟶ T)
    (h : i ≫ f = 𝟙 S) (c : Compactification f) (N : DerivedCategory (Modules Λ S)) :=
  supportToOrdinary Λ c ((moduleObjectDerivedPushforward Λ.X i).obj N) ≫
    (rightDerivedLowerStarComp Λ.X i f).hom.app N ≫
    (Functor.rightDerivedFunctorNatIso (CondensedRing.lowerStarCongr Λ.X h)).hom.app N ≫
    (CondensedOpenProper.rId Λ.X S).hom.app N

/-- The canonical section map is invertible by proper support and composition.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
thm-pur-rank-one-thom.proof.md, proper-section composition in Step 1
(blueprint: lem-pur-line-thom-geometric-pullback).
Proof: the closed section is proper. Its direct image has support proper over S,
so forgetting compact support is invertible. The remaining factors are the fixed
direct-image compositor, section identity and identity-functor comparison. -/
theorem sectionMap_isIso (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {T S : Scheme.{u}} {f : T ⟶ S}
    (i : S ⟶ T) [IsClosedImmersion i] (h : i ≫ f = 𝟙 S)
    (c : Compactification f) (N : DerivedCategory (Modules Λ S)) :
    IsIso (sectionMap Λ i h c N) := by
  sorry

/-- Sigma is the isomorphism of the specified proper-section map.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Step 1 (blueprint: lem-pur-line-thom-geometric-pullback). -/
def sigma (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {T S : Scheme.{u}} {f : T ⟶ S}
    (i : S ⟶ T) [IsClosedImmersion i] (h : i ≫ f = 𝟙 S)
    (c : Compactification f) (N : DerivedCategory (Modules Λ S)) :=
  letI := sectionMap_isIso Λ i h c N
  asIso (sectionMap Λ i h c N)

/-- The coordinate set on the one-dimensional affine space is its singleton coordinate.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Step 2, the coordinate of the framed geometric fibre.
Proof: ULift (Fin 1) has one element, so every coordinate has that index.
(blueprint: lem-pur-line-thom-geometric-pullback). -/
theorem coordinate_range (S : Scheme.{u}) :
    Set.range (AffineSpace.coord (n := ULift.{u} (Fin 1)) S) =
      {AffineSpace.coord S (ULift.up 0 : ULift.{u} (Fin 1))} := by
  ext t
  constructor
  · rintro ⟨j, rfl⟩
    have hj : j = (ULift.up 0 : ULift.{u} (Fin 1)) := Subsingleton.elim _ _
    simp only [hj, Set.mem_singleton_iff]
  · intro ht
    exact ⟨ULift.up 0, Set.mem_singleton_iff.mp ht |>.symm⟩

/-- The existing scheme isomorphism identifies the origin with the coordinate zero locus.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Step 2 (blueprint: lem-pur-line-thom-geometric-pullback). -/
def originIso (S : Scheme.{u}) :=
  AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) S (coordinate_range S)

/-- The inverse zero-locus identification commutes with its closed inclusion.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Step 2, origin as the zero divisor of the coordinate.
Proof: compose the existing hom/inclusion equation with the inverse isomorphism
and cancel its hom-inverse identity.
(blueprint: lem-pur-line-thom-geometric-pullback). -/
theorem originIso_inv_comp (S : Scheme.{u}) :
    (originIso S).inv ≫ AffineSpace.zeroSection (ULift.{u} (Fin 1)) S =
      (AffineSpace (ULift.{u} (Fin 1)) S).zeroLocusSubschemeι
        {AffineSpace.coord S (ULift.up 0 : ULift.{u} (Fin 1))} := by
  rw [← AffineSpace.zeroSectionIsoZeroLocusSubscheme_hom_zeroLocusSubschemeι
    (ULift.{u} (Fin 1)) S (coordinate_range S)]
  simp only [originIso, Iso.inv_hom_id_assoc]

/-- The origin is of finite presentation over the affine line, over any base.
Source: rank-one Thom, Step 2, the coordinate origin
(blueprint: lem-pur-line-thom-geometric-pullback).
Proof: its composite with the finite-type line projection is the identity.
Cancellation for locally finitely presented morphisms gives the assertion. -/
instance origin_locallyOfFinitePresentation (S : Scheme.{u}) :
    LocallyOfFinitePresentation (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S) := by
  have : LocallyOfFinitePresentation
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S ≫
        AffineSpace (ULift.{u} (Fin 1)) S ↘ S) := by
    rw [AffineSpace.zeroSection_over]
    infer_instance
  exact locallyOfFinitePresentation_of_comp
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)

/-- The complement of the origin is a principal open, hence quasi-compact over the line.
Source: rank-one Thom, Step 2, the coordinate origin
(blueprint: lem-pur-line-thom-geometric-pullback).
Proof: the zero section has exactly the coordinate zero locus as its range. There is
one coordinate, so its complement is the coordinate basic open; that inclusion is affine.
This works over arbitrary bases, including nonreduced and empty schemes. -/
instance origin_complement_quasiCompact (S : Scheme.{u}) :
    QuasiCompact (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S).openComplement.ι := by
  have he : (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S).openComplement =
      (AffineSpace (ULift.{u} (Fin 1)) S).basicOpen
        (AffineSpace.coord S (ULift.up 0 : ULift.{u} (Fin 1))) := by
    apply SetLike.coe_injective
    rw [Scheme.Hom.coe_openComplement, AffineSpace.compl_range_zeroSection]
  rw [he]
  infer_instance

/-- The fibre arrow is the actual positive coordinate Kummer boundary, transported
along the canonical zero-locus/origin identification and exact closed comparison.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Step 2 (blueprint: lem-pur-line-thom-geometric-pullback). -/
def fibreClass (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (S : Scheme.{u}) (b : S ⟶ Spec (CommRingCat.of P.field.k)) :=
  let X := AffineSpace (ULift.{u} (Fin 1)) S
  let i := AffineSpace.zeroSection (ULift.{u} (Fin 1)) S
  let t := AffineSpace.coord S (ULift.up 0 : ULift.{u} (Fin 1))
  letI := closedSingleMap_isIso Λ i
  (asIso (closedSingleMap Λ i)).inv ≫
    (DerivedCategory.singleFunctor _ 0).map
      (supportRestriction Λ (X.zeroLocusSubschemeι {t}) i
        (originIso S).inv (originIso_inv_comp S)) ≫
    principalBoundary P Λ hΛ X ((X ↘ S) ≫ b) t

/-- Alpha is exactly the adjunct of the independently defined fibre boundary.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Step 2 (blueprint: lem-pur-line-thom-geometric-pullback). -/
def alpha (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (S : Scheme.{u}) (b : S ⟶ Spec (CommRingCat.of P.field.k)) :=
  (closedAdjunction Λ (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).homEquiv _ _
    (fibreClass P Λ hΛ S b)

/-- u is compact support of the actual closed counit, preceded by proper-section sigma.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Step 2 (blueprint: lem-pur-line-thom-geometric-pullback). -/
def compactCounit (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {T S : Scheme.{u}} {a : T ⟶ S} (i : S ⟶ T) [IsClosedImmersion i]
    [QuasiCompact i.openComplement.ι]
    (hi : i ≫ a = 𝟙 S) (c : Compactification a)
    (M : DerivedCategory (Admissible.Modules Λ T)) :=
  (sigma Λ i hi c ((closedExceptional Λ i).obj M)).inv ≫
    (CondensedRing.rightDerivedLowerShriekOfCompactification Λ.X c).map
      ((closedAdjunction Λ i).counit.app M)

/-- Beta is the canonical compact exchange followed by the existing twist pullback.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Step 2 (blueprint: lem-pur-line-thom-geometric-pullback). -/
def beta (P : WeilConjectures.PurityFiniteSetting.{u})
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    {V B X S : Scheme.{u}} {π : V ⟶ B} {a : X ⟶ S}
    {v : X ⟶ V} {b : S ⟶ B} (sq : IsPullback v a π b)
    (c : Compactification π)
    (aV : V ⟶ Spec (CommRingCat.of P.field.k))
    (aX : X ⟶ Spec (CommRingCat.of P.field.k)) :=
  compactExchange Λ sq c
      (((DerivedCategory.singleFunctor _ 0).obj (line P Λ hΛ V)) ⟦(2 : ℤ)⟧) ≫
    (CondensedRing.rightDerivedLowerShriekOfCompactification Λ.X (c.ofIsPullback sq)).map
      (twistPull P Λ hΛ aX aV v).hom

/-- Full derived geometric exchange identifies the global divisor-class Thom map
with the adjunct and compact counit of the coordinate boundary. Quantification
over frames expresses independence of the chosen linear frame.
Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-smooth-purity/sec-the-trace-map-of-affine-space/sk-prop-an/
thm-pur-rank-one-thom.proof.md, Steps 1--2 (blueprint: lem-pur-line-thom-geometric-pullback).
Proof: use the local equation formula for the reviewed global cl(D), through the
supported-Hom identification. Exact pullback preserves its Kummer and support
boundary diagrams, so on the framed fibre it is the independently defined
coordinate boundary, with the stated root/scalar twist comparison. Compact
base change is invertible on this coefficient line. Paste the section and
projection squares: their composite is the identity square. Proper coincidence
and unital composition identify source exchange under sigma with unit pullback.
Naturality of exchange then expresses pulled-back tau as compact support of the
fibre class after sigma inverse. The closed adjunction factors that class as
pushforward of its adjunct followed by the counit. Naturality of sigma gives
alpha followed by compactCounit. Rescaling the coordinate adds the Kummer class
of a unit extending across the origin, whose support boundary is zero. Thus
this is independent of the frame, for each admissible coefficient directly.
At finite coefficients the fixed etale comparison is fully faithful, so the
full-arrow identity identifies the retained etale arrows as well. No finite
reductions determine the class, and no invertibility of tau, alpha or u is used. -/
theorem line_thom_geometric_pullback
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (bk : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated bk] [LocallyOfFiniteType bk] [QuasiCompact bk]
    (V : PurityVectorBundle P B bk 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (c : Compactification V.p) (b : Spec (CommRingCat.of Ω) ⟶ B)
    (v : AffineSpace (ULift.{u} (Fin 1)) (Spec (CommRingCat.of Ω)) ⟶ V.E)
    (sq : IsPullback v
      (AffineSpace (ULift.{u} (Fin 1)) (Spec (CommRingCat.of Ω)) ↘ Spec (CommRingCat.of Ω))
      V.p b)
    (hz : AffineSpace.zeroSection (ULift.{u} (Fin 1)) (Spec (CommRingCat.of Ω)) ≫ v =
      b ≫ V.zeroSection) :
    let S := Spec (CommRingCat.of Ω)
    let X := AffineSpace (ULift.{u} (Fin 1)) S
    let a := X ↘ S
    let i := AffineSpace.zeroSection (ULift.{u} (Fin 1)) S
    let M := ((DerivedCategory.singleFunctor _ 0).obj (line P Λ hΛ X)) ⟦(2 : ℤ)⟧
    IsIso (beta P Λ hΛ sq c (V.p ≫ bk) (a ≫ b ≫ bk)) ∧
      (unitPull Λ b).inv ≫
        (moduleObjectDerivedPullback Λ.X b).map (canonicalTau P bk V Λ hΛ c) ≫
        beta P Λ hΛ sq c (V.p ≫ bk) (a ≫ b ≫ bk) =
      alpha P Λ hΛ S (b ≫ bk) ≫
        compactCounit Λ i (AffineSpace.zeroSection_over _ _) (c.ofIsPullback sq) M := by
  sorry

end AlgebraicGeometry.ProEtale.LineThom
