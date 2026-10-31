/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.Transport
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Finite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
public import WeilConjectures.AlgebraicGeometry.GeoCartierCanonicalEtale
public import WeilConjectures.AlgebraicGeometry.CartierKummerMap
public import WeilConjectures.AlgebraicGeometry.PurityDivisorClass
public import WeilConjectures.AlgebraicGeometry.AffineSpaceCoordinateBoundaries
public import WeilConjectures.AlgebraicGeometry.ProjectionPurityCoordinates

/-! # Normalizations of smooth trace

Source: current blueprint sec-smooth-purity/sk-def-sp-trace/sk-def-sp-trace-properties.md
(blueprint: det-sp-trace-basic).
The comparisons below use the literal native condensed coefficient functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- The normalized pullback of the regular coefficient module.
Source: Cartesian coefficient units (blueprint: det-sp-trace-basic). -/
def tracePullUnit (c : Coefficient ell) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (actualPull (c.obj.{u} ell) f).obj (unit ell c Y) ≅ unit ell c X :=
  ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj.{u} ell) f).app
    (unit ell c Y)) ≪≫
    ((CondensedRing.upperStar (c.obj.{u} ell) f).mapDerivedCategorySingleFunctor 0).app (𝟙_ _) ≪≫
    (DerivedCategory.singleFunctor
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
        (condensedRingObj (c.obj.{u} ell) X)) 0).mapIso
      (Functor.Monoidal.εIso (CondensedRing.upperStar (c.obj.{u} ell) f)).symm

/-- The rank-zero Tate factor is the derived monoidal unit, with its actual
zero-shift and single-object comparisons.
Source: the rank-zero etale chart (blueprint: det-sp-trace-basic). -/
def traceLineZero (c : Coefficient ell) (X : Scheme.{u}) :
    c.derivedLine ell X 0 ≅ 𝟙_ (c.derived ell X) :=
  (shiftFunctorZero _ ℤ).app _ ≪≫ DerivedCategory.singleFunctorObjUnitIso.{u + 1, u + 1, u + 2}
    (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj (c.obj.{u} ell) X))

/-- Remove the rank-zero Tate factor from the smooth source.
Source: the rank-zero etale chart (blueprint: det-sp-trace-basic). -/
def traceSourceZero (c : Coefficient ell) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : c.derived ell Y) :
    (c.smoothSource ell f 0).obj K ≅ (actualPull (c.obj.{u} ell) f).obj K :=
  tensorIso (Iso.refl _) (traceLineZero ell c X) ≪≫ ρ_ _

/-- The canonical map from open extension by zero to direct image. It is the
pullback/direct-image adjunct of the inverse of the open-extension unit.
Source: compact-support/direct-image comparison (blueprint: det-sp-trace-basic). -/
def traceOpenToStar (c : Coefficient ell) {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (K : c.derived ell X) :
    (actualOpen (c.obj.{u} ell) j).obj K ⟶ (actualPush (c.obj.{u} ell) j).obj K :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction (c.obj.{u} ell) j).unit.app _ ≫
    (actualPush (c.obj.{u} ell) j).map
      (inv ((CondensedRing.derivedOpenImmersionLowerShriekLeftDerivedUpperStarAdjunction'
        (c.obj.{u} ell) j).unit.app K))

/-- The canonical compact-support/direct-image map for the displayed compactification.
It is constructed from the open-extension map and the direct-image compositor;
it does not use the smooth adjunction or its trace.
Source: the proper coincidence in clause (3) (blueprint: det-sp-trace-basic). -/
def traceShriekToStar (c : Coefficient ell) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (cf : Compactification f) (K : c.derived ell X) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj.{u} ell) cf).obj K ⟶
      (actualPush (c.obj.{u} ell) f).obj K :=
  (actualPush (c.obj.{u} ell) cf.g).map (traceOpenToStar ell c cf.i K) ≫
    (lowerComp (c.obj.{u} ell) cf.i cf.g).inv.app K ≫
    (eqToIso (congrArg (actualPush (c.obj.{u} ell)) cf.comm.symm)).hom.app K

/-- Derive the sheaf-level finite-etale sum. Exact finite direct image and exact
inverse image identify its source with `Rf_* Lf^* K`. The map `b.counit` is
required separately to satisfy the explicit sheet-sum formula.
Source: finite-etale summation in clause (3) (blueprint: det-sp-trace-basic). -/
def traceDerivedFiniteSum (c : Coefficient ell) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Etale f]
    (b : CondensedRing.lowerStar (c.obj.{u} ell) f ⊣ CondensedRing.upperStar (c.obj.{u} ell) f)
    (K : c.derived ell Y) :
    (actualPush (c.obj.{u} ell) f).obj ((actualPull (c.obj.{u} ell) f).obj K) ⟶ K :=
  letI := CondensedRing.preservesFiniteColimits_lowerStar_of_isFinite (c.obj.{u} ell) f
  ((CondensedRing.lowerStar (c.obj.{u} ell) f).rightDerivedFunctorIsoMapDerivedCategory).hom.app _ ≫
    (CondensedRing.lowerStar (c.obj.{u} ell) f).mapDerivedCategory.map
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory (c.obj.{u} ell) f).hom.app K) ≫
    (Adjunction.mapDerivedCategoryAdjunction b).counit.app K

/-- Clause (3), with the native sheet-summation formula and the actual proper
comparison `f_! -> f_*`. No equality to a trace defined as this same map is used.
The explicit rank-zero hypothesis retains the empty-source case.
Source: smooth trace properties (3) (blueprint: det-sp-trace-basic). -/
def TraceFiniteEtale (D : WeilConjectures.FiniteFieldDatum.{u})
    (a : AdjunctionFamily ell D) : Prop :=
  ∀ (c : Coefficient ell) (s : SmoothDatum D) [IsFinite s.map] [Etale s.map]
    (hzero : s.dim = 0),
    ∃ b : CondensedRing.lowerStar (c.obj.{u} ell) s.map ⊣
      CondensedRing.upperStar (c.obj.{u} ell) s.map,
      (∀ P, FiniteEtaleTraceFormula (c.obj.{u} ell) s.map P (b.counit.app P)) ∧
      (∀ K : c.derived ell s.X.left,
        IsIso (traceShriekToStar ell c s.compactification K)) ∧
      ∀ K : c.ctf ell s.Y.left,
        (a c s).trace K =
          (CondensedRing.rightDerivedLowerShriekOfCompactification
            (c.obj.{u} ell) s.compactification).map
              ((eqToIso (congrArg (fun d ↦ (c.smoothSource ell s.map d).obj K.obj)
                hzero)).hom ≫ (traceSourceZero ell c s.map K.obj).hom) ≫
          traceShriekToStar ell c s.compactification
            ((actualPull (c.obj.{u} ell) s.map).obj K.obj) ≫
          traceDerivedFiniteSum ell c s.map b K.obj

/-- The supported coefficient unit for a closed immersion, formed from the
ordinary pullback/direct-image adjunction and its normalized unit comparison.
Source: the supported Cartier source (blueprint: det-sp-trace-basic). -/
def traceSupportedUnit (c : Coefficient ell) {Z T : Scheme.{u}} (i : Z ⟶ T) :
    unit ell c T ⟶ (actualPush (c.obj.{u} ell) i).obj (unit ell c Z) :=
  (CondensedRing.derivedUpperStarLowerStarAdjunction (c.obj.{u} ell) i).unit.app _ ≫
    (actualPush (c.obj.{u} ell) i).map (tracePullUnit ell c i).hom

/-- A family of native supported Cartier arrows. Normalization is imposed below,
independently of the smooth trace. The final theorem asserts their existence
and its integration equation for every such family, so they cannot be chosen
using the desired integration equation.
Source: Cartier classes in clause (2) (blueprint: det-sp-trace-basic). -/
def TraceCartierFamily : Type (u + 1) :=
  ∀ (c : Coefficient ell) {Z T : Scheme.{u}} (i : Z ⟶ T)
    [IsClosedImmersion i] (_hI : i.ker.IsInvertible)
    (_hT : IsUnit (ell : Γ(T, ⊤))),
    (actualPush (c.obj.{u} ell) i).obj (unit ell c Z) ⟶ c.derivedLine ell T 1

/-- Finite native Cartier arrows are the actual relative-Kummer Ext classes.
The source comparison is fixed by the supported unit; the target comparison is
fixed by the root projection at the annihilating exponent. These equations
therefore do not allow an arbitrary rescaling of either class or orientation.
Source: lem-amb-cartier-kummer-map and its relative-boundary construction
(blueprint: det-sp-trace-basic). -/
def TraceCartierFinite (C : TraceCartierFamily.{u} ell) : Prop :=
  ∀ (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ)
    (hA : (ell ^ (n + 1) : A) = 0) {Z T : Scheme.{u}}
    (i : Z ⟶ T) [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (hT : IsUnit (ell : Γ(T, ⊤))),
    letI : Finite A := fin
    letI : TopologicalSpace A := ⊥
    letI : DiscreteTopology A := discreteTopology_bot A
    ∃ (hTN : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(T, ⊤)))
      (pT : FiniteLineCoordinates ell A fin n hA T hTN)
      (α : (finiteEncodingDerived A T).inverse.obj
        ((actualPush ((Coefficient.finite A fin n hA).obj ell) i).obj
          (unit ell (.finite A fin n hA) Z)) ≅
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory.obj
            ((Etale.ordinaryFinitePushforward (ULift.{u + 1} A) i).obj
              (Etale.ordinaryFiniteUnit (ULift.{u + 1} A) Z))),
      (finiteEncodingDerived A T).inverse.map
          (traceSupportedUnit ell (.finite A fin n hA) i) ≫ α.hom =
        (finiteDerivedUnit ell A n hA T hTN pT).hom ≫
          (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory.map
            (Etale.supportedDerivedUnit (ULift.{u + 1} A) i) ∧
      (finiteEncodingDerived A T).inverse.map
          (C (.finite A fin n hA) i hI hT) ≫
          (finiteDerivedLine ell A n hA T hTN pT).hom =
        α.hom ≫
          (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1} A)) T).mapDerivedCategory.map
              (Etale.supportedExactDerivedMap
                (Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) i)
                (Etale.ordinaryFiniteConstant (ULift.{u + 1} A) Z)
                (Scheme.finiteEtaleTateLine T (ell ^ (n + 1)) (ULift.{u + 1} A)
                  (finiteLiftAnnihilator ell A n hA))
                (Etale.geoCartierEtaleClass (ULift.{u + 1} A) (ell ^ (n + 1))
                  (pow_pos (Fact.out : ell.Prime).pos _) (finiteLiftAnnihilator ell A n hA)
                  i hI hTN))

/-- The canonical derived coefficient-unit map, obtained from degree zero of the
root-normalized scalar Tate coordinates.
Source: coefficient transport of the classes (blueprint: det-sp-trace-basic). -/
def traceScalarUnit {c c' : Coefficient ell} (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell) (T : Scheme.{u})
    (p : ScalarLineCoordinates ell a ha T) :
    (scalarSixChange a T).obj (unit ell c T) ⟶ unit ell c' T :=
  (scalarSixChange a T).map ((shiftFunctorZero _ ℤ).inv.app (unit ell c T)) ≫
    scalarLineMap ell a T 0 (p.power 0) ≫
    (shiftFunctorZero _ ℤ).hom.app (unit ell c' T)

/-- Native Cartier maps commute with the actual derived scalar-extension mate.
In particular this includes integral reduction to every finite quotient and
extension from the native integral ring to O_E, E and Qbar; no rationalization
or Karoubi-envelope coefficient model is introduced.
Source: coefficient transport in clause (2) (blueprint: det-sp-trace-basic). -/
def TraceCartierScalar (C : TraceCartierFamily.{u} ell) : Prop :=
  ∀ (c c' : Coefficient ell) (a : c.bundled.{u} ell ⟶ c'.bundled ell)
    (ha : c.integralMap ell ≫ a.hom.hom = c'.integralMap ell)
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (hI : i.ker.IsInvertible) (hT : IsUnit (ell : Γ(T, ⊤))),
    ∃ (pZ : ScalarLineCoordinates ell a ha Z) (pT : ScalarLineCoordinates ell a ha T),
      (scalarSixChange a T).map (C c i hI hT) ≫
          scalarLineMap ell a T 1 (pT.power 1) =
        (scalarDirectMate a i).app (unit ell c Z) ≫
          (actualPush (c'.obj.{u} ell) i).map (traceScalarUnit ell a ha Z pZ) ≫ C c' i hI hT

/-- The source of a product of supported coordinate classes. At zero it is the
regular unit, and at each step it is the actual derived tensor of supported units.
Source: the coordinate Cartier product (blueprint: det-sp-trace-basic). -/
def traceProductSource (c : Coefficient ell) (B : Scheme.{u}) (d : ℕ) :
    List (Fin d) → c.derived ell (iteratedAffineLine B d)
  | [] => unit ell c (iteratedAffineLine B d)
  | i :: is => traceProductSource c B d is ⊗
      (actualPush (c.obj.{u} ell) (AffineZeroPurity.inclusion B d i)).obj
        (unit ell c (AffineZeroPurity.divisor B d i))

/-- The quotient unit into the coordinate-support tensor, with the derived
single-unit comparison fixing the empty product and tensor unit maps.
Source: the source of the origin class (blueprint: det-sp-trace-basic). -/
def traceProductUnit (c : Coefficient ell) (B : Scheme.{u}) (d : ℕ) :
    (is : List (Fin d)) → unit ell c (iteratedAffineLine B d) ⟶
      traceProductSource ell c B d is
  | [] => 𝟙 _
  | i :: is => (λ_ (unit ell c (iteratedAffineLine B d))).inv ≫
      ((DerivedCategory.singleFunctorObjUnitIso.{u + 1, u + 1, u + 2}
        (Mod (Sheaf (ProEt.topology (iteratedAffineLine B d)) Ab.{u + 1})
          (condensedRingObj (c.obj.{u} ell) (iteratedAffineLine B d)))).inv ⊗ₘ 𝟙 _) ≫
      (traceProductUnit c B d is ⊗ₘ
        traceSupportedUnit ell c (AffineZeroPurity.inclusion B d i))

/-- Tensor the actual Cartier factors, or their negative Kummer-boundary factors,
and multiply their shifted Tate targets using the published even-degree tensorator.
Source: lem-amb-cartier-kummer-map and the negative boundary in lem-pur-divisor-class
(blueprint: det-sp-trace-basic). -/
def traceProductMap (C : TraceCartierFamily.{u} ell) (negative : Bool)
    (c : Coefficient ell) (B : Scheme.{u}) (d : ℕ)
    [∀ x : iteratedAffineLine B d, Invertible (ell : (iteratedAffineLine B d).residueField x)]
    (hT : IsUnit (ell : Γ(iteratedAffineLine B d, ⊤))) :
    (is : List (Fin d)) → traceProductSource ell c B d is ⟶
      c.derivedLine ell (iteratedAffineLine B d) is.length
  | [] => (shiftFunctorZero _ ℤ).inv.app (unit ell c (iteratedAffineLine B d))
  | i :: is =>
      (traceProductMap C negative c B d hT is ⊗ₘ
        (if negative then -C c (AffineZeroPurity.inclusion B d i)
          (AffineZeroPurity.coordinate_cartier B d i) hT
        else C c (AffineZeroPurity.inclusion B d i)
          (AffineZeroPurity.coordinate_cartier B d i) hT)) ≫
        (derivedProduct ell c (iteratedAffineLine B d) is.length 1).hom

/-- The native derived direct image of the identity, with its actual derived
identity comparison. Source: support of the origin (blueprint: det-sp-trace-basic). -/
def tracePushIdentity (c : Coefficient ell) (B : Scheme.{u}) :
    actualPush (c.obj.{u} ell) (𝟙 B) ≅ 𝟭 (c.derived ell B) :=
  Functor.rightDerivedFunctorNatIso (CondensedRing.lowerStarId (c.obj.{u} ell) B) ≪≫
    (𝟭 (Mod (Sheaf (ProEt.topology B) Ab.{u + 1})
      (condensedRingObj (c.obj.{u} ell) B))).rightDerivedFunctorIsoMapDerivedCategory ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The support of the origin is proper over the base. Its comparison to the
coefficient unit is formed before, and independently of, smooth integration.
Source: origin support in clause (2) (blueprint: det-sp-trace-basic). -/
def traceOriginSupport (c : Coefficient ell) (B : Scheme.{u}) (d : ℕ)
    (cf : Compactification (iteratedAffineLineProj B d)) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj.{u} ell) cf).obj
      ((actualPush (c.obj.{u} ell) (AffineZeroPurity.zero B d)).obj (unit ell c B)) ⟶
      unit ell c B :=
  traceShriekToStar ell c cf _ ≫
    (lowerComp (c.obj.{u} ell) (AffineZeroPurity.zero B d)
      (iteratedAffineLineProj B d)).inv.app (unit ell c B) ≫
    (eqToIso (congrArg (actualPush (c.obj.{u} ell))
      (Scheme.Hom.toIteratedAffineLine_proj (𝟙 B) (fun _ : Fin d ↦ 0)))).hom.app _ ≫
    (tracePushIdentity ell c B).hom.app _

/-- The affine projection in every dimension, in the project's ordered polynomial
coordinates. Source: the projection p_d (blueprint: det-sp-trace-basic). -/
def traceAffineDatum (D : WeilConjectures.FiniteFieldDatum.{u})
    (Y : Over (Spec (.of D.k))) [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] (d : ℕ)
    (cf : Compactification (iteratedAffineLineProj Y.left d)) : SmoothDatum D :=
  letI : (iteratedAffineLine Y.left d).Over (Spec (.of D.k)) :=
    ⟨iteratedAffineLineProj Y.left d ≫ Y.hom⟩
  letI : (iteratedAffineLineProj Y.left d).IsOver (Spec (.of D.k)) := ⟨rfl⟩
  letI := WeilConjectures.PurityFiniteSetting.projection_smooth Y.left d
  let X : Over (Spec (.of D.k)) := Over.mk (iteratedAffineLineProj Y.left d ≫ Y.hom)
  letI : LocallyOfFiniteType X.hom :=
    inferInstanceAs (LocallyOfFiniteType (iteratedAffineLineProj Y.left d ≫ Y.hom))
  letI : QuasiCompact X.hom :=
    inferInstanceAs (QuasiCompact (iteratedAffineLineProj Y.left d ≫ Y.hom))
  letI : IsSeparated X.hom :=
    inferInstanceAs (IsSeparated (iteratedAffineLineProj Y.left d ≫ Y.hom))
  { X := X
    Y := Y
    map := iteratedAffineLineProj Y.left d
    dim := d
    compactification := cf }

/-- The actual compactly supported origin/coordinate-product arrow, evaluated by
this same smooth trace. The source comparisons in TraceAffine are normalized by
the quotient unit and the proper-support comparison, so neither can absorb a
scalar or be chosen to force the trace equation.
Source: affine integration in clause (2) (blueprint: det-sp-trace-basic). -/
def traceAffineValue (D : WeilConjectures.FiniteFieldDatum.{u})
    (a : AdjunctionFamily ell D) (C : TraceCartierFamily.{u} ell) (negative : Bool)
    (c : Coefficient ell) (Y : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] (d : ℕ)
    (cf : Compactification (iteratedAffineLineProj Y.left d))
    (hi : ∀ x : iteratedAffineLine Y.left d,
      Invertible (ell : (iteratedAffineLine Y.left d).residueField x))
    (hT : IsUnit (ell : Γ(iteratedAffineLine Y.left d, ⊤)))
    (hu : property ell c Y.left (unit ell c Y.left))
    (α : traceProductSource ell c Y.left d (List.finRange d) ≅
      (actualPush (c.obj.{u} ell) (AffineZeroPurity.zero Y.left d)).obj (unit ell c Y.left))
    (β : unit ell c Y.left ≅
      (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj.{u} ell) cf).obj
        ((actualPush (c.obj.{u} ell) (AffineZeroPurity.zero Y.left d)).obj
          (unit ell c Y.left))) : unit ell c Y.left ⟶ unit ell c Y.left :=
  β.hom ≫
    (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj.{u} ell) cf).map
      (α.inv ≫ @traceProductMap ell inferInstance C negative c Y.left d hi hT
        (List.finRange d) ≫
        (eqToIso (congrArg (c.derivedLine ell (iteratedAffineLine Y.left d))
          (List.length_finRange (n := d)))).hom ≫
        (sourceUnit ell c (iteratedAffineLineProj Y.left d) d).inv) ≫
    (a c (traceAffineDatum D Y d cf)).trace ⟨_, hu⟩

/-- Every admissible coefficient and every dimension has the normalized origin
product and the negative Kummer product. The equalities are over Y itself, hence
remain these equalities after pullback to each geometric fibre. They include the
empty product d=0. Source: clause (2) (blueprint: det-sp-trace-basic). -/
def TraceAffine (D : WeilConjectures.FiniteFieldDatum.{u})
    (a : AdjunctionFamily ell D) (C : TraceCartierFamily.{u} ell) : Prop :=
  ∀ (c : Coefficient ell) (Y : Over (Spec (.of D.k))) [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] (d : ℕ)
    (cf : Compactification (iteratedAffineLineProj Y.left d)),
    ∃ (hi : ∀ x : iteratedAffineLine Y.left d,
        Invertible (ell : (iteratedAffineLine Y.left d).residueField x))
      (hT : IsUnit (ell : Γ(iteratedAffineLine Y.left d, ⊤)))
      (hu : property ell c Y.left (unit ell c Y.left))
      (α : traceProductSource ell c Y.left d (List.finRange d) ≅
        (actualPush (c.obj.{u} ell) (AffineZeroPurity.zero Y.left d)).obj
          (unit ell c Y.left))
      (β : unit ell c Y.left ≅
        (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj.{u} ell) cf).obj
          ((actualPush (c.obj.{u} ell) (AffineZeroPurity.zero Y.left d)).obj
            (unit ell c Y.left))),
      traceProductUnit ell c Y.left d (List.finRange d) ≫ α.hom =
        traceSupportedUnit ell c (AffineZeroPurity.zero Y.left d) ∧
      β.inv = traceOriginSupport ell c Y.left d cf ∧
      traceAffineValue ell D a C false c Y d cf hi hT hu α β = 𝟙 _ ∧
      traceAffineValue ell D a C true c Y d cf hi hT hu α β = (-1 : ℤ) ^ d • 𝟙 _

/-- The smooth trace is the transported counit, affine integration in every
relative dimension, and the finite-etale sheet sum, for native condensed finite,
integral, rational, finite-extension and algebraically closed coefficients.

Source: current blueprint sec-smooth-purity/sk-def-sp-trace,
sk-def-sp-trace-properties.md (blueprint: det-sp-trace-basic).

The family `a` carries all properties of `smooth_purity_transport`
(sk-thm-purity-transport): Brown comparison, change of coefficients, base change,
composition and affine-line normalization. Hence its counit-compatible gamma is the
specified purity isomorphism gamma_f, and `(a c s).trace` is Tr_f = epsilon_f o Rf_!(gamma_f).

Proof, following the six DAG steps.
1. Transport the specified exceptional Hom bijection along purity gamma from
sk-thm-purity-transport. Its inverse at the identity is epsilon composed with
Rf_!(gamma), and naturality is the displayed counit equation.
2. For finite coefficients, uniqueness in sk-thm-purity-transport identifies this
counit with the normalized finite system. det-sp-finite-general-ring and
det-sp-orientation-charts identify the affine projection with the ordered
coordinate integrations, agreeing with def-pur-smooth-trace.
3. The Cartier family is the relative frame-torsor boundary of
lem-amb-cartier-kummer-map (cartier_kummer_map). Its ordinary representative is
the uniquely normalized geoCartierEtaleClass used below. Its restriction from P1
has ordinary Chern class c1(O(1)), so def-amb-p1-trace integrates it to one.
lem-pur-coordinate-section-product-recursion and the projection formula iterate
this identity for every d. The source quotient unit fixes the tensor product's
identification with the origin support. lem-asd-ordinary-supported-kummer gives
arbitrary finite rings. lem-pur-divisor-class (divisor_class) uses the same
relative boundary and identifies each coordinate Kummer boundary with minus
this Cartier class; multilinearity gives (-1)^d. Pullback gives each geometric
fibre, and the empty coordinate product gives rank zero.
4. det-sp-reduction-exceptional, det-sp-orientation-charts and
det-sp-finite-general-ring identify the etale chart with the normalized sheet
sum. lem-pur-etale-sum-right-adjoint-tensor gives this equality on every K, via
the etale/pro-etale comparison of projection maps and their transposes.
5. lem-pur-transport-integral-counit-realization supplies integral counits;
coefficient extension carries the same identities to O_E, E and Qbar in the
native condensed categories. ScalarLineCoordinates fix all scalar maps by their
integral generators and root tensors. Uniqueness in sk-thm-purity-transport
identifies these counits with the same family a. The native Cartier maps are
specified independently by finite Kummer realization and scalar compatibility.
6. Finite maps are proper (lem-weil-pbc-finite-proper). The canonical open/direct
image map and the direct-image compositor give the invertible proper comparison
Rf_! to Rf_*, as in cor-cbc-proper-coincidence and sk-def-sfb-dc-lower-shriek.
The exact finite pushforward derives the actual sheet sum, including empty fibres.
-/
theorem smoothTrace_basic (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) :
    ∃ a : AdjunctionFamily ell D,
      BrownComparison ell D a ∧
      ScalarCompatible ell D a ∧
      BaseChangeCompatible ell D a ∧
      CompositionCompatible ell D hEll a ∧
      AffineNormalized ell D a ∧
      (∀ (c : Coefficient ell) (s : SmoothDatum D)
        (K L : c.ctf ell s.Y.left) (v : K ⟶ L),
        (source ell c s.map s.dim (a c s).source_closed ⋙
          support ell c s.compactification (a c s).support_closed).map v ≫
            (a c s).adjunction.counit.app L =
          (a c s).adjunction.counit.app K ≫ (𝟭 _).map v) ∧
      (∃ C : TraceCartierFamily.{u} ell,
        TraceCartierFinite ell C ∧ TraceCartierScalar ell C) ∧
      (∀ C : TraceCartierFamily.{u} ell,
        TraceCartierFinite ell C → TraceCartierScalar ell C → TraceAffine ell D a C) ∧
      TraceFiniteEtale ell D a := by
  sorry

end AlgebraicGeometry.ProEtale.PurityTransport
