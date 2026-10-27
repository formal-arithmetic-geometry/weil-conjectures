/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q08
-/
module

public import Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison
public import Sheaf.Paper.PurityAffineLineDatum
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

/-! # The zero-section exceptional object and its supported Kummer class

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
lem-pur-gysin-structure.md and its proof (blueprint: lem-pur-gysin-structure).

The support identification uses the counit-normalized localization comparison and
its cocycle-normalized edge map. The coordinate class is the recorded Kummer class,
converted to derived global sections by the degree-zero derived unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- The zero section is a closed immersion. Source: blueprint affine-line datum
(blueprint: lem-pur-gysin-structure). -/
instance gysinZeroClosed (Y : Scheme.{u}) : IsClosedImmersion (zeroSection Y) := by
  dsimp [zeroSection]
  infer_instance

/-- The coordinate basic open is open. Source: blueprint affine-line datum
(blueprint: lem-pur-gysin-structure). -/
instance gysinOpen (Y : Scheme.{u}) : IsOpenImmersion (openImmersion Y) := by
  dsimp [openImmersion]
  infer_instance

/-- The actual etale root line placed in degree zero. Source: blueprint clause one
(blueprint: lem-pur-gysin-structure). -/
abbrev gysinEtaleInput (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :=
  (DerivedCategory.Plus.singleFunctor (EtSheaves P (Line Y)) 0).obj
    (P.twistEtale h (Line Y))

/-- The exact comparison presentation of the coefficient sheaf on the small pro-etale site.
Source: blueprint conventions (blueprint: lem-pur-gysin-structure). -/
abbrev gysinInput (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :=
  (nuPlus P (Line Y)).obj (P.gysinEtaleInput h Y)

/-- The unshifted exceptional value uses the proper compactification of the zero section.
Source: blueprint clause one (blueprint: lem-pur-gysin-structure). -/
abbrev gysinClosed (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :=
  (closedTerm P (zeroSection Y)).obj (P.gysinEtaleInput h Y)

/-- The displayed object Rs^! A(1)[2]. Source: blueprint clause one
(blueprint: lem-pur-gysin-structure). -/
abbrev gysinValue (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :=
  (P.gysinClosed h Y)⟦(2 : ℤ)⟧

/-- Sections supported on the zero section, in degree two. Source: blueprint clause two
(blueprint: lem-pur-gysin-structure). -/
abbrev gysinSupport (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :=
  supportHypercohomology (zeroSection Y) P.Coefficient 2 (P.gysinInput h Y)

/-- Evaluation on 1 through the constant-sheaf and comparison adjunctions.
Source: blueprint proof step 9 (blueprint: lem-pur-gysin-structure). -/
def gysinEvaluate (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    {F : ProSheaves P T} (f : P.constant T ⟶ F) :
    (globalSectionsFunctor (Modules P) T).obj F :=
  ((constantSheafAdj T.smallEtaleTopology (Modules P)
    (Scheme.Etale.isTerminalMkId T)).homEquiv _ _
      ((comparisonAdjunction (Modules P) T).homEquiv _ _ f)) 1

/-- The actual map from derived Hom to global sections of H^0.
Source: blueprint proof step 9 (blueprint: lem-pur-gysin-structure). -/
def gysinHomToSections (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (m : P.derivedSheaf h Y false ⟶ P.gysinValue h Y) :
    (localClasses P Y 0).obj (P.gysinValue h Y) :=
  P.gysinEvaluate Y
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ProSheaves P Y) 0).inv.app
      (P.constant Y) ≫ (DerivedCategory.homologyFunctor (ProSheaves P Y) 0).map m)

/-- A derived class is evaluated on the actual coefficient unit, using the canonical
H^0(R Gamma(M[0])) = Gamma(M) comparison, then the derived shift comparison.
Source: blueprint proof steps 8--9 (blueprint: lem-pur-gysin-structure). -/
def gysinGlobalClass (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    {K : DerivedCategory (ProSheaves P T)} (q : ℤ)
    (m : (DerivedCategory.singleFunctor (ProSheaves P T) 0).obj (P.constant T) ⟶ K⟦q⟧) :
    (hyper P T q).obj K :=
  let E := globalSectionsFunctor (Modules P) T
  let v := (E.homologyRightDerivedFunctorObjSingleFunctorIso (P.constant T) 0).inv
    ((E.toRightDerivedZero.app (P.constant T)) (P.gysinEvaluate T (𝟙 (P.constant T))))
  ((DerivedCategory.homologyFunctor (Modules P) 0).map
      (E.rightDerivedFunctor.map m ≫
        (E.rightDerivedFunctor.commShiftIso q).hom.app K) ≫
    ((DerivedCategory.homologyFunctor (Modules P) 0).shiftIso q 0 q (add_zero q)).hom.app
      (E.rightDerivedFunctor.obj K)) v

/-- The canonical map identifying restriction of the input with the root line on Gm.
Its factors are exact-comparison, single-complex and root-pullback comparisons.
Source: blueprint affine-line datum and proof step 9 (blueprint: lem-pur-gysin-structure). -/
def gysinOpenCoefficient (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :
    (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory.obj
        (P.gysinInput h Y).obj ⟶ P.derivedSheaf h (Punctured Y) true :=
  let j := openImmersion Y
  let V := upperStar (Modules P) j
  V.mapDerivedCategory.map
    (((comparisonUpperStar (Modules P) (Line Y)).mapDerivedCategorySingleFunctor 0).hom.app
      (P.twistEtale h (Line Y))) ≫
    (V.mapDerivedCategorySingleFunctor 0).hom.app (P.twist h (Line Y)) ≫
    (DerivedCategory.singleFunctor (ProSheaves P (Punctured Y)) 0).map
      ((comparisonUpperStarCompUpperStarIso (Modules P) j).hom.app
        (P.twistEtale h (Line Y)) ≫
        (comparisonUpperStar (Modules P) (Punctured Y)).map (P.twistEtalePullback h j))

/-- Convert the actual Kummer class to the H^1 term at the support open. The coefficient
isomorphism is constrained in the theorem to have the specified canonical forward map.
Source: blueprint clause two (blueprint: lem-pur-gysin-structure). -/
def gysinKummerSection (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (c : Comparison P (lineProjection Y) (zeroSection Y) (openImmersion Y)
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y))
    (b : (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory.obj
      (P.gysinInput h Y).obj ≅ P.derivedSheaf h (Punctured Y) true) :
    (Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology (Line Y)) (Modules P)
      (Scheme.ProEt.mk (zeroSection Y).openComplement.ι) 1).obj (P.gysinInput h Y) :=
  let j := openImmersion Y
  let V := upperStar (Modules P) j
  let E := globalSectionsFunctor (Modules P) (Punctured Y)
  letI := (openImmersionLowerShriekUpperStarAdjunction (Modules P) j).preservesKInjectiveComplexes
  let e := Functor.isoWhiskerRight V.rightDerivedFunctorIsoMapDerivedCategory.symm
      E.rightDerivedFunctor ≪≫
    Functor.rightDerivedFunctorCompIso' V E (openSectionsIso P j)
  let x := (DerivedCategory.homologyFunctor (Modules P) 1).map
    (E.rightDerivedFunctor.map b.inv ≫ e.hom.app (P.gysinInput h Y).obj)
      (P.gysinGlobalClass (Punctured Y) 1 (P.coordinateKummer h Y a).hom)
  let y := ((sectionPlusIso P (Line Y) (Scheme.ProEt.mk j) 1).hom.app
    (P.gysinInput h Y)) x
  ((complementSectionsIso P (zeroSection Y) j c.complement 1).hom.app
    (P.gysinInput h Y)) y

/-- The canonical supported-cohomology identification is the inverse normalized edge map,
followed by the counit-normalized support comparison; its forward shift map is H^0(B[2])=H^2(B).
The final clause applies every exact support boundary to the actual coordinate class.
Source: blueprint clause two and proof steps 7--9 (blueprint: lem-pur-gysin-structure). -/
def GysinSupportIdentification (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) : Prop :=
  Nonempty (Comparison P (lineProjection Y) (zeroSection Y) (openImmersion Y)
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y)) ∧
  ∀ c : Comparison P (lineProjection Y) (zeroSection Y) (openImmersion Y)
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y),
    ∃ (b : (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory.obj
          (P.gysinInput h Y).obj ≅ P.derivedSheaf h (Punctured Y) true)
      (edge : (hyper P Y 2).obj (P.gysinClosed h Y) ≅
        (localClasses P Y 2).obj (P.gysinClosed h Y))
      (e : (localClasses P Y 0).obj (P.gysinValue h Y) ≅ P.gysinSupport h Y),
      b.hom = P.gysinOpenCoefficient h Y ∧
      edge.hom = (c.edge 2).app (P.gysinClosed h Y) ∧
      e.hom = (globalSectionsFunctor (Modules P) Y).map
          (((DerivedCategory.homologyFunctor (ProSheaves P Y) 0).shiftIso
            (2 : ℤ) 0 2 (add_zero 2)).hom.app (P.gysinClosed h Y)) ≫
        edge.inv ≫ (c.supportIso 2).hom.app (P.gysinEtaleInput h Y) ∧
      ∀ δ : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology (Line Y)) (Modules P)
          (supportRestrictionArrow (zeroSection Y)) ⊤,
        Sheaf.SupportSequenceExact (Scheme.ProEt.topology (Line Y)) (Modules P)
          (supportRestrictionArrow (zeroSection Y)) ⊤ δ →
        ∃ m : P.derivedSheaf h Y false ⟶ P.gysinValue h Y,
          e.hom (P.gysinHomToSections h Y m) =
            (δ 1).app ⟨P.gysinInput h Y, trivial⟩ (P.gysinKummerSection h Y a c b)

/-- Structure of the exceptional inverse image of the zero section.
Source: blueprint main-20261015, lem-pur-gysin-structure, both clauses
(blueprint: lem-pur-gysin-structure).

Proof: (1) The finite conventions and finite Kummer-level lemma give a finite coefficient
ring and an invertible Kummer exponent; affine-line support geometry gives a Noetherian
closed-open pair with quasi-compact complement. (2) The support localization triangle and
exact closed direct image, followed by Rp_*, give B0 -> P -> Q -> B0[1]. The derived
composition and identity comparisons use ps=id. (3) Relative Kummer identifies P with
A(1)[0], H^0(Q) with A(1), and H^1(Q) with A on the coordinate generator; higher and negative
cohomology vanish by injective representatives. (4) The cohomology long exact sequence gives
H^2(B0)=A and vanishing elsewhere. (5) Shift by two and use canonical good truncations.
(6) The constant rank-one module is constructible with Tor amplitude [0,0]. (7) Compare B0
with the transported exceptional value by the counit-compatible closed-support comparison.
(8) Supported Hom, the support adjunction and derived single full faithfulness identify
supported classes with Hom from A. The normalized global edge is therefore invertible.
(9) Evaluation at 1 gives the displayed bijection. The canonical global-cohomology image
of coordinateKummer is sent by any exact support boundary to a supported class; its inverse
image under the specified comparison and evaluation bijection is the asserted morphism.
-/
theorem gysin_structure (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y
      ((finiteCoefficientIntrinsicRealization Y P.Ring).mapDerivedCategory.obj
        (P.gysinValue h Y)) ∧
    (∀ q : ℤ, q ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ProSheaves P Y) q).obj (P.gysinValue h Y))) ∧
    (∃ H : EtSheaves P Y,
      Nonempty ((comparisonUpperStar (Modules P) Y).obj H ≅
        (DerivedCategory.homologyFunctor (ProSheaves P Y) 0).obj (P.gysinValue h Y)) ∧
      ∃ V : Scheme.Cover.{u} Scheme.etalePrecoverage Y,
        ∀ i : V.I₀, Nonempty
          ((Etale.upperStar (Modules P) (V.f i)).obj H ≅ P.constantEtale (V.X i))) ∧
    Function.Bijective (P.gysinHomToSections h Y) ∧
    GysinSupportIdentification P h Y a := by
  sorry

end WeilConjectures.PurityFiniteSetting
