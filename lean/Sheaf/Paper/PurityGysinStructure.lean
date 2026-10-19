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
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.Paper.PurityGysinConstant
import Sheaf.Paper.FiniteCtfTriangulated
import Sheaf.Paper.PurityConstantFiniteTor
import Sheaf.Paper.PurityConcentratedEdge
import Sheaf.Paper.AffineLineSupportGeometry

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
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite AlgebraicGeometry
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

/-- Evaluate a functor using the category structures already recorded in its type.
This is its ordinary object projection. Source: blueprint comparison conventions
(blueprint: lem-pur-gysin-structure). -/
def gysinFunctorObj {C D : Type*} {instC : Category C} {instD : Category D}
    (F : @CategoryTheory.Functor C instC D instD) (X : C) : D :=
  @Functor.obj C instC D instD F X

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
    gysinFunctorObj (D := Modules P) (globalSectionsFunctor (Modules P) T) F :=
  ((constantSheafAdj T.smallEtaleTopology (Modules P)
    (Scheme.Etale.isTerminalMkId T)).homEquiv _ _
      ((comparisonAdjunction (Modules P) T).homEquiv _ _ f)) 1

/-- Derived evaluation before specialization of the category.
Source: blueprint evaluation on one (blueprint: lem-pur-gysin-structure). -/
def gysinDerivedEvaluate {Λ : Type*} [CommRing Λ]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (E : C ⥤ ModuleCat Λ) (A : C) (K : DerivedCategory C)
    (ev : (F : C) → (A ⟶ F) → E.obj F)
    (m : gysinFunctorObj (DerivedCategory.singleFunctor C 0) A ⟶ K) :
    gysinFunctorObj (D := ModuleCat Λ) (DerivedCategory.homologyFunctor C 0 ⋙ E) K :=
  ev _ ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
    (DerivedCategory.homologyFunctor C 0).map m)

/-- The actual map from derived Hom to global sections of H^0.
Source: blueprint proof step 9 (blueprint: lem-pur-gysin-structure). -/
def gysinHomToSections (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (m : gysinFunctorObj (DerivedCategory.singleFunctor (ProSheaves P Y) 0)
      (P.constant Y) ⟶ P.gysinValue h Y) :
    gysinFunctorObj (D := Modules P) (localClasses P Y 0) (P.gysinValue h Y) :=
  gysinDerivedEvaluate (globalSectionsFunctor (Modules P) Y) (P.constant Y)
    (P.gysinValue h Y) (fun F ↦ P.gysinEvaluate Y (F := F)) m

/-- Global evaluation before specialization of the category.
Source: blueprint Kummer class conversion (blueprint: lem-pur-gysin-structure). -/
def gysinDerivedGlobalClass (Λ : Type*) [CommRing Λ]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [EnoughInjectives C] [HasKInjectiveResolutions C]
    (E : C ⥤ ModuleCat Λ) [E.Additive]
    (A : C) {K : DerivedCategory C} (q : ℤ)
    (m : gysinFunctorObj (DerivedCategory.singleFunctor C 0) A ⟶
      gysinFunctorObj (shiftFunctor (DerivedCategory C) q) K) (x : E.obj A) :
    (DerivedCategory.homologyFunctor (ModuleCat Λ) q).obj (E.rightDerivedFunctor.obj K) :=
  let v := (E.homologyRightDerivedFunctorObjSingleFunctorIso A 0).inv
    ((E.toRightDerivedZero.app A) x)
  ((DerivedCategory.homologyFunctor (ModuleCat Λ) 0).map
      (E.rightDerivedFunctor.map m ≫ (E.rightDerivedFunctor.commShiftIso q).hom.app K) ≫
    ((DerivedCategory.homologyFunctor (ModuleCat Λ) 0).shiftIso q 0 q (add_zero q)).hom.app
      (E.rightDerivedFunctor.obj K)) v

/-- A derived class is evaluated on the actual coefficient unit, using the canonical
H^0(R Gamma(M[0])) = Gamma(M) comparison, then the derived shift comparison.
Source: blueprint proof steps 8--9 (blueprint: lem-pur-gysin-structure). -/
def gysinGlobalClass (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    {K : DerivedCategory (ProSheaves P T)} (q : ℤ)
    (m : gysinFunctorObj (DerivedCategory.singleFunctor (ProSheaves P T) 0) (P.constant T) ⟶
      gysinFunctorObj (shiftFunctor (DerivedCategory (ProSheaves P T)) q) K) :
    gysinFunctorObj (D := Modules P) (hyper P T q) K :=
  gysinDerivedGlobalClass P.Coefficient (globalSectionsFunctor (Modules P) T)
    (P.constant T) q m (P.gysinEvaluate T (𝟙 (P.constant T)))

/-- Compose the three coefficient comparisons before category specialization.
Source: blueprint coefficient pullback comparison (blueprint: lem-pur-gysin-structure). -/
def gysinCoefficientComposite
    {C D E A B F : Type*}
    [Category C] [Category D] [Category E] [Category A] [Category B] [Category F]
    (sC : C ⥤ A) (sD : D ⥤ B) (sE : E ⥤ F)
    (V : D ⥤ E) (VD : B ⥤ F) (N : C ⥤ D) (ND : A ⥤ B)
    (α : sC ⋙ ND ⟶ N ⋙ sD) (β : sD ⋙ VD ⟶ V ⋙ sE)
    (X : C) (Y : E) (f : V.obj (N.obj X) ⟶ Y) :
    gysinFunctorObj VD (gysinFunctorObj ND (gysinFunctorObj sC X)) ⟶
      gysinFunctorObj sE Y :=
  VD.map (α.app X) ≫ β.app (N.obj X) ≫ sE.map f

/-- The canonical map identifying restriction of the input with the root line on Gm.
Its factors are exact-comparison, single-complex and root-pullback comparisons.
Source: blueprint affine-line datum and proof step 9 (blueprint: lem-pur-gysin-structure). -/
def gysinOpenCoefficient (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u}) :
    gysinFunctorObj (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory
        (P.gysinInput h Y).obj ⟶ P.derivedSheaf h (Punctured Y) true :=
  gysinCoefficientComposite
    (DerivedCategory.singleFunctor (EtSheaves P (Line Y)) 0)
    (DerivedCategory.singleFunctor (ProSheaves P (Line Y)) 0)
    (DerivedCategory.singleFunctor (ProSheaves P (Punctured Y)) 0)
    (upperStar (Modules P) (openImmersion Y))
    (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory
    (comparisonUpperStar (Modules P) (Line Y))
    (comparisonUpperStar (Modules P) (Line Y)).mapDerivedCategory
    ((comparisonUpperStar (Modules P) (Line Y)).mapDerivedCategorySingleFunctor 0).hom
    ((upperStar (Modules P) (openImmersion Y)).mapDerivedCategorySingleFunctor 0).hom
    (P.twistEtale h (Line Y)) (P.twist h (Punctured Y))
    ((comparisonUpperStarCompUpperStarIso (Modules P) (openImmersion Y)).hom.app
      (P.twistEtale h (Line Y)) ≫
      (comparisonUpperStar (Modules P) (Punctured Y)).map
        (P.twistEtalePullback h (openImmersion Y)))

/-- Transport a class through a comparison of composite functors.
Source: blueprint supported Kummer class (blueprint: lem-pur-gysin-structure). -/
def gysinTransportClass {Λ : Type*} [CommRing Λ]
    {C D E : Type*} [Category C] [Category D] [Category E]
    (L : E ⥤ C) (F : C ⥤ D) (G : E ⥤ D) (H : D ⥤ ModuleCat Λ)
    (e : L ⋙ F ≅ G) (X : E) (Y : C) (x : H.obj (F.obj Y)) (b : L.obj X ≅ Y) :
    H.obj (G.obj X) := H.map (F.map b.inv ≫ e.hom.app X) x

/-- Convert the actual Kummer class to the H^1 term at the support open. The coefficient
isomorphism is constrained in the theorem to have the specified canonical forward map.
Source: blueprint clause two (blueprint: lem-pur-gysin-structure). -/
def gysinKummerSection (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (c : Comparison P (lineProjection Y) (zeroSection Y) (openImmersion Y)
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y))
    (b : gysinFunctorObj (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory
      (P.gysinInput h Y).obj ≅ P.derivedSheaf h (Punctured Y) true) :
    gysinFunctorObj (D := Modules P)
    (Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology (Line Y)) (Modules P)
      (Scheme.ProEt.mk (zeroSection Y).openComplement.ι) 1) (P.gysinInput h Y) :=
  let j := openImmersion Y
  let V := upperStar (Modules P) j
  let E := globalSectionsFunctor (Modules P) (Punctured Y)
  letI := (openImmersionLowerShriekUpperStarAdjunction (Modules P) j).preservesKInjectiveComplexes
  let e := Functor.isoWhiskerRight V.rightDerivedFunctorIsoMapDerivedCategory.symm
      E.rightDerivedFunctor ≪≫
    Functor.rightDerivedFunctorCompIso' V E (openSectionsIso P j)
  let x := gysinTransportClass V.mapDerivedCategory E.rightDerivedFunctor _
    (DerivedCategory.homologyFunctor (Modules P) 1) e (P.gysinInput h Y).obj
    (P.derivedSheaf h (Punctured Y) true)
    (P.gysinGlobalClass (Punctured Y) 1 (P.coordinateKummer h Y a).hom) b
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
    ∃ (b : gysinFunctorObj (upperStar (Modules P) (openImmersion Y)).mapDerivedCategory
          (P.gysinInput h Y).obj ≅ P.derivedSheaf h (Punctured Y) true)
      (edge : gysinFunctorObj (D := Modules P) (hyper P Y 2) (P.gysinClosed h Y) ≅
        gysinFunctorObj (D := Modules P) (localClasses P Y 2) (P.gysinClosed h Y))
      (e : gysinFunctorObj (D := Modules P) (localClasses P Y 0)
        (P.gysinValue h Y) ≅ P.gysinSupport h Y),
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
        ∃ m : gysinFunctorObj (DerivedCategory.singleFunctor (ProSheaves P Y) 0)
            (P.constant Y) ⟶ P.gysinValue h Y,
          e.hom (P.gysinHomToSections h Y m) =
            (δ 1).app ⟨P.gysinInput h Y, trivial⟩ (P.gysinKummerSection h Y a c b)

private theorem gysinEvaluate_bijective (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (F : ProSheaves P Y) : Function.Bijective (P.gysinEvaluate Y (F := F)) := by
  let e := (comparisonAdjunction (Modules P) Y).homEquiv (P.constantEtale Y) F
  let d := (constantSheafAdj Y.smallEtaleTopology (Modules P)
    (Scheme.Etale.isTerminalMkId Y)).homEquiv
      (ModuleCat.of P.Coefficient P.Coefficient)
      ((comparisonLowerStar (Modules P) Y).obj F)
  let M := (globalSectionsFunctor (Modules P) Y).obj F
  let v : (ModuleCat.of P.Coefficient P.Coefficient ⟶ M) ≃ M :=
    (ModuleCat.homEquiv).trans
      (LinearMap.ringLmapEquivSelf P.Coefficient P.Coefficient M).toEquiv
  exact (v.bijective.comp d.bijective).comp e.bijective

private theorem gysinDerivedEvaluate_bijective {Λ : Type*} [CommRing Λ]
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (E : C ⥤ ModuleCat Λ) (A B : C) (K : DerivedCategory C)
    (e : K ≅ (DerivedCategory.singleFunctor C 0).obj B)
    (ev : (F : C) → (A ⟶ F) → E.obj F)
    (hev : Function.Bijective (ev ((DerivedCategory.homologyFunctor C 0).obj K))) :
    Function.Bijective (gysinDerivedEvaluate E A K ev) := by
  have : K.IsGE 0 := DerivedCategory.TStructure.t.isGE_of_iso e.symm 0
  have : K.IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso e.symm 0
  have hh := (Iso.homCongr
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app A)
      (Iso.refl ((DerivedCategory.homologyFunctor C 0).obj K))).bijective.comp
    (DerivedCategory.homologyFunctor_map_bijective_of_isGE_of_isLE
      (P := (DerivedCategory.singleFunctor C 0).obj A) (Q := K) 0)
  change Function.Bijective (fun m : (DerivedCategory.singleFunctor C 0).obj A ⟶ K ↦
    ev _ ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).inv.app A ≫
      (DerivedCategory.homologyFunctor C 0).map m))
  simpa only [Function.comp_def, Iso.homCongr_apply, Iso.refl_hom,
    Category.comp_id, Iso.app_inv] using hev.comp hh

private theorem module_exists_preimage {Λ : Type*} [CommRing Λ] {S : Type*}
    {M N : ModuleCat Λ} (e : M ≅ N) (f : S → M) (hf : Function.Bijective f) (y : N) :
    ∃ x, e.hom (f x) = y := by
  obtain ⟨x, hx⟩ := hf.surjective (e.inv y)
  exact ⟨x, (congrArg (fun z ↦ e.hom z) hx).trans (e.inv_hom_id_apply y)⟩

private theorem single_structure_transport {C D : Type*}
    [Category C] [Abelian C] [HasDerivedCategory C] [Category D]
    (G : DerivedCategory C ⥤ D) (Q : ObjectProperty D) [Q.IsClosedUnderIsomorphisms]
    (A : C) (K : DerivedCategory C)
    (v : K ≅ (DerivedCategory.singleFunctor C 0).obj A)
    (ha : Q (G.obj ((DerivedCategory.singleFunctor C 0).obj A))) :
    Q (G.obj K) ∧
      (∀ q : ℤ, q ≠ 0 → IsZero ((DerivedCategory.homologyFunctor C q).obj K)) ∧
      Nonempty (A ≅ (DerivedCategory.homologyFunctor C 0).obj K) ∧ K.IsGE 0 := by
  have : K.IsGE 0 := DerivedCategory.TStructure.t.isGE_of_iso v.symm 0
  have : K.IsLE 0 := DerivedCategory.TStructure.t.isLE_of_iso v.symm 0
  refine ⟨Q.prop_of_iso (G.mapIso v.symm) ha, ?_, ?_⟩
  · intro q hq
    rcases lt_or_gt_of_ne hq with hq | hq
    · exact (DerivedCategory.isGE_iff _ 0).mp ‹K.IsGE 0› q hq
    · exact (DerivedCategory.isLE_iff _ 0).mp ‹K.IsLE 0› q hq
  · exact ⟨⟨((DerivedCategory.homologyFunctor C 0).mapIso v ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app A).symm⟩, inferInstance⟩

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
  have hiso : Nonempty (P.gysinValue h Y ≅ P.derivedSheaf h Y false) :=
    P.gysin_shifted_constant h Y a
  obtain ⟨v⟩ := hiso
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y) :=
    (Scheme.finite_ctf_isTriangulated P.coefficients.l P.extension P.level P.level_pos Y).1
  have hparts := single_structure_transport
    (finiteCoefficientIntrinsicRealization Y P.Ring).mapDerivedCategory
    (finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y)
    (P.constant Y) (P.gysinValue h Y) v (P.constant_finiteTor h Y a)
  have hv : (P.gysinValue h Y).IsGE 0 := hparts.2.2.2
  have hclosed : (P.gysinClosed h Y).IsGE 2 :=
    DerivedCategory.TStructure.t.isGE_of_shift (P.gysinClosed h Y) 2 2 0 (by omega)
  have hb : Function.Bijective (P.gysinHomToSections h Y) :=
    gysinDerivedEvaluate_bijective (globalSectionsFunctor (Modules P) Y)
      (P.constant Y) (P.constant Y) _ v
      (fun F ↦ P.gysinEvaluate Y (F := F)) (gysinEvaluate_bijective P Y _)
  refine ⟨hparts.1, hparts.2.1, ?_, hb, ?_⟩
  · refine ⟨P.constantEtale Y, hparts.2.2.1, Scheme.coverOfIsIso (P := @Etale) (𝟙 Y), ?_⟩
    intro i
    exact ⟨(Scheme.upperStarConstantSheafIso (Modules P) (𝟙 Y)).app _⟩
  · let : Y.Over (Spec (.of P.field.k)) := ⟨a⟩
    have : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) := by
      change LocallyOfFiniteType a
      infer_instance
    have : QuasiCompact (Y ↘ Spec (.of P.field.k)) := by
      change QuasiCompact a
      infer_instance
    have : IsSeparated (Y ↘ Spec (.of P.field.k)) := by
      change IsSeparated a
      infer_instance
    have hgeom := affineLine_support_geometry P.field.k Y
    let : QuasiCompact (openImmersion Y) := hgeom.2.2.2.2.2
    let : (Line Y).Over (Spec (.of P.field.k)) := ⟨lineProjection Y ≫ a⟩
    have : (lineProjection Y).IsOver (Spec (.of P.field.k)) :=
      ⟨rfl⟩
    let : LocallyOfFiniteType (lineProjection Y ≫ a) := hgeom.1.1
    let : QuasiCompact (lineProjection Y ≫ a) := hgeom.1.2
    have : LocallyOfFiniteType (lineProjection Y) := by
      dsimp [lineProjection]
      infer_instance
    have : QuasiCompact (lineProjection Y) := by
      dsimp [lineProjection]
      infer_instance
    have hp : IsSeparated (lineProjection Y) := by
      dsimp [lineProjection]
      infer_instance
    let : IsSeparated (lineProjection Y) := hp
    have hcompl : IsCompl (Set.range (zeroSection Y).base)
        (Set.range (openImmersion Y).base) := by
      have hs : Set.range (zeroSection Y).base =
          ((Line Y).basicOpen (coordinate Y) : Set (Line Y))ᶜ := by
        change Set.range (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Y) = _
        rw [AffineSpace.range_zeroSection]
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
        exact ⟨fun hx ↦ hx (ULift.up 0), fun hx i ↦ by
          have : i = ULift.up 0 := Subsingleton.elim _ _
          subst i
          exact hx⟩
      rw [hs]
      change IsCompl _ (Set.range ((Line Y).basicOpen (coordinate Y)).ι.base)
      rw [Scheme.Opens.range_ι]
      exact isCompl_compl.symm
    have : IsSeparated (Line Y ↘ Spec (.of P.field.k)) := by
      change IsSeparated (lineProjection Y ≫ a)
      infer_instance
    have : LocallyOfFiniteType (Line Y ↘ Spec (.of P.field.k)) := by
      change LocallyOfFiniteType (lineProjection Y ≫ a)
      infer_instance
    have : QuasiCompact (Line Y ↘ Spec (.of P.field.k)) := by
      change QuasiCompact (lineProjection Y ≫ a)
      infer_instance
    have hc := exists_comparison P (lineProjection Y) (zeroSection Y)
      (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) Y)
      (openImmersion Y) hcompl
    refine ⟨hc, fun c ↦ ?_⟩
    let := P.isIso_twistEtalePullback h (openImmersion Y)
      (P.exponent_isUnit (Line Y) (lineProjection Y ≫ a))
    have hbcoeff : IsIso (P.gysinOpenCoefficient h Y) := by
      dsimp [gysinOpenCoefficient, gysinCoefficientComposite, gysinFunctorObj]
      infer_instance
    let b := asIso (P.gysinOpenCoefficient h Y)
    let := edge_isIso_of_isGE P Y 2 (c.edge 2) (c.edge_normalized 2)
      (P.gysinClosed h Y)
    let edge := asIso ((c.edge 2).app (P.gysinClosed h Y))
    let e : (localClasses P Y 0).obj (P.gysinValue h Y) ≅ P.gysinSupport h Y :=
      (globalSectionsFunctor (Modules P) Y).mapIso
        (((DerivedCategory.homologyFunctor (ProSheaves P Y) 0).shiftIso
          (2 : ℤ) 0 2 (add_zero 2)).app (P.gysinClosed h Y)) ≪≫
        edge.symm ≪≫ (c.supportIso 2).app (P.gysinEtaleInput h Y)
    refine ⟨b, edge, e, rfl, rfl, rfl, fun δ _ ↦ ?_⟩
    exact module_exists_preimage e (P.gysinHomToSections h Y) hb
      ((δ 1).app ⟨P.gysinInput h Y, trivial⟩ (P.gysinKummerSection h Y a c b))

end WeilConjectures.PurityFiniteSetting
