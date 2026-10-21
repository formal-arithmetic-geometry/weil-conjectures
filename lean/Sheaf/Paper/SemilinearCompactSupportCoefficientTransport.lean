/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.CompactSupportReductionTower
public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.BoundedConstructibleTower
import Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import all Sheaf.AlgebraicGeometry.VaryingRingOperations

/-! # SemilinearCompactSupportCoefficientTransport

Source: blueprint sk-thm-purity-transport, Steps 2--3; the compact-support
realization prerequisite, proof Steps 2--3 and 8--11 (agent-formulated constructions).
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The existing finite quotient rings, with the site-size lift.
Source: blueprint proof Step 2
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
abbrev quotientRings (n : ℕ) : CommRingCat.{u + 1} :=
  CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))

/-- The actual adjacent quotient maps, retaining their scalar actions.
Source: blueprint proof Step 2
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def quotientMaps (n : ℕ) : quotientRings l E (n + 1) ⟶ quotientRings l E n :=
  CommRingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((Padic.coefficientExtensionTransition l E (n + 1)).comp ULift.ringEquiv.toRingHom))

/-- Whole-system compact support: exact extension by zero followed by separately
right-derived proper direct image, on the ringed sequence site itself.
Source: blueprint proof Steps 2--3, Zheng Construction 4.1
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def systemSupport {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    coefficientSequenceDerived.{u, u} l E X ⥤ coefficientSequenceDerived.{u, u} l E Y :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.J (quotientRings l E) (quotientMaps l E) c.i ⋙
    AlgebraicGeometry.ProEtale.SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) c.g



end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E F : Type u) [NormedField E] [NormedField F]
  [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The finite scalar maps commute with the adjacent quotient transitions, even when
ramified. Source: blueprint proof Steps 8--11
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: both composites are induced from the same integer-ring inclusion and target
quotient. Quotient induction and constant sheafification give the equality. -/
theorem scalarQuotients_commute (W : Scheme.{u}) (n : ℕ) :
    integralScalarQuotientSheafMap.{u, u} l E F i W (n + 1) ≫
        coefficientSequenceCommRingTransition.{u, u} l F W n =
      coefficientSequenceCommRingTransition.{u, u} l E W n ≫
        integralScalarQuotientSheafMap.{u, u} l E F i W n := by
  unfold integralScalarQuotientSheafMap
  have h (K : Type u) [NormedField K] [NormedAlgebra ℚ_[l] K]
      [FiniteDimensional ℚ_[l] K] :
      coefficientSequenceCommRingTransition.{u, u} l K W n =
        (constantSheaf (ProEt.topology W) CommRingCat.{u + 1}).map
          (quotientMaps l K n) := rfl
  rw [h E, h F, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext x
  exact RingHom.congr_fun (integralScalarQuotientMap_transition l E F i n) x.down

/-- The actual ring map on the entire vertical sequence site.
Source: blueprint proof Steps 9--11; semilinear systemMap
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def scalarSystemMap (W : Scheme.{u}) :=
  SemilinearSections.systemMap (ProEt.topology W)
    (integralCoefficientCommRingSheaf.{u, u} l E W)
    (coefficientSequenceCommRingTransition.{u, u} l E W)
    (integralCoefficientCommRingSheaf.{u, u} l F W)
    (coefficientSequenceCommRingTransition.{u, u} l F W)
    (integralScalarQuotientSheafMap.{u, u} l E F i W) (scalarQuotients_commute l E F i W)

/-- Exact restriction of the full semilinear system along the actual coefficient map.
Source: blueprint proof Steps 9--11
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
abbrev systemRestriction (W : Scheme.{u}) :=
  SemilinearSections.res (scalarSystemMap l E F i W)

/-- Exact derived coefficient restriction on whole systems.
Source: blueprint proof Steps 9--11
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
abbrev derivedSystemRestriction (W : Scheme.{u}) :=
  (systemRestriction l E F i W).mapDerivedCategory

/-- The existing universal, K-flat normalized whole-system scalar extension.
Source: blueprint proof Step 10; lem-coef-semilinear-derived-sections
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def systemScalarData (W : Scheme.{u}) :
    SemilinearSections.ScalarSystems.{u + 1, u, u + 1} (ProEt.topology W)
      (integralCoefficientCommRingSheaf.{u, u} l E W)
      (coefficientSequenceCommRingTransition.{u, u} l E W)
      (integralCoefficientCommRingSheaf.{u, u} l F W)
      (coefficientSequenceCommRingTransition.{u, u} l F W)
      (integralScalarQuotientSheafMap.{u, u} l E F i W)
      (scalarQuotients_commute l E F i W) :=
  (SemilinearSections.semilinearDerivedSections.{u + 1, u, u + 1} (ProEt.topology W)
    (integralCoefficientCommRingSheaf.{u, u} l E W)
    (coefficientSequenceCommRingTransition.{u, u} l E W)).some.coefficientExtension
      (integralCoefficientCommRingSheaf.{u, u} l F W)
     
    (coefficientSequenceCommRingTransition.{u, u} l F W)
      (integralScalarQuotientSheafMap.{u, u} l E F i W) (scalarQuotients_commute l E F i W)

private theorem scalarSystemMap_app (W : Scheme.{u}) (n : ℕ) (U : W.ProEtᵒᵖ) :
    (scalarSystemMap l E F i W).hom.app (op (n, U.unop)) =
      (integralScalarQuotientSheafMap l E F i W n).hom.app U :=
  (SemilinearSections.systemMap_existsUnique (ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W)
    (coefficientSequenceCommRingTransition l E W)
    (integralCoefficientCommRingSheaf l F W)
    (coefficientSequenceCommRingTransition l F W)
    (integralScalarQuotientSheafMap l E F i W)
    (scalarQuotients_commute l E F i W)).exists.choose_spec n U

private theorem scalarSystemMap_push_square {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SemilinearProperOpen.coefficientMap (quotientRings l E) (quotientMaps l E) f ≫
        ((SemilinearProperOpen.siteMap f).sheafPushforwardContinuous CommRingCat.{u + 1}
          (coefficientSequenceTopology (ProEt.topology Y))
          (coefficientSequenceTopology (ProEt.topology X))).map
            (scalarSystemMap l E F i X) =
      scalarSystemMap l E F i Y ≫
        SemilinearProperOpen.coefficientMap (quotientRings l F) (quotientMaps l F) f := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  have hE := eq_of_heq ((SemilinearProperOpen.coefficientMap_existsUnique
    (quotientRings l E) (quotientMaps l E) f).choose_spec.1 U.unop.1 U.unop.2)
  have hF := eq_of_heq ((SemilinearProperOpen.coefficientMap_existsUnique
    (quotientRings l F) (quotientMaps l F) f).choose_spec.1 U.unop.1 U.unop.2)
  have hX := scalarSystemMap_app l E F i X U.unop.1
    (op ((proEtaleBaseChange f).obj U.unop.2))
  have hY := scalarSystemMap_app l E F i Y U.unop.1 (op U.unop.2)
  have h := congrArg (fun t ↦ t.hom.app (op U.unop.2))
    (VaryingRing.constantMap_naturality f (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
        ((integralScalarQuotientMap l E F i U.unop.1).comp
          (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))))
  exact (congrArg₂ (fun a b ↦ a ≫ b) hE hX).trans
    (h.symm.trans (congrArg₂ (fun a b ↦ a ≫ b) hY hF).symm)

private theorem restriction_push_iso
    {A B : Type*} [Category A] [Category B]
    {J : GrothendieckTopology A} {K : GrothendieckTopology B}
    (T : A ⥤ B) [T.IsContinuous J K]
    {RX SX : Sheaf K RingCat.{u + 1}} {RY SY : Sheaf J RingCat.{u + 1}}
    (aX : RX ⟶ SX) (aY : RY ⟶ SY)
    (bE : RY ⟶ (T.sheafPushforwardContinuous RingCat.{u + 1} J K).obj RX)
    (bF : SY ⟶ (T.sheafPushforwardContinuous RingCat.{u + 1} J K).obj SX)
    (h : bE ≫ (T.sheafPushforwardContinuous RingCat.{u + 1} J K).map aX = aY ≫ bF) :
    ∃ d : SheafOfModules.restrictScalars.{u + 1} aX ⋙ SheafOfModules.pushforward bE ≅
        SheafOfModules.pushforward bF ⋙ SheafOfModules.restrictScalars aY,
      ∀ (M : SheafOfModules.{u + 1} SX) (U : Aᵒᵖ)
        (x : M.val.obj (T.op.obj U)), (d.hom.app M).val.app U x = x := by
  let d : SheafOfModules.restrictScalars.{u + 1} aX ⋙ SheafOfModules.pushforward bE ≅
      SheafOfModules.pushforward bF ⋙ SheafOfModules.restrictScalars aY :=
    SheafOfModules.pushforwardComp (F := T) (G := 𝟭 B) bE aX ≪≫
      SheafOfModules.pushforwardCongr h ≪≫
        (SheafOfModules.pushforwardComp (F := 𝟭 A) (G := T) aY bF).symm
  exact ⟨d, fun _ _ _ ↦ rfl⟩

/-- Restriction commutes with ordinary geometric pushforward by the identity on sections.
Source: blueprint proof Step 10; Stacks 03D7
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: both objects have sections M_n(U times_Y X), with the same source-ring action
through the quotient inclusion. Identity maps give a natural isomorphism and commute
with every index arrow. Sections at (n,U) prove uniqueness. -/
theorem systemRestrictionPush_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! d : systemRestriction l E F i X ⋙
          SemilinearProperOpen.push (quotientRings l E) (quotientMaps l E) f ≅
        SemilinearProperOpen.push (quotientRings l F) (quotientMaps l F) f ⋙
          systemRestriction l E F i Y,
      ∀ (M : coefficientSequenceModules.{u, u} l F X) (n : ℕ) (U : Y.ProEt)
        (x : ((systemRestriction l E F i X ⋙
          SemilinearProperOpen.push (quotientRings l E) (quotientMaps l E) f).obj M).val.obj
            (op (n, U))),
        HEq ((d.hom.app M).val.app (op (n, U)) x) x := by
  let a (W : Scheme.{u}) := (sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (scalarSystemMap l E F i W)
  let b (K : Type u) [NormedField K] [NormedAlgebra ℚ_[l] K]
      [FiniteDimensional ℚ_[l] K] := (sheafCompose _
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (SemilinearProperOpen.coefficientMap (quotientRings l K) (quotientMaps l K) f)
  have he : b E ≫ ((SemilinearProperOpen.siteMap f).sheafPushforwardContinuous
      RingCat.{u + 1} (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceTopology (ProEt.topology X))).map (a X) = a Y ≫ b F := by
    exact congrArg (fun t ↦ (sheafCompose _
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map t)
        (scalarSystemMap_push_square l E F i f)
  obtain ⟨d, hd⟩ := restriction_push_iso (SemilinearProperOpen.siteMap f)
    (a X) (a Y) (b E) (b F) he
  refine ⟨d, fun M n U x ↦ heq_of_eq (hd M (op (n, U)) x), ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext x
  exact (eq_of_heq (hd' M U.unop.1 U.unop.2 x)).trans (hd M U x).symm

/-- The ordinary inverse-image comparison is the specified pushforward mate.
Source: blueprint proof Step 10
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def systemRestrictionPullInv {X Y : Scheme.{u}} (f : X ⟶ Y) :
    systemRestriction l E F i Y ⋙
        SemilinearProperOpen.pull (quotientRings l E) (quotientMaps l E) f ⟶
      SemilinearProperOpen.pull (quotientRings l F) (quotientMaps l F) f ⋙
        systemRestriction l E F i X :=
  (mateEquiv
    (SemilinearProperOpen.ordinaryAdj (quotientRings l F) (quotientMaps l F) f)
    (SemilinearProperOpen.ordinaryAdj (quotientRings l E) (quotientMaps l E) f)).symm
      (systemRestrictionPush_existsUnique l E F i f).choose.inv

/-- The pullback comparison is invertible without quotient flatness.
Source: blueprint proof Step 10; Stacks 03EK
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: inverse image uses identified coefficient sheaves. The displayed mate is the
identity on the underlying additive inverse images, with the same restricted action.
It has the inverse identity map, at every index simultaneously. -/
theorem systemRestrictionPullInv_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (systemRestrictionPullInv l E F i f) := by
  sorry

attribute [instance] systemRestrictionPullInv_isIso

/-- The recorded exact pullback has its recorded additive structure.
Source: Zheng 4.10 (blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
instance systemPullAdditive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (SemilinearProperOpen.pull (quotientRings l E) (quotientMaps l E) f).Additive :=
  (SemilinearProperOpen.pull_exact (quotientRings l E) (quotientMaps l E) f).1

/-- The exact localization of the normalized ordinary pullback square.
Source: blueprint proof Step 10
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def systemRestrictionPull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SemilinearProperOpen.P (quotientRings l F) (quotientMaps l F) f ⋙
        derivedSystemRestriction l E F i X ≅
      derivedSystemRestriction l E F i Y ⋙
        SemilinearProperOpen.P (quotientRings l E) (quotientMaps l E) f :=
  letI := systemPullAdditive l E f
  letI := systemPullAdditive l F f
  letI := (SemilinearProperOpen.pull_exact (quotientRings l E) (quotientMaps l E) f).2.1
  letI := (SemilinearProperOpen.pull_exact (quotientRings l E) (quotientMaps l E) f).2.2
  letI := (SemilinearProperOpen.pull_exact (quotientRings l F) (quotientMaps l F) f).2.1
  letI := (SemilinearProperOpen.pull_exact (quotientRings l F) (quotientMaps l F) f).2.2
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (asIso (systemRestrictionPullInv l E F i f)).symm ≪≫
      Functor.mapDerivedCategoryCompIso _ _


/-- The proper-image restriction arrow is the actual derived adjunction mate.
Source: blueprint proof Step 10
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def systemRestrictionPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SemilinearProperOpen.R (quotientRings l F) (quotientMaps l F) f ⋙
        derivedSystemRestriction l E F i Y ⟶
      derivedSystemRestriction l E F i X ⋙
        SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) f :=
  mateEquiv (SemilinearProperOpen.adj (quotientRings l F) (quotientMaps l F) f)
    (SemilinearProperOpen.adj (quotientRings l E) (quotientMaps l E) f)
      (systemRestrictionPull l E F i f).inv

/-- The normalized proper-image restriction comparison is an isomorphism.
Source: blueprint proof Step 10; derived ring-sheaf change adjunction
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: derive the actual ordinary restriction/direct-image square on simultaneous
K-injective resolutions. The universal derived comparison identifies that square with
the displayed adjunction mate. Its sectionwise identity inverse gives invertibility,
without requiring coefficient restriction to preserve K-injectives. -/
theorem systemRestrictionPush_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (systemRestrictionPush l E F i f) := by
  sorry

attribute [instance] systemRestrictionPush_isIso

/-- The open restriction arrow is fixed by the same pullback square and the open unit.
Source: blueprint proof Step 10
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def systemRestrictionOpenInv {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    derivedSystemRestriction l E F i X ⋙
        SemilinearProperOpen.J (quotientRings l E) (quotientMaps l E) j ⟶
      SemilinearProperOpen.J (quotientRings l F) (quotientMaps l F) j ⋙
        derivedSystemRestriction l E F i Z :=
  (mateEquiv (SemilinearProperOpen.jAdj (quotientRings l F) (quotientMaps l F) j)
    (SemilinearProperOpen.jAdj (quotientRings l E) (quotientMaps l E) j)).symm
      (systemRestrictionPull l E F i j).hom

/-- The open-unit mate is invertible on the whole ordinary derived system category.
Source: blueprint proof Step 10; Stacks 03DI
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: the underlying ordinary extension has the original sections on the open and
zero outside. Scalar restriction keeps both pieces and their open unit, so its mate
is identity on the original summands. Exact localization preserves its inverse. -/
theorem systemRestrictionOpenInv_isIso {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] : IsIso (systemRestrictionOpenInv l E F i j) := by
  sorry

attribute [instance] systemRestrictionOpenInv_isIso

/-- The canonical restriction square for the entire proper/open system functor.
Source: blueprint proof Step 10
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def systemSupportRestriction {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    derivedSystemRestriction l E F i X ⋙ systemSupport l E c ≅
      systemSupport l F c ⋙ derivedSystemRestriction l E F i Y :=
  Functor.isoWhiskerRight (asIso (systemRestrictionOpenInv l E F i c.i))
      (SemilinearProperOpen.R (quotientRings l E) (quotientMaps l E) c.g) ≪≫
    Functor.isoWhiskerLeft
      (SemilinearProperOpen.J (quotientRings l F) (quotientMaps l F) c.i)
      (asIso (systemRestrictionPush l E F i c.g)).symm

/-- The whole-system coefficient projection is this actual scalar-adjunction mate.
Source: blueprint proof Step 10
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def systemProjection {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    systemSupport l E c ⋙ (systemScalarData l E F i Y).scalar.T ⟶
      (systemScalarData l E F i X).scalar.T ⋙ systemSupport l F c :=
  ((mateEquiv (systemScalarData l E F i X).scalar.adjunction
    (systemScalarData l E F i Y).scalar.adjunction).symm
      (TwoSquare.mk _ (systemSupport l F c) (systemSupport l E c) _
        (systemSupportRestriction l E F i c).hom)).natTrans

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

section DerivedUnit
universe a av b bv d dv e ev h hv z zv w
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{w} B]
  [Abelian.HasKInjectiveResolutions A] (G : A ⥤ B) [G.Additive]


/-- The universal right-derived unit on complexes, including the canonical homotopy
quotient comparisons. Source: Stacks 0D6E; blueprint proof Steps 2--3
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def rightUnitApp (K : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      G.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso B).inv.app
      ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
    G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
    G.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).hom.app K)

/-- Naturality of the same universal unit, before any coefficient evaluation.
Source: Stacks 0D6E; blueprint proof Steps 2--3
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: compose naturality of quotientCompQhIso, the derived unit, and the quotient
comparison. The functoriality of G and associativity give the displayed equation. -/
theorem rightUnitApp_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f) ≫ rightUnitApp G L =
      rightUnitApp G K ≫ G.rightDerivedFunctor.map (DerivedCategory.Q.map f) := by
  let π := HomotopyCategory.quotient A (.up ℤ)
  let H := G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let e : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ≅ π ⋙ H :=
    Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _
  let η : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G.rightDerivedFunctor :=
    e.hom ≫ Functor.whiskerLeft π G.rightDerivedFunctorUnit ≫
      (Functor.associator _ _ _).inv ≫
      (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A)
        G.rightDerivedFunctor).hom
  have hfac (K : CochainComplex A ℤ) :
      (G.mapHomotopyCategoryFactors (.up ℤ)).inv.app K =
        𝟙 ((HomotopyCategory.quotient B (.up ℤ)).obj
          ((G.mapHomologicalComplex (.up ℤ)).obj K)) := rfl
  simpa [η, e, rightUnitApp, hfac, π] using η.naturality f

/-- The actual universal right-derived unit as one natural transformation on complexes.
Source: Stacks 0D6E; blueprint proof Steps 2--3
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def rightUnit : G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ G.rightDerivedFunctor where
  app := rightUnitApp G
  naturality := fun _ _ f ↦ rightUnitApp_naturality G f

end DerivedUnit

private theorem composed_rightUnit_naturality
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions B]
    (V : A ⥤ B) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (G : B ⥤ C) [G.Additive]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    DerivedCategory.Q.map
        ((G.mapHomologicalComplex (.up ℤ)).map
          ((V.mapHomologicalComplex (.up ℤ)).map f)) ≫
        (rightUnit G).app ((V.mapHomologicalComplex (.up ℤ)).obj L) ≫
        G.rightDerivedFunctor.map (V.mapDerivedCategoryFactors.inv.app L) =
      ((rightUnit G).app ((V.mapHomologicalComplex (.up ℤ)).obj K) ≫
        G.rightDerivedFunctor.map (V.mapDerivedCategoryFactors.inv.app K)) ≫
        G.rightDerivedFunctor.map (V.mapDerivedCategory.map (DerivedCategory.Q.map f)) := by
  change _ ≫ rightUnitApp G _ ≫ _ = _
  rw [← Category.assoc, rightUnitApp_naturality]
  simp only [Category.assoc, ← Functor.map_comp]
  apply congrArg ((rightUnit G).app ((V.mapHomologicalComplex (.up ℤ)).obj K) ≫ ·)
  exact congrArg G.rightDerivedFunctor.map
    (V.mapDerivedCategoryFactors.inv.naturality f)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ordinary limit of a strict semilinear system after its actual coefficient
restriction. Source: Zheng 4.1; blueprint proof Step 3
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def ordinarySystemLimit (W : Scheme.{u}) :
    coefficientSequenceModules.{u, u} l E W ⥤ scalarReductionSource.{u, u} l E W :=
  coefficientSequenceRestriction.{u, u} l E W ⋙
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E W) ⥤
      scalarReductionSource.{u, u} l E W)

/-- Additivity of the actual strict-system limit.
Source: Stacks 0941 (blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: restriction of scalars is additive and limits in module sheaves are formed
on the underlying additive sheaves. Thus the map of a sum of compatible sections
is the sum of their limit maps. The universal projections detect this equation. -/
theorem ordinarySystemLimit_additive (W : Scheme.{u}) :
    (ordinarySystemLimit l E W).Additive := by
  have h := coefficientConstantTowerLimitAdditive l E W
  change (coefficientSequenceRestriction l E W ⋙ lim).Additive
  infer_instance

attribute [instance] ordinarySystemLimit_additive

/-- The natural comparison from an ordinary limit on complexes to the specified total
limit: the real limit derived unit followed by exact coefficient-restriction descent.
Source: Stacks 0D6E; blueprint proof Step 3
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def limitUnitApp (W : Scheme.{u}) (K : CochainComplex
    (coefficientSequenceModules.{u, u} l E W) ℤ) :=
  (rightUnit (lim : (ℕᵒᵖ ⥤ scalarReductionSource.{u, u} l E W) ⥤
    scalarReductionSource.{u, u} l E W)).app
      (((coefficientSequenceRestriction.{u, u} l E W).mapHomologicalComplex (.up ℤ)).obj K) ≫
    (coefficientConstantTowerLimit.{u, u} l E W).map
      ((coefficientSequenceRestriction.{u, u} l E W).mapDerivedCategoryFactors.inv.app K)

/-- Naturality of the specified whole-system limit unit.
Source: Stacks 0D6E; blueprint proof Step 3
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: naturality of the real right-derived limit unit and of exact restriction's
localization comparison paste to this equation on all chain maps. -/
theorem limitUnitApp_naturality (W : Scheme.{u})
    {K L : CochainComplex (coefficientSequenceModules.{u, u} l E W) ℤ} (f : K ⟶ L) :
    DerivedCategory.Q.map (((ordinarySystemLimit l E W).mapHomologicalComplex (.up ℤ)).map f) ≫
        limitUnitApp l E W L =
      limitUnitApp l E W K ≫ (coefficientSequenceLimit.{u, u} l E W).map
        (DerivedCategory.Q.map f) := by
  exact composed_rightUnit_naturality (coefficientSequenceRestriction l E W)
    (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) f

/-- The actual total-limit comparison on complexes, retained to normalize coefficient
transport before evaluation. Source: blueprint proof Steps 3 and 10
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def limitUnit (W : Scheme.{u}) :
    (ordinarySystemLimit l E W).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientSequenceLimit.{u, u} l E W where
  app := limitUnitApp l E W
  naturality := fun _ _ f ↦ limitUnitApp_naturality l E W f

end WeilConjectures.CompactSupportCondensedRealization

namespace WeilConjectures.CompactSupportCondensedRealization

variable (l : ℕ) [Fact l.Prime] (E F : Type u) [NormedField E] [NormedField F]
  [NormedAlgebra ℚ_[l] E] [NormedAlgebra ℚ_[l] F]
  [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Actual restriction along the residue-normalized completed coefficient inclusion.
Source: blueprint proof Steps 7--11
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
abbrev completedRestriction (W : Scheme.{u}) :=
  pbcRestrict (completedCoefficientMap l E F i W)

/-- Restriction after forgetting a semilinear system equals termwise completed scalar
restriction, by the identity on underlying sections. This retains the strict diagram.
Source: blueprint proof Step 10
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: the completed inclusion followed by a target finite projection equals the
source finite projection followed by the same-index quotient inclusion. Thus the two
restricted coefficient actions agree. Identity section maps commute with all index
arrows; sectionwise faithfulness proves uniqueness. No quotient flatness is used. -/
theorem restrictionTower_existsUnique (W : Scheme.{u}) :
    ∃! d : systemRestriction l E F i W ⋙ coefficientSequenceRestriction.{u, u} l E W ≅
        coefficientSequenceRestriction.{u, u} l F W ⋙
          (Functor.whiskeringRight ℕᵒᵖ (scalarReductionSource.{u, u} l F W)
            (scalarReductionSource.{u, u} l E W)).obj (completedRestriction l E F i W),
      ∀ (M : coefficientSequenceModules.{u, u} l F W) (n : ℕ) (U : W.ProEtᵒᵖ)
        (x : (((coefficientSequenceRestriction.{u, u} l E W).obj
          ((systemRestriction l E F i W).obj M)).obj (op n)).val.obj U),
        HEq (((d.hom.app M).app (op n)).val.app U x) x := by
  sorry

/-- The uniquely section-normalized strict tower comparison.
Source: blueprint proof Step 10
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def restrictionTower (W : Scheme.{u}) :
    systemRestriction l E F i W ⋙ coefficientSequenceRestriction.{u, u} l E W ≅
      coefficientSequenceRestriction.{u, u} l F W ⋙
        (Functor.whiskeringRight ℕᵒᵖ (scalarReductionSource.{u, u} l F W)
          (scalarReductionSource.{u, u} l E W)).obj (completedRestriction l E F i W) :=
  (restrictionTower_existsUnique l E F i W).exists.choose

private theorem restriction_preserves_tower_limits
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (a : R ⟶ S) :
    PreservesLimitsOfShape ℕᵒᵖ (SheafOfModules.restrictScalars.{u + 1} a) := by
  let U := SheafOfModules.forget.{u + 1} R ⋙ PresheafOfModules.toPresheaf R.obj
  have : PreservesLimitsOfShape ℕᵒᵖ (SheafOfModules.restrictScalars.{u + 1} a ⋙ U) :=
    inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ
      (SheafOfModules.forget.{u + 1} S ⋙ PresheafOfModules.toPresheaf S.obj))
  have : ReflectsLimitsOfShape ℕᵒᵖ U :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves _ U

private theorem limit_comparison_existsUnique
    {A B C : Type*} [Category A] [Category B] [Category C]
    [HasLimitsOfShape ℕᵒᵖ B] [HasLimitsOfShape ℕᵒᵖ C]
    (R : B ⥤ C) [PreservesLimitsOfShape ℕᵒᵖ R]
    (V : A ⥤ ℕᵒᵖ ⥤ B) (U : A ⥤ ℕᵒᵖ ⥤ C)
    (e : U ≅ V ⋙ (Functor.whiskeringRight ℕᵒᵖ B C).obj R) :
    ∃! d : V ⋙ lim ⋙ R ≅ U ⋙ lim,
      ∀ (M : A) (n : ℕᵒᵖ), d.hom.app M ≫ limit.π (U.obj M) n ≫
        (e.hom.app M).app n = R.map (limit.π (V.obj M) n) := by
  let d : V ⋙ lim ⋙ R ≅ U ⋙ lim :=
    Functor.isoWhiskerLeft V (preservesLimitNatIso R) ≪≫
      Functor.isoWhiskerRight e.symm lim
  have hd (M : A) (n : ℕᵒᵖ) : d.hom.app M ≫ limit.π (U.obj M) n ≫
      (e.hom.app M).app n = R.map (limit.π (V.obj M) n) := by
    change ((preservesLimitIso R (V.obj M)).hom ≫ lim.map (e.inv.app M)) ≫ _ ≫ _ = _
    simp only [Category.assoc, lim_map, limMap_π_assoc,
      ← NatTrans.comp_app, Iso.inv_hom_id, NatTrans.id_app]
    change (preservesLimitIso R (V.obj M)).hom ≫
      limit.π (V.obj M ⋙ R) n ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact preservesLimitIso_hom_π R (V.obj M) n
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply limit.hom_ext
  intro n
  apply (cancel_mono ((e.hom.app M).app n)).mp
  simpa only [Category.assoc] using (hd' M n).trans (hd M n).symm

/-- The ordinary limit comparison is fixed by every actual strict-tower projection.
Source: Stacks 0A07; blueprint proof Step 11
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: coefficient restriction creates limits, as it leaves the underlying abelian
sheaf unchanged. Its projection cone, followed by restrictionTower inverse, is a
limiting cone on the restricted strict system. The limit universal property supplies
the displayed isomorphism and proves uniqueness from these projection equations. -/
theorem ordinaryLimitRestriction_existsUnique (W : Scheme.{u}) :
    ∃! d : ordinarySystemLimit l F W ⋙ completedRestriction l E F i W ≅
        systemRestriction l E F i W ⋙ ordinarySystemLimit l E W,
      ∀ (M : coefficientSequenceModules.{u, u} l F W) (n : ℕ),
        d.hom.app M ≫
            limit.π ((coefficientSequenceRestriction.{u, u} l E W).obj
              ((systemRestriction l E F i W).obj M)) (op n) ≫
            ((restrictionTower l E F i W).hom.app M).app (op n) =
          (completedRestriction l E F i W).map
            (limit.π ((coefficientSequenceRestriction.{u, u} l F W).obj M) (op n)) := by
  let R := completedRestriction l E F i W
  have : PreservesLimitsOfShape ℕᵒᵖ R := restriction_preserves_tower_limits
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (completedCoefficientMap l E F i W))
  obtain ⟨d, hd, hu⟩ := limit_comparison_existsUnique R
    (coefficientSequenceRestriction l F W)
    (systemRestriction l E F i W ⋙ coefficientSequenceRestriction l E W)
    (restrictionTower l E F i W)
  refine ⟨d, fun M n ↦ hd M (op n), ?_⟩
  intro d' hd'
  exact hu d' (fun M n ↦ hd' M n.unop)

/-- The canonical ordinary limit/restriction comparison.
Source: blueprint proof Step 11
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def ordinaryLimitRestriction (W : Scheme.{u}) :
    ordinarySystemLimit l F W ⋙ completedRestriction l E F i W ≅
      systemRestriction l E F i W ⋙ ordinarySystemLimit l E W :=
  (ordinaryLimitRestriction_existsUnique l E F i W).exists.choose

/-- Zero preservation of the displayed ordinary composite.
Source: blueprint proof Steps 10--12; Stacks 03DA
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: Restriction is additive sectionwise and the sectionwise inverse limit preserves zero. Their
composite therefore maps each zero arrow to zero. -/
theorem systemRestrictionLimit_zero (W : Scheme.{u}) :
    (systemRestriction l E F i W ⋙ ordinarySystemLimit l E W).PreservesZeroMorphisms := by
  constructor
  intro X Y
  have := coefficientConstantTowerLimitAdditive l E W
  change lim.map ((coefficientSequenceRestriction l E W).map
    ((systemRestriction l E F i W).map 0)) = 0
  simp only [Functor.map_zero]

attribute [instance] systemRestrictionLimit_zero

/-- Zero preservation of the opposite ordinary normalization composite.
Source: blueprint proof Steps 10--12; Stacks 03DA
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: both factors are additive on section morphisms and map zero to zero.
Their composite therefore maps the zero arrow between any two modules to zero. -/
theorem systemLimitRestriction_zero (W : Scheme.{u}) :
    (ordinarySystemLimit l F W ⋙ completedRestriction l E F i W).PreservesZeroMorphisms := by
  constructor
  intro X Y
  change (completedRestriction l E F i W).map
    ((ordinarySystemLimit l F W).map 0) = 0
  rw [Functor.map_zero, Functor.map_zero]

/-- The exact universal normalization equation on whole complexes.
Source: blueprint proof Steps 10--12; Stacks 06YY and 0D6E
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def IsLimitRestrictionNormalized (W : Scheme.{u})
    (d : coefficientSequenceLimit.{u, u} l F W ⋙
          (completedRestriction l E F i W).mapDerivedCategory ≅
        derivedSystemRestriction l E F i W ⋙ coefficientSequenceLimit.{u, u} l E W) : Prop :=
  letI := systemRestrictionLimit_zero l E F i W
  letI := systemLimitRestriction_zero l E F i W
  ∀ K : CochainComplex (coefficientSequenceModules.{u, u} l F W) ℤ,
    (completedRestriction l E F i W).mapDerivedCategory.map ((limitUnit l F W).app K) ≫
        d.hom.app (DerivedCategory.Q.obj K) ≫
        (coefficientSequenceLimit.{u, u} l E W).map
          ((systemRestriction l E F i W).mapDerivedCategoryFactors.hom.app K) =
      (completedRestriction l E F i W).mapDerivedCategoryFactors.hom.app
          (((ordinarySystemLimit l F W).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (ordinaryLimitRestriction l E F i W) (.up ℤ)).hom.app
            K) ≫
        (limitUnit l E W).app
          (((systemRestriction l E F i W).mapHomologicalComplex (.up ℤ)).obj K)

/-- Derived limit/restriction is normalized by the real universal comparison on whole
complexes, not selected by evaluated derived arrows.
Source: Stacks 0D6E and 0A07; blueprint proof Step 11
(blueprint: def-pur-semilinear-compact-support-coefficient-transport).
Proof: ordinary restriction is exact, preserves products, and carries the strict Roos
complex and both its coordinates to the same Roos complex with restricted action.
Derive the projection-normalized ordinary square. The right-derived universal unit
identifies this comparison uniquely by the displayed equation on all system complexes.
The inverse is the derived inverse ordinary square. This proves invertibility without
an assumption that arbitrary coefficient restriction preserves K-injectives. -/
theorem limitRestriction_existsUnique (W : Scheme.{u}) :
    ∃! d : coefficientSequenceLimit.{u, u} l F W ⋙
          (completedRestriction l E F i W).mapDerivedCategory ≅
        derivedSystemRestriction l E F i W ⋙ coefficientSequenceLimit.{u, u} l E W,
      IsLimitRestrictionNormalized l E F i W d := by
  sorry


/-- The normalized whole-system derived limit comparison.
Source: blueprint proof Step 11
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def limitRestriction (W : Scheme.{u}) :
    coefficientSequenceLimit.{u, u} l F W ⋙
        (completedRestriction l E F i W).mapDerivedCategory ≅
      derivedSystemRestriction l E F i W ⋙ coefficientSequenceLimit.{u, u} l E W :=
  (limitRestriction_existsUnique l E F i W).exists.choose

/-- Reduction/scalar balancing is the conjugate of the specified limit restriction
square under the actual scalar and reduction adjunctions. This defines the comparison
on the whole derived ringed sequence site.
Source: blueprint proof Steps 10--11
(blueprint: def-pur-semilinear-compact-support-coefficient-transport). -/
def reductionScalar (W : Scheme.{u})
    (RE : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (RF : CoefficientDerivedSystemCalculus.{u, u} l F W) :
    pbcDerivedExtend (completedCoefficientMap l E F i W) ⋙ RF.reduction ≅
      RE.reduction ⋙ (systemScalarData l E F i W).scalar.T :=
  (((pbcDerivedScalarAdjunction (completedCoefficientMap l E F i W)).comp
    RF.adjunction).ofNatIsoRight (limitRestriction l E F i W)).leftAdjointUniq
      (RE.adjunction.comp (systemScalarData l E F i W).scalar.adjunction)

end WeilConjectures.CompactSupportCondensedRealization
