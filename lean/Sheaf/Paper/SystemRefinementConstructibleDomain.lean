/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting
public import Sheaf.Paper.RefinementComparisonIsomorphism
public import Sheaf.Paper.ProEtaleFixedModuleConstructible
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.SystemNormalizedTensorClosure
public import Sheaf.CategoryTheory.ConstantScalarRestrictionTensor
public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import all Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
import all Sheaf.AlgebraicGeometry.VaryingRingOperations
import all Sheaf.Paper.ProEtaleConstructibleOrigin
import all Sheaf.CategoryTheory.ConstantScalarRestrictionTensor
import all Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport

/-! # Constructible domain of strict-system refinement comparisons

Source: Stacks Project, Tags 0F7B and 0F7J; blueprint compatibility (7),
levelwise domain and normalization prerequisites
(blueprint: lem-pur-system-refinement-constructible-domain).

Indices are zero based: index n denotes the positive quotient exponent n+1.
All categories of systems are ordinary unbounded derived categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SystemRefinement

private theorem ringRestrictionDirect
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (RY SY : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (RX SX : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (aY : RY ⟶ SY) (aX : RX ⟶ SX)
    (cR : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
    (cS : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)
    (comm : cR.hom ≫ aX =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ cS.hom) :
    ∃! d : Scheme.proEtaleRingRestrictScalars aX ⋙
        Scheme.proEtaleRingModuleDirectImage f RY RX cR ≅
      Scheme.proEtaleRingModuleDirectImage f SY SX cS ⋙
        Scheme.proEtaleRingRestrictScalars aY,
      HEq (Functor.whiskerRight d.hom
        (SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY)))
        (𝟙 (Scheme.proEtaleRingModuleDirectImage f SY SX cS ⋙
          SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj SY))) := by
  obtain ⟨e, he, _⟩ := Scheme.proEtaleRingRestrictionDirectImage_existsUnique
    f RY SY RX SX aY aX cR cS comm
  have hi (M : Scheme.proEtaleRingModules X SX) (U : Y.ProEtᵒᵖ)
      (x : M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U)) :
      (e.inv.app M).val.app U x = x := by
    have ht := congrArg (fun t ↦ t.val.app U x) (e.inv_hom_id_app M)
    change (e.hom.app M).val.app U ((e.inv.app M).val.app U x) = x at ht
    rw [he] at ht
    exact ht
  refine ⟨e.symm, ?_, ?_⟩
  · apply heq_of_eq
    ext M U x
    exact hi M U x
  · intro d hd
    apply Iso.ext
    ext M U x
    exact (ConcreteCategory.congr_hom
      (congr_app (congrArg (fun t ↦ (t.app M).hom) (eq_of_heq hd)) U) x).trans
        (hi M U x).symm

private theorem ringRestrictionPull
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (RY SY : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (RX SX : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (aY : RY ⟶ SY) (aX : RX ⟶ SX)
    (cR : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
    (cS : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)
    (comm : cR.hom ≫ aX =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aY ≫ cS.hom)
    (β : Scheme.proEtaleRingRestrictScalars aX ⋙
        Scheme.proEtaleRingModuleDirectImage f RY RX cR ≅
      Scheme.proEtaleRingModuleDirectImage f SY SX cS ⋙
        Scheme.proEtaleRingRestrictScalars aY)
    (hβ : HEq (Functor.whiskerRight β.hom
        (SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RY)))
        (𝟙 (Scheme.proEtaleRingModuleDirectImage f SY SX cS ⋙
          SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology Y)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj SY)))) :
    ∃! d : Scheme.proEtaleRingRestrictScalars aY ⋙
        Scheme.proEtaleRingModulePullback f RY RX cR ≅
      Scheme.proEtaleRingModulePullback f SY SX cS ⋙
        Scheme.proEtaleRingRestrictScalars aX,
      ∀ M : Scheme.proEtaleRingModules Y SY,
        (Scheme.proEtaleRingModuleAdjunction f RY RX cR).homEquiv _ _ (d.hom.app M) =
          (Scheme.proEtaleRingRestrictScalars aY).map
            ((Scheme.proEtaleRingModuleAdjunction f SY SX cS).unit.app M) ≫
              β.inv.app ((Scheme.proEtaleRingModulePullback f SY SX cS).obj M) := by
  let e := Scheme.proEtaleRingRestrictionDirectImage f RY SY RX SX aY aX cR cS comm
  have he := (Scheme.proEtaleRingRestrictionDirectImage_existsUnique
    f RY SY RX SX aY aX cR cS comm).choose_spec.1
  change ∀ (M : Scheme.proEtaleRingModules X SX) (U : Y.ProEtᵒᵖ)
    (x : M.val.obj ((Scheme.proEtaleBaseChange f).op.obj U)),
      (e.hom.app M).val.app U x = x at he
  have hed : e.symm = β := by
    apply Iso.ext
    ext M U x
    have hb : (β.hom.app M).val.app U x = x :=
      ConcreteCategory.congr_hom
        (congr_app (congrArg (fun t ↦ (t.app M).hom) (eq_of_heq hβ)) U) x
    have hi := congrArg (fun t ↦ t.val.app U x) (e.inv_hom_id_app M)
    change (e.hom.app M).val.app U ((e.inv.app M).val.app U x) = x at hi
    rw [he] at hi
    exact hi.trans hb.symm
  let t := Scheme.proEtaleRingRestrictionPullbackInv f RY SY RX SX aY aX cR cS comm
  have : IsIso t :=
    Scheme.proEtaleRingRestrictionPullbackInv_isIso f RY SY RX SX aY aX cR cS comm
  let d := asIso t
  have hd (M : Scheme.proEtaleRingModules Y SY) :
      (Scheme.proEtaleRingModuleAdjunction f RY RX cR).homEquiv _ _ (d.hom.app M) =
        (Scheme.proEtaleRingRestrictScalars aY).map
          ((Scheme.proEtaleRingModuleAdjunction f SY SX cS).unit.app M) ≫
            β.inv.app ((Scheme.proEtaleRingModulePullback f SY SX cS).obj M) := by
    rw [← hed]
    have hu := unit_mateEquiv
      (Scheme.proEtaleRingModuleAdjunction f SY SX cS)
      (Scheme.proEtaleRingModuleAdjunction f RY RX cR)
      (TwoSquare.mk _ _ _ _ t) M
    have hm := congrArg
      (fun z ↦ z.app ((Scheme.proEtaleRingModulePullback f SY SX cS).obj M))
      (Scheme.restrictionPullback_mate f RY SY RX SX aY aX cR cS comm)
    change (mateEquiv (Scheme.proEtaleRingModuleAdjunction f SY SX cS)
      (Scheme.proEtaleRingModuleAdjunction f RY RX cR) (TwoSquare.mk _ _ _ _ t)).app
        ((Scheme.proEtaleRingModulePullback f SY SX cS).obj M) =
      e.hom.app ((Scheme.proEtaleRingModulePullback f SY SX cS).obj M) at hm
    rw [hm] at hu
    exact hu.symm
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  exact ((Scheme.proEtaleRingModuleAdjunction f RY RX cR).homEquiv _ _).injective
    ((hd' M).trans (hd M).symm)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem normalizedLeftComparison
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (a : L ⊣ R) (b : L' ⊣ R') (U : C ⥤ C') (V : D ⥤ D')
    [U.IsEquivalence] [V.IsEquivalence] (β : R ⋙ U ≅ V ⋙ R') :
    ∃! d : L ⋙ V ≅ U ⋙ L', ∀ M : C,
      U.map (a.unit.app M) ≫ β.hom.app (L.obj M) ≫ R'.map (d.hom.app M) =
        b.unit.app (U.obj M) := by
  let α := ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ β.hom)).natTrans
  have : IsIso α := StrictTower.inverseMate_isIso_of_equivalences a b
    (TwoSquare.mk _ _ _ _ β.hom)
  let d := (asIso α).symm
  have hu (M : C) : U.map (a.unit.app M) ≫ β.hom.app (L.obj M) =
      b.unit.app (U.obj M) ≫ R'.map (α.app M) :=
    unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ β.hom) M
  refine ⟨d, ?_, ?_⟩
  · intro M
    rw [← Category.assoc, hu, Category.assoc, ← R'.map_comp]
    change b.unit.app (U.obj M) ≫ R'.map ((asIso α).hom.app M ≫ (asIso α).inv.app M) = _
    rw [(asIso α).hom_inv_id_app]
    exact (congrArg (fun z ↦ b.unit.app (U.obj M) ≫ z)
      (R'.map_id (L'.obj (U.obj M)))).trans (Category.comp_id _)
  · intro e he
    have hinv (M : C) : e.inv.app M = α.app M := by
      apply (b.homEquiv _ _).injective
      simp only [Adjunction.homEquiv_unit]
      rw [← hu]
      apply (cancel_mono (R'.map (e.hom.app M))).1
      rw [Category.assoc, ← R'.map_comp, e.inv_hom_id_app]
      exact ((congrArg (fun z ↦ b.unit.app (U.obj M) ≫ z)
        (R'.map_id (L'.obj (U.obj M)))).trans (Category.comp_id _)).trans
          ((he M).symm.trans (Category.assoc _ _ _).symm)
    have hs : e.symm = d.symm := by
      apply Iso.ext
      apply NatTrans.ext
      funext M
      exact hinv M
    exact congrArg Iso.symm hs

/-- The actual positive finite quotient with the site's coefficient lift.
Source: blueprint finite coefficient convention; Stacks 0F7B
(blueprint: lem-pur-system-refinement-constructible-domain). -/
abbrev rings (n : ℕ) : CommRingCat.{u + 1} :=
  IntegralSystemRealization.scalarRings l E n

/-- Adjacent maps are the actual quotient homomorphisms, conjugated by the universe lift.
Source: blueprint finite coefficient convention
(blueprint: lem-pur-system-refinement-constructible-domain). -/
abbrev transitions (n : ℕ) : rings l E (n + 1) ⟶ rings l E n :=
  IntegralSystemRealization.scalarTransitions l E n

/-- Finiteness of the positive quotients, reusing the recorded coefficient theorem.
Source: blueprint coefficient convention
(blueprint: lem-pur-system-refinement-constructible-domain). -/
instance finiteRings (n : ℕ) : Finite (rings l E n) :=
  @Finite.of_equiv _ _ (Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.succ_pos n)) Equiv.ulift.symm

/-- Fixed scalar encoding of one level is the existing exact constant-scalar restriction.
Source: Stacks 03CY; the canonical scalar comparisons in the node
(blueprint: lem-pur-system-refinement-constructible-domain). -/
abbrev fixed (X : Scheme.{u}) (n : ℕ) :=
  ConstantScalarRestriction.onDerived (Scheme.ProEt.topology X) (rings l E n)

/-- Positive-level evaluation followed by its canonical fixed-scalar encoding.
Source: Zheng 4.1 and 4.10; Stacks 03CY
(blueprint: lem-pur-system-refinement-constructible-domain). -/
abbrev level (X : Scheme.{u}) (n : ℕ) :=
  VaryingRing.ev (rings l E) (transitions l E) X n ⋙ fixed l E X n

private theorem scalarEncoding_unit (W : Scheme.{u}) (R₀ : Type u) [CommRing R₀]
    (U : W.ProEtᵒᵖ) (b : ULift.{u + 1, u} R₀) :
    (ConstantScalarRestriction.scalarUnit (Scheme.ProEt.topology W)
      (ULift.{u + 1, u} R₀)).app U b =
      (Scheme.proEtaleModuleScalarUnit W R₀).app U b := by
  let J := Scheme.ProEt.topology W
  let A := ULift.{u + 1, u} R₀
  have hc := toSheafify_naturality J
    (Functor.constComp W.ProEtᵒᵖ (CommRingCat.of A)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv
  change ((toSheafify J ((Functor.const W.ProEtᵒᵖ).obj (RingCat.of A)) ≫
    sheafifyMap J (Functor.constComp W.ProEtᵒᵖ (CommRingCat.of A)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).inv ≫
    (sheafifyComposeIso J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
      ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of A))).hom).app U) b = _
  erw [← Category.assoc, ← hc, Category.assoc, sheafComposeIso_hom_fac]
  rfl

private def restrictionEncoding (W : Scheme.{u}) (R₀ : Type u) [CommRing R₀] :
    ConstantScalarRestriction.restriction (Scheme.ProEt.topology W)
      (ULift.{u + 1, u} R₀) ≅ Scheme.proEtaleModuleRestriction W R₀ :=
  NatIso.ofComponents (fun M ↦
    { hom := ⟨{
        app := fun U ↦ ModuleCat.ofHom
          (X := ((ConstantScalarRestriction.restriction (Scheme.ProEt.topology W)
            (ULift.{u + 1, u} R₀)).obj M).obj.obj U)
          (Y := ((Scheme.proEtaleModuleRestriction W R₀).obj M).obj.obj U)
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun b x ↦ by
              let x' : M.val.obj U := x
              change (ConstantScalarRestriction.scalarUnit (Scheme.ProEt.topology W)
                (ULift.{u + 1, u} R₀)).app U b • x' =
                  (Scheme.proEtaleModuleScalarUnit W R₀).app U b • x'
              rw [scalarEncoding_unit] }
        naturality := fun _ _ _ ↦ by ext x; rfl }⟩
      inv := ⟨{
        app := fun U ↦ ModuleCat.ofHom
          (X := ((Scheme.proEtaleModuleRestriction W R₀).obj M).obj.obj U)
          (Y := ((ConstantScalarRestriction.restriction (Scheme.ProEt.topology W)
            (ULift.{u + 1, u} R₀)).obj M).obj.obj U)
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun b x ↦ by
              let x' : M.val.obj U := x
              change (Scheme.proEtaleModuleScalarUnit W R₀).app U b • x' =
                (ConstantScalarRestriction.scalarUnit (Scheme.ProEt.topology W)
                  (ULift.{u + 1, u} R₀)).app U b • x'
              rw [scalarEncoding_unit] }
        naturality := fun _ _ _ ↦ by ext x; rfl }⟩
      hom_inv_id := by ext U x; rfl
      inv_hom_id := by ext U x; rfl }) (fun _ ↦ by ext U x; rfl)

/-- The ordinary encoding/direct-image isomorphism is uniquely identity on sections.
Source: Stacks 03CY and 0D6E, canonical coefficient comparison
(blueprint: lem-pur-system-refinement-constructible-domain).
Proof: both sides evaluate N on the same base-changed pro-etale object. The coefficient
map extends constant sections, so the identity is linear. These identities are natural
and invertible. They uniquely specify the comparison at every object and every section. -/
theorem ordinaryDirect_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! d : StrictTower.moduleDirectImage (rings l E n) f ⋙
        ConstantScalarRestriction.restriction (Scheme.ProEt.topology Y) (rings l E n) ≅
      ConstantScalarRestriction.restriction (Scheme.ProEt.topology X) (rings l E n) ⋙
        lowerStar (ModuleCat.{u + 1} (rings l E n)) f,
      ∀ (N : StrictTower.Modules (rings l E n) X) (U : Y.ProEtᵒᵖ)
        (x : N.val.obj ((Scheme.proEtaleBaseChange f).op.obj U)),
        HEq ((d.hom.app N).hom.app U x) x := by
  classical
  let d := isoWhiskerLeft (StrictTower.moduleDirectImage (rings l E n) f)
      (restrictionEncoding Y (Padic.coefficientExtensionRing l E (n + 1))) ≪≫
    StrictTower.fixedDirect (rings l E n) f ≪≫
      isoWhiskerRight
        (restrictionEncoding X (Padic.coefficientExtensionRing l E (n + 1))).symm
        (lowerStar (ModuleCat.{u + 1} (rings l E n)) f)
  have hd (N : StrictTower.Modules (rings l E n) X) (U : Y.ProEtᵒᵖ)
      (x : N.val.obj ((Scheme.proEtaleBaseChange f).op.obj U)) :
      HEq ((d.hom.app N).hom.app U x) x := by
    dsimp [d, StrictTower.fixedDirect, StrictTower.ringUnitPushforwardIso,
      restrictionEncoding]
    rfl
  refine ⟨d, hd, ?_⟩
  intro e he
  apply Iso.ext
  ext N U x
  exact eq_of_heq ((he N U x).trans (hd N U x).symm)

/-- The section-normalized ordinary coefficient comparison.
Source: Stacks 03CY, 0D6E
(blueprint: lem-pur-system-refinement-constructible-domain). -/
def ordinaryDirect {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (ordinaryDirect_existsUnique l E f n).choose

/-- The canonical total derived coefficient comparison, with its resolution units.
Source: Stacks 0D6E; canonical scalar comparison
(blueprint: lem-pur-system-refinement-constructible-domain). -/
def fixedDirect {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (StrictTower.moduleDirectImage (rings l E n) f).rightDerivedFunctor ⋙ fixed l E Y n ≅
      fixed l E X n ⋙ (lowerStar (ModuleCat.{u + 1} (rings l E n)) f).rightDerivedFunctor :=
  letI := ConstantScalarRestriction.additive (Scheme.ProEt.topology X) (rings l E n)
  letI : PreservesFiniteLimits (ConstantScalarRestriction.restriction
    (Scheme.ProEt.topology X) (rings l E n)) :=
      (ConstantScalarRestriction.exact (Scheme.ProEt.topology X) (rings l E n)).1
  letI : PreservesFiniteColimits (ConstantScalarRestriction.restriction
    (Scheme.ProEt.topology X) (rings l E n)) :=
      (ConstantScalarRestriction.exact (Scheme.ProEt.topology X) (rings l E n)).2
  letI := ConstantScalarRestriction.additive (Scheme.ProEt.topology Y) (rings l E n)
  letI : PreservesFiniteLimits (ConstantScalarRestriction.restriction
    (Scheme.ProEt.topology Y) (rings l E n)) :=
      (ConstantScalarRestriction.exact (Scheme.ProEt.topology Y) (rings l E n)).1
  letI : PreservesFiniteColimits (ConstantScalarRestriction.restriction
    (Scheme.ProEt.topology Y) (rings l E n)) :=
      (ConstantScalarRestriction.exact (Scheme.ProEt.topology Y) (rings l E n)).2
  letI : (ConstantScalarRestriction.restriction (Scheme.ProEt.topology X)
    (rings l E n)).IsEquivalence := ConstantScalarRestriction.isEquivalence _ _
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived _ _).symm ≪≫
    Functor.rightDerivedFunctorNatIso (ordinaryDirect l E f n) ≪≫
    Functor.mapDerivedCategoryCompRightDerivedFunctorIso _ _

/-- The unique inverse-image encoding compatible with both adjunction units.
Source: Stacks 03CY, 03D3
(blueprint: lem-pur-system-refinement-constructible-domain).
Proof: conjugate the fixed-module inverse/direct image adjunction by the exact
encoding equivalences. The section-normalized ordinaryDirect identifies its right
adjoint with the intrinsic direct image. Uniqueness of left adjoints supplies an
isomorphism, and adjunction transposition proves precisely the displayed unit
identity. That identity determines every component by the Hom equivalences. -/
theorem ordinaryPull_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    ∃! d : StrictTower.modulePullback (rings l E n) f ⋙
        ConstantScalarRestriction.restriction (Scheme.ProEt.topology X) (rings l E n) ≅
      ConstantScalarRestriction.restriction (Scheme.ProEt.topology Y) (rings l E n) ⋙
        upperStar (ModuleCat.{u + 1} (rings l E n)) f,
      ∀ M : StrictTower.Modules (rings l E n) Y,
        (ConstantScalarRestriction.restriction (Scheme.ProEt.topology Y) (rings l E n)).map
            ((Scheme.proEtaleRingModuleAdjunction f
              (StrictTower.coefficients (rings l E n) Y)
              (StrictTower.coefficients (rings l E n) X)
              (StrictTower.constantRingIso (rings l E n) f)).unit.app M) ≫
          (ordinaryDirect l E f n).hom.app ((StrictTower.modulePullback (rings l E n) f).obj M) ≫
          (lowerStar (ModuleCat.{u + 1} (rings l E n)) f).map (d.hom.app M) =
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (rings l E n)) f).unit.app
          ((ConstantScalarRestriction.restriction (Scheme.ProEt.topology Y)
            (rings l E n)).obj M) := by
  have : (ConstantScalarRestriction.restriction (Scheme.ProEt.topology X)
      (rings l E n)).IsEquivalence := ConstantScalarRestriction.isEquivalence _ _
  have : (ConstantScalarRestriction.restriction (Scheme.ProEt.topology Y)
      (rings l E n)).IsEquivalence := ConstantScalarRestriction.isEquivalence _ _
  exact normalizedLeftComparison
    (Scheme.proEtaleRingModuleAdjunction f (StrictTower.coefficients (rings l E n) Y)
      (StrictTower.coefficients (rings l E n) X) (StrictTower.constantRingIso (rings l E n) f))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (rings l E n)) f)
    _ _ (ordinaryDirect l E f n)

/-- The normalized inverse-image encoding, uniquely fixed by its adjunction unit.
Source: Stacks 03D3 (blueprint: lem-pur-system-refinement-constructible-domain). -/
def ordinaryPull {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :=
  (ordinaryPull_existsUnique l E f n).choose

/-- The unique open-extension encoding compatible with both adjunction units.
Source: Stacks 03DI, 03D3
(blueprint: lem-pur-system-refinement-constructible-domain).
Proof: transport the fixed open adjunction through the encoding equivalences.
The inverse-image comparison identifies its right adjoint with the intrinsic
inverse image. Uniqueness of left adjoints produces the isomorphism. Its
unit identity follows by transposition, which also proves uniqueness. -/
theorem ordinaryOpen_existsUnique {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) :
    ∃! d : StrictTower.moduleJ (rings l E n) j ⋙
        ConstantScalarRestriction.restriction (Scheme.ProEt.topology X) (rings l E n) ≅
      ConstantScalarRestriction.restriction (Scheme.ProEt.topology U) (rings l E n) ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} (rings l E n)) j,
      ∀ M : StrictTower.Modules (rings l E n) U,
        (ConstantScalarRestriction.restriction (Scheme.ProEt.topology U) (rings l E n)).map
            ((StrictTower.moduleJAdj (rings l E n) j).unit.app M) ≫
          (ordinaryPull l E j n).hom.app ((StrictTower.moduleJ (rings l E n) j).obj M) ≫
          (upperStar (ModuleCat.{u + 1} (rings l E n)) j).map (d.hom.app M) =
        (openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (rings l E n)) j).unit.app
          ((ConstantScalarRestriction.restriction (Scheme.ProEt.topology U)
            (rings l E n)).obj M) := by
  have : (ConstantScalarRestriction.restriction (Scheme.ProEt.topology U)
      (rings l E n)).IsEquivalence := ConstantScalarRestriction.isEquivalence _ _
  have : (ConstantScalarRestriction.restriction (Scheme.ProEt.topology X)
      (rings l E n)).IsEquivalence := ConstantScalarRestriction.isEquivalence _ _
  exact normalizedLeftComparison (StrictTower.moduleJAdj (rings l E n) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} (rings l E n)) j)
    _ _ (ordinaryPull l E j n)

/-- The normalized open-extension encoding.
Source: Stacks 03DI (blueprint: lem-pur-system-refinement-constructible-domain). -/
def ordinaryOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :=
  (ordinaryOpen_existsUnique l E j n).choose

/-- Derived extension-by-zero encoding, obtained by exact localization.
Source: Stacks 03DI (blueprint: lem-pur-system-refinement-constructible-domain). -/
def fixedOpen {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (StrictTower.moduleJ (rings l E n) j).mapDerivedCategory ⋙ fixed l E X n ≅
      fixed l E U n ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} (rings l E n)) j).mapDerivedCategory :=
  letI := ConstantScalarRestriction.additive (Scheme.ProEt.topology U) (rings l E n)
  letI : PreservesFiniteLimits (ConstantScalarRestriction.restriction
    (Scheme.ProEt.topology U) (rings l E n)) :=
      (ConstantScalarRestriction.exact (Scheme.ProEt.topology U) (rings l E n)).1
  letI : PreservesFiniteColimits (ConstantScalarRestriction.restriction
    (Scheme.ProEt.topology U) (rings l E n)) :=
      (ConstantScalarRestriction.exact (Scheme.ProEt.topology U) (rings l E n)).2
  letI := ConstantScalarRestriction.additive (Scheme.ProEt.topology X) (rings l E n)
  letI : PreservesFiniteLimits (ConstantScalarRestriction.restriction
    (Scheme.ProEt.topology X) (rings l E n)) :=
      (ConstantScalarRestriction.exact (Scheme.ProEt.topology X) (rings l E n)).1
  letI : PreservesFiniteColimits (ConstantScalarRestriction.restriction
    (Scheme.ProEt.topology X) (rings l E n)) :=
      (ConstantScalarRestriction.exact (Scheme.ProEt.topology X) (rings l E n)).2
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (ordinaryOpen l E j n) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Evaluation of proper direct image in the fixed scalar presentation.
Source: Zheng 4.10; Stacks 0D6E
(blueprint: lem-pur-system-refinement-constructible-domain). -/
def pushLevel {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    VaryingRing.P (rings l E) (transitions l E) f ⋙ level l E Y n ≅
      level l E X n ⋙
        (lowerStar (ModuleCat.{u + 1} (rings l E n)) f).rightDerivedFunctor :=
  isoWhiskerRight (VaryingRing.evalP (rings l E) (transitions l E) f n) (fixed l E Y n) ≪≫
    isoWhiskerLeft (VaryingRing.ev (rings l E) (transitions l E) X n) (fixedDirect l E f n)

/-- Evaluation of extension by zero in the fixed scalar presentation.
Source: Zheng 4.10; Stacks 03DI
(blueprint: lem-pur-system-refinement-constructible-domain). -/
def openLevel {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    VaryingRing.J (rings l E) (transitions l E) j ⋙ level l E X n ≅
      level l E U n ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} (rings l E n)) j).mapDerivedCategory :=
  isoWhiskerRight (VaryingRing.evalJ (rings l E) (transitions l E) j n) (fixed l E X n) ≪≫
    isoWhiskerLeft (VaryingRing.ev (rings l E) (transitions l E) U n) (fixedOpen l E j n)

/-- The levelwise intrinsic bounded-constructible domain, without a common degree bound.
Source: Stacks 0F7B; blueprint intrinsic constructibility
(blueprint: lem-pur-system-refinement-constructible-domain). -/
abbrev domain (X : Scheme.{u})
    (K : VaryingRing.Derived (rings l E) (transitions l E) X) : Prop :=
  ∀ n : ℕ, Scheme.intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) X
    ((VaryingRing.ev (rings l E) (transitions l E) X n).obj K)

/-- The actual commutative coefficient sheaf at each positive level.
Source: Stacks 03CY (blueprint: lem-pur-system-refinement-constructible-domain). -/
abbrev B (W : Scheme.{u}) := VaryingRing.coefficients (rings l E) W

/-- The actual quotient transitions on coefficient sheaves.
Source: Zheng 4.1 (blueprint: lem-pur-system-refinement-constructible-domain). -/
abbrev tau (W : Scheme.{u}) := VaryingRing.coefficientTransition (rings l E) (transitions l E) W

/-- A model of the recorded normalized simultaneous system tensor calculus.
Source: Zheng 4.1, 4.10; Stacks 06YS
(blueprint: lem-pur-system-refinement-constructible-domain). -/
abbrev Calculus (W : Scheme.{u}) :=
  SemilinearSections.Data.{u + 1, u, u + 1} (Scheme.ProEt.topology W) (B l E W) (tau l E W)

/-- The composite actual coefficient quotient map.
Source: Zheng 4.1 (blueprint: lem-pur-system-refinement-constructible-domain). -/
def quotient (W : Scheme.{u}) {m n : ℕ} (h : n ≤ m) :
    B l E W m ⟶ B l E W n :=
  SemilinearSections.coefficientMap.{u + 1, u, u + 1}
    (Scheme.ProEt.topology W) (B l E W) (tau l E W) h

private theorem quotient_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :
    quotient l E Y h ≫
        Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (rings l E n) =
      Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (rings l E m) ≫
        (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
          (quotient l E X h) := by
  let δ : SemilinearSections.rings (Scheme.ProEt.topology Y) (B l E Y) (tau l E Y) ⟶
      SemilinearSections.rings (Scheme.ProEt.topology X) (B l E X) (tau l E X) ⋙
        Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1} :=
    NatTrans.ofOpSequence
      (fun k ↦ Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (rings l E k))
      (by
        intro k
        dsimp only [SemilinearSections.rings, Functor.comp_map]
        simp only [Functor.ofOpSequence_map_homOfLE_succ]
        exact VaryingRing.constantMap_naturality f (transitions l E k))
  exact δ.naturality (homOfLE h).op

private theorem quotient_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :
    (StrictTower.constantRingIso (rings l E m) f).hom ≫ quotient l E X h =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map (quotient l E Y h) ≫
        (StrictTower.constantRingIso (rings l E n) f).hom := by
  apply ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
  simpa only [StrictTower.constantRingIso, asIso_hom,
    Scheme.proEtaleConstantInverseImageMap, ← Adjunction.homEquiv_counit,
    Equiv.apply_symm_apply] using (quotient_naturality l E f h).symm

/-- Restriction and ordinary direct image commute by the identity on sections.
Source: Stacks 03CY, 03CZ
(blueprint: lem-pur-system-refinement-constructible-domain).
Proof: both functors have the same underlying section groups over each base-changed
object. The coefficient actions agree because constant quotient homomorphisms commute
with constant-section extension. Identity section maps therefore are linear and natural,
and are their own inverses. Their section formula proves uniqueness. -/
theorem restrictionDirect_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :
    ∃! d : SemilinearSections.res (quotient l E X h) ⋙
        StrictTower.moduleDirectImage (rings l E m) f ≅
      StrictTower.moduleDirectImage (rings l E n) f ⋙
        SemilinearSections.res (quotient l E Y h),
      HEq (Functor.whiskerRight d.hom
          (SheafOfModules.toSheaf (SemilinearSections.ring (Scheme.ProEt.topology Y) (B l E Y m))))
        (𝟙 (StrictTower.moduleDirectImage (rings l E n) f ⋙
          SheafOfModules.toSheaf
            (SemilinearSections.ring (Scheme.ProEt.topology Y) (B l E Y n)))) := by
  exact ringRestrictionDirect f
    (StrictTower.coefficients (rings l E m) Y) (StrictTower.coefficients (rings l E n) Y)
    (StrictTower.coefficients (rings l E m) X) (StrictTower.coefficients (rings l E n) X)
    (quotient l E Y h) (quotient l E X h)
    (StrictTower.constantRingIso (rings l E m) f)
    (StrictTower.constantRingIso (rings l E n) f) (quotient_square l E f h)

/-- Section-normalized restriction/direct-image comparison.
Source: Stacks 03CZ (blueprint: lem-pur-system-refinement-constructible-domain). -/
def restrictionDirect {X Y : Scheme.{u}} (f : X ⟶ Y) {m n : ℕ} (h : n ≤ m) :=
  (restrictionDirect_existsUnique l E f h).choose

/-- Restriction/inverse image is the mate of the section-normalized direct comparison.
Source: Stacks 03D3, 03CZ
(blueprint: lem-pur-system-refinement-constructible-domain).
Proof: take the inverse-image/direct-image adjunction mate of restrictionDirect.
For constant coefficients inverse image is inverse image of the underlying sheaf,
so this mate is identity on the inverse-image underlying sheaf and is invertible.
Its displayed ordinary unit identity determines its components uniquely. -/
theorem restrictionPull_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) :
    ∃! d : SemilinearSections.res (quotient l E Y h) ⋙
        StrictTower.modulePullback (rings l E m) f ≅
      StrictTower.modulePullback (rings l E n) f ⋙
        SemilinearSections.res (quotient l E X h),
      ∀ M : StrictTower.Modules (rings l E n) Y,
        (Scheme.proEtaleRingModuleAdjunction f
          (StrictTower.coefficients (rings l E m) Y)
          (StrictTower.coefficients (rings l E m) X)
          (StrictTower.constantRingIso (rings l E m) f)).homEquiv _ _ (d.hom.app M) =
        (SemilinearSections.res (quotient l E Y h)).map
          ((Scheme.proEtaleRingModuleAdjunction f
            (StrictTower.coefficients (rings l E n) Y)
            (StrictTower.coefficients (rings l E n) X)
            (StrictTower.constantRingIso (rings l E n) f)).unit.app M) ≫
          (restrictionDirect l E f h).inv.app
            ((StrictTower.modulePullback (rings l E n) f).obj M) := by
  exact ringRestrictionPull f
    (StrictTower.coefficients (rings l E m) Y) (StrictTower.coefficients (rings l E n) Y)
    (StrictTower.coefficients (rings l E m) X) (StrictTower.coefficients (rings l E n) X)
    (quotient l E Y h) (quotient l E X h)
    (StrictTower.constantRingIso (rings l E m) f)
    (StrictTower.constantRingIso (rings l E n) f) (quotient_square l E f h)
    (restrictionDirect l E f h) (restrictionDirect_existsUnique l E f h).choose_spec.1

/-- The ordinary restriction/inverse-image comparison with its fixed mate normalization.
Source: Stacks 03CZ (blueprint: lem-pur-system-refinement-constructible-domain). -/
def restrictionPull {X Y : Scheme.{u}} (f : X ⟶ Y) {m n : ℕ} (h : n ≤ m) :=
  (restrictionPull_existsUnique l E f h).choose

/-- Localization of the normalized restriction/inverse-image comparison.
Source: Stacks 07A4 (blueprint: lem-pur-system-refinement-constructible-domain). -/
def derivedRestrictionPull {X Y : Scheme.{u}} (f : X ⟶ Y) {m n : ℕ} (h : n ≤ m) :=
  (Functor.mapDerivedCategoryCompIso
    (SemilinearSections.res (quotient l E Y h))
    (StrictTower.modulePullback (rings l E m) f)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (restrictionPull l E f h) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Scalar extension/inverse image is fixed by its scalar-adjunction transpose.
Source: Stacks 07A4, 06YS
(blueprint: lem-pur-system-refinement-constructible-domain).
Proof: on K-flat representatives, inverse image commutes with extension of scalars
by the ordinary tensor associator. Its inverse has the displayed scalar-adjunction
transpose: pull the scalar unit, then use the identity-on-underlying-sheaves
restriction comparison. These formulas are natural and descend through all
quasi-isomorphisms. The scalar Hom equivalence determines every component uniquely. -/
theorem scalarPull_existsUnique (A : ∀ W : Scheme.{u}, Calculus l E W)
    {X Y : Scheme.{u}} (f : X ⟶ Y) {m n : ℕ} (h : n ≤ m) :
    ∃! d : ((A Y).scalar h).T ⋙
        (StrictTower.modulePullback (rings l E n) f).mapDerivedCategory ≅
      (StrictTower.modulePullback (rings l E m) f).mapDerivedCategory ⋙ ((A X).scalar h).T,
      ∀ P : DerivedCategory (StrictTower.Modules (rings l E m) Y),
        ((A X).scalar h).adjunction.homEquiv _ _ (d.inv.app P) =
          (StrictTower.modulePullback (rings l E m) f).mapDerivedCategory.map
            (((A Y).scalar h).adjunction.unit.app P) ≫
            (derivedRestrictionPull l E f h).hom.app (((A Y).scalar h).T.obj P) := by
  sorry

/-- The canonical scalar-extension/inverse-image comparison.
Source: Stacks 07A4 (blueprint: lem-pur-system-refinement-constructible-domain). -/
def scalarPull (A : ∀ W : Scheme.{u}, Calculus l E W)
    {X Y : Scheme.{u}} (f : X ⟶ Y) {m n : ℕ} (h : n ≤ m) :=
  (scalarPull_existsUnique l E A f h).choose

/-- Transition-adjoints are those of the actual semilinear transitions.
Source: Zheng 4.1 (blueprint: lem-pur-system-refinement-constructible-domain). -/
abbrev reduction (A : ∀ W : Scheme.{u}, Calculus l E W) (W : Scheme.{u})
    {m n : ℕ} (h : n ≤ m)
    (M : VaryingRing.Derived (rings l E) (transitions l E) W) :=
  SemilinearSections.reduction.{u + 1, u, u + 1}
    (Scheme.ProEt.topology W) (B l E W) (tau l E W) h ((A W).scalar h) M

/-- Normalization means invertibility of all actual transition-adjoints.
Source: Zheng 4.10 (blueprint: lem-pur-system-refinement-constructible-domain). -/
abbrev normalized (A : ∀ W : Scheme.{u}, Calculus l E W) (W : Scheme.{u})
    (M : VaryingRing.Derived (rings l E) (transitions l E) W) :=
  SemilinearSections.Normalized.{u + 1, u, u + 1}
    (Scheme.ProEt.topology W) (B l E W) (tau l E W) (A W).scalar M

/-- Finite Tor amplitude uses the recorded pro-etale predicate on each actual level.
Source: Stacks 08FZ (blueprint: lem-pur-system-refinement-constructible-domain). -/
abbrev tor (W : Scheme.{u}) (n : ℕ)
    (M : VaryingRing.Derived (rings l E) (transitions l E) W) (a b : ℤ) :=
  Scheme.HasProEtaleTorAmplitude W (Padic.coefficientExtensionRing l E (n + 1))
    ((VaryingRing.ev (rings l E) (transitions l E) W n).obj M) a b

/-- Bounded intrinsic constructibility and finite Tor amplitude independently at each level.
Source: Stacks 08FZ; blueprint D^b_ctf
(blueprint: lem-pur-system-refinement-constructible-domain). -/
abbrev ctf (W : Scheme.{u})
    (M : VaryingRing.Derived (rings l E) (transitions l E) W) : Prop :=
  ∀ n : ℕ, finiteTorConstructible l E (n + 1) (Nat.succ_pos n) W
    ((VaryingRing.ev (rings l E) (transitions l E) W n).obj M)

variable {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]

/-- Compactification opens are quasi-compact for a quasi-compact f.
Source: Stacks 0F7J (blueprint: lem-pur-system-refinement-constructible-domain). -/
instance compactificationOpenQuasiCompact (c : Compactification f) : QuasiCompact c.i :=
  c.quasiCompact_openImmersion inferInstance

/-- The actual geometric mate, with the canonical identity-edge identification.
Its underlying inverse-image arrow is the open comparison followed by clopen projection.
Source: Stacks 0F7B; varying-ring proper/open pasting
(blueprint: lem-pur-system-refinement-constructible-domain). -/
def gamma {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (K : VaryingRing.Derived (rings l E) (transitions l E) X) :=
  (VaryingRing.J (rings l E) (transitions l E) c₂.i).map
      ((VaryingRing.pId (rings l E) (transitions l E) X).inv.app K) ≫
    (VaryingRing.gamma (rings l E) (transitions l E) c₁.i (𝟙 X) r.hom c₂.i
      (r.i_hom.trans (Category.id_comp _).symm)).app K

/-- Evaluation of the actual refinement mate is the constant-ring normalized mate.
The identity-edge factor is retained explicitly on the finite side.
Source: Stacks 0F7B; varying-ring proper/open mate evaluation
(blueprint: lem-pur-system-refinement-constructible-domain).
Proof: expand gamma as the canonical identity-edge map followed by the proper/open
mate. Apply gamma_evaluation of varying-ring proper/open pasting. Naturality of
open evaluation moves the identity-edge factor through that comparison. Functoriality
then gives exactly the displayed word, with no conservativity or faithfulness argument. -/
theorem gamma_evaluation {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (K : VaryingRing.Derived (rings l E) (transitions l E) X) (n : ℕ) :
    (VaryingRing.ev (rings l E) (transitions l E) c₂.Z n).map (gamma l E r K) ≫
        (VaryingRing.evalP (rings l E) (transitions l E) r.hom n).hom.app
          ((VaryingRing.J (rings l E) (transitions l E) c₁.i).obj K) ≫
        (StrictTower.moduleDirectImage (rings l E n) r.hom).rightDerivedFunctor.map
          ((VaryingRing.evalJ (rings l E) (transitions l E) c₁.i n).hom.app K) =
      (VaryingRing.evalJ (rings l E) (transitions l E) c₂.i n).hom.app K ≫
        (StrictTower.moduleJ (rings l E n) c₂.i).mapDerivedCategory.map
          ((VaryingRing.ev (rings l E) (transitions l E) X n).map
              ((VaryingRing.pId (rings l E) (transitions l E) X).inv.app K) ≫
            (VaryingRing.evalP (rings l E) (transitions l E) (𝟙 X) n).hom.app K) ≫
        VaryingRing.constantGamma (rings l E n) c₁.i (𝟙 X) r.hom c₂.i
          (r.i_hom.trans (Category.id_comp _).symm)
          ((VaryingRing.ev (rings l E) (transitions l E) X n).obj K) := by
  dsimp only [gamma]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [VaryingRing.gamma_evaluation]
  have hn := (VaryingRing.evalJ (rings l E) (transitions l E) c₂.i n).hom.naturality
    ((VaryingRing.pId (rings l E) (transitions l E) X).inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [reassoc_of% hn]
  rw [Functor.map_comp]
  simp only [Category.assoc]

/-- The compactification candidate on the ordinary unbounded system derived category.
Source: Stacks 0F7J (blueprint: lem-pur-system-refinement-constructible-domain). -/
abbrev image (c : Compactification f) :=
  VaryingRing.J (rings l E) (transitions l E) c.i ⋙
    VaryingRing.P (rings l E) (transitions l E) c.g

/-- The canonical compositor in the orientation R_p1 to R_p2 R_u.
Source: Stacks 0D6E, 0F7J
(blueprint: lem-pur-system-refinement-constructible-domain). -/
def compositor {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂) :
    VaryingRing.P (rings l E) (transitions l E) c₁.g ≅
      VaryingRing.P (rings l E) (transitions l E) r.hom ⋙
        VaryingRing.P (rings l E) (transitions l E) c₂.g :=
  eqToIso (congrArg (fun g ↦ VaryingRing.P (rings l E) (transitions l E) g)
    r.hom_g.symm) ≪≫ (VaryingRing.pComp (rings l E) (transitions l E) r.hom c₂.g).symm

/-- Evaluation of the compactification candidate, including both canonical comparisons.
Source: Stacks 0D6E, 03DI
(blueprint: lem-pur-system-refinement-constructible-domain). -/
def imageLevel (c : Compactification f) (n : ℕ) :
    image l E c ⋙ level l E Y n ≅
      level l E X n ⋙ rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (rings l E n)) c :=
  isoWhiskerLeft (VaryingRing.J (rings l E) (transitions l E) c.i)
      (pushLevel l E c.g n) ≪≫
    isoWhiskerRight (openLevel l E c.i n)
      (lowerStar (ModuleCat.{u + 1} (rings l E n)) c.g).rightDerivedFunctor

section Geometry
variable (F : FiniteFieldDatum.{u}) (hl : l ≠ F.p)
  [overX : X.Over (Spec (.of F.k))] [overY : Y.Over (Spec (.of F.k))]
  [separatedX : IsSeparated (X ↘ Spec (.of F.k))]
  [finiteTypeX : LocallyOfFiniteType (X ↘ Spec (.of F.k))]
  [quasiCompactX : QuasiCompact (X ↘ Spec (.of F.k))]
  [separatedY : IsSeparated (Y ↘ Spec (.of F.k))]
  [finiteTypeY : LocallyOfFiniteType (Y ↘ Spec (.of F.k))]
  [quasiCompactY : QuasiCompact (Y ↘ Spec (.of F.k))]
  [overF : f.IsOver (Spec (.of F.k))] [separatedF : IsSeparated f]
  [finiteTypeF : LocallyOfFiniteType f]

set_option linter.unusedSectionVars false in
include F hl in
/-- Every positive level separately has a bounded constructible etale origin.
Source: Stacks 098T; blueprint lem-sf-proetale-constructible-origin
(blueprint: lem-pur-system-refinement-constructible-domain).
Proof: apply bounded constructible essential surjectivity of the recorded origin
comparison to the intrinsically constructible level. Its positive quotient ring is
finite and ell is invertible. Exact coefficient realization gives the displayed
fixed-scalar isomorphism. The argument is independent for each n. -/
theorem level_origin (K : VaryingRing.Derived (rings l E) (transitions l E) X)
    (hK : domain l E X K) (n : ℕ) :
    ∃ L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (rings l E n))),
      Etale.DerivedCategory.isBoundedConstructible (rings l E n) X L.obj ∧
        Nonempty ((comparisonUpperStar (ModuleCat.{u + 1} (rings l E n)) X).mapDerivedCategory.obj
          L.obj ≅
          (level l E X n).obj K) := by
  classical
  let R₀ := Padic.coefficientExtensionRing l E (n + 1)
  have : Finite R₀ := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  let Q := (VaryingRing.ev (rings l E) (transitions l E) X n).obj K
  let U := ConstantScalarRestriction.restriction (Scheme.ProEt.topology X) (rings l E n)
  have : U.Additive := ConstantScalarRestriction.additive _ _
  have hc (q : ℤ) : IsConstructible (rings l E n)
      ((DerivedCategory.homologyFunctor _ q).obj (U.mapDerivedCategory.obj Q)) := by
    have hs := (Scheme.proEtaleModuleRestriction_constructible_iff X R₀ _).mp ((hK n).2 q)
    have hs' := isConstructible_of_iso
      ((restrictionEncoding X R₀).symm.app ((DerivedCategory.homologyFunctor _ q).obj Q)) hs
    exact isConstructible_of_iso ((U.mapDerivedCategoryHomologyFunctorIso q).app Q) hs'
  obtain ⟨a, ha⟩ := (hK n).1.bddBelow
  obtain ⟨b, hb⟩ := (hK n).1.bddAbove
  have hz (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor _ q).obj Q) := by
    by_contra hn
    rcases hq with hq | hq
    · exact (not_lt_of_ge (ha hn)) hq
    · exact (not_lt_of_ge (hb hn)) hq
  obtain ⟨L, hL, he⟩ := fixedDerivedOrigin X (rings l E n)
    (U.mapDerivedCategory.obj Q) hc a b
    (fun q hq ↦ U.isZero_homologyFunctor_mapDerivedCategory_obj (hz q hq))
  have hplus : DerivedCategory.TStructure.t.plus L := by
    obtain ⟨c, d, _, hcd⟩ := hL.2
    exact ⟨c, (DerivedCategory.isGE_iff L c).mpr (fun q hq ↦ hcd q (Or.inl hq))⟩
  exact ⟨⟨L, hplus⟩, hL, he⟩

include F hl overX overY separatedX finiteTypeX quasiCompactX
  separatedY finiteTypeY quasiCompactY overF separatedF finiteTypeF in
/-- The evaluated mate is the named proper/open map transported along every origin witness.
Source: Stacks 0F7B; refinement comparison definition, clause (a)
(blueprint: lem-pur-system-refinement-constructible-domain).
Proof: use gamma_evaluation to identify the actual mate with the constant-ring clopen
projection mate. On the bounded etale origin, strict-tower proper/open normalization
and proper-open-comparison-site-normalization identify this with properOpenProEtaleIso.
Naturality conjugates by the arbitrary alpha. The identity-edge normalization supplies
exactly j2! of alpha inverse, followed by the named mate, followed by Ru* j1! of alpha.
Each witness is treated separately; no compatibility of witnesses or evaluation
faithfulness is used. -/
theorem gamma_witness_evaluation {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (K : VaryingRing.Derived (rings l E) (transitions l E) X)
    (hK : domain l E X K) (n : ℕ)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (rings l E n))))
    (hL : Etale.DerivedCategory.isBoundedConstructible (rings l E n) X L.obj)
    (alpha : (comparisonUpperStar (ModuleCat.{u + 1} (rings l E n)) X).mapDerivedCategory.obj
      L.obj ≅ (level l E X n).obj K) :
    (level l E c₂.Z n).map (gamma l E r K) ≫
        (pushLevel l E r.hom n).hom.app
          ((VaryingRing.J (rings l E) (transitions l E) c₁.i).obj K) ≫
        (lowerStar (ModuleCat.{u + 1} (rings l E n)) r.hom).rightDerivedFunctor.map
          ((openLevel l E c₁.i n).hom.app K) =
      (openLevel l E c₂.i n).hom.app K ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} (rings l E n))
          c₂.i).mapDerivedCategory.map alpha.inv ≫
        (properOpenProEtaleIso (rings l E n) r.hom c₁.i c₂.i r.i_hom L).hom ≫
        (lowerStar (ModuleCat.{u + 1} (rings l E n)) r.hom).rightDerivedFunctor.map
          ((openImmersionLowerShriek (ModuleCat.{u + 1} (rings l E n))
            c₁.i).mapDerivedCategory.map alpha.hom) := by
  sorry

include F hl overX overY separatedX finiteTypeX quasiCompactX
  separatedY finiteTypeY quasiCompactY overF separatedF finiteTypeF in
/-- Constructible systems admit the actual inverse refinement mate.
Source: Stacks 0F7B, 0F7J
(blueprint: lem-pur-system-refinement-constructible-domain).
Proof: at each positive level, bounded intrinsic constructibility gives a bounded
constructible etale origin. The constant finite-ring proper/open theorem makes the
normalized mate invertible there. Varying-ring mate evaluation identifies this with
the evaluation of gamma, including its canonical identity edge. The evaluation
functors jointly detect isomorphisms in the ordinary derived system category.
No common bound, normalization of K, or faithfulness on morphisms is used. -/
theorem gamma_isIso {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (K : VaryingRing.Derived (rings l E) (transitions l E) X)
    (hK : domain l E X K) : IsIso (gamma l E r K) := by
  classical
  let S := (SemilinearSections.semilinearDerivedSections.{u + 1, u, u + 1}
    (Scheme.ProEt.topology c₂.Z) (B l E c₂.Z) (tau l E c₂.Z)).some
  apply S.systems.detects
  intro n
  obtain ⟨L, hL, ⟨alpha⟩⟩ := level_origin l E F hl K hK n
  have he := gamma_witness_evaluation l E F hl r K hK n L hL alpha
  have : IsIso ((level l E c₂.Z n).map (gamma l E r K) ≫
      (pushLevel l E r.hom n).hom.app
        ((VaryingRing.J (rings l E) (transitions l E) c₁.i).obj K) ≫
      (lowerStar (ModuleCat.{u + 1} (rings l E n)) r.hom).rightDerivedFunctor.map
        ((openLevel l E c₁.i n).hom.app K)) := by
    rw [he]
    infer_instance
  have := IsIso.of_isIso_comp_right
    ((level l E c₂.Z n).map (gamma l E r K))
    ((pushLevel l E r.hom n).hom.app
      ((VaryingRing.J (rings l E) (transitions l E) c₁.i).obj K) ≫
      (lowerStar (ModuleCat.{u + 1} (rings l E n)) r.hom).rightDerivedFunctor.map
        ((openLevel l E c₁.i n).hom.app K))
  have : IsIso ((fixed l E c₂.Z n).map
      ((VaryingRing.ev (rings l E) (transitions l E) c₂.Z n).map (gamma l E r K))) :=
    inferInstanceAs (IsIso ((level l E c₂.Z n).map (gamma l E r K)))
  have : (fixed l E c₂.Z n).IsEquivalence :=
    ConstantScalarRestriction.derived_isEquivalence _ _
  exact isIso_of_reflects_iso
    ((VaryingRing.ev (rings l E) (transitions l E) c₂.Z n).map (gamma l E r K))
    (fixed l E c₂.Z n)

/-- Refinement comparison is the canonical compositor followed by the inverse actual mate.
Source: Stacks 0F7J (blueprint: lem-pur-system-refinement-constructible-domain). -/
def theta {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (K : VaryingRing.Derived (rings l E) (transitions l E) X)
    (hK : domain l E X K) : (image l E c₁).obj K ≅ (image l E c₂).obj K :=
  (compositor l E r).app ((VaryingRing.J (rings l E) (transitions l E) c₁.i).obj K) ≪≫
    (VaryingRing.P (rings l E) (transitions l E) c₂.g).mapIso
      (@asIso _ _ _ _ (gamma l E r K) (gamma_isIso l E F hl r K hK)).symm

include F hl overX overY separatedX finiteTypeX quasiCompactX
  separatedY finiteTypeY quasiCompactY overF separatedF finiteTypeF in
/-- Evaluation is exactly the specified finite refinement arrow, for every origin witness.
Source: Stacks 0F7B, 0F7J; definition of the refinement comparison
(blueprint: lem-pur-system-refinement-constructible-domain).
Proof: varying-ring proper/open pasting evaluates gamma to the constant finite-ring
mate. Finite-etale proper/open interchange and site normalization identify that
mate with properOpenProEtaleIso for the chosen L. Naturality transports the equality
along any alpha. Evaluation preserves the canonical direct-image compositor and
inverses. Thus the inverse-mate composite evaluates to properTransportRefinement,
conjugated by alpha. This works for every witness independently and never infers
equality of system maps from their evaluations. -/
theorem theta_evaluation {c₁ c₂ : Compactification f} (r : c₁.Refinement c₂)
    (K : VaryingRing.Derived (rings l E) (transitions l E) X)
    (hK : domain l E X K) (n : ℕ)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (rings l E n))))
    (hL : Etale.DerivedCategory.isBoundedConstructible (rings l E n) X L.obj)
    (alpha : (comparisonUpperStar (ModuleCat.{u + 1} (rings l E n)) X).mapDerivedCategory.obj
          L.obj ≅
          (level l E X n).obj K) :
    (level l E Y n).mapIso (theta l E F hl r K hK) ≪≫ (imageLevel l E c₂ n).app K =
      (imageLevel l E c₁ n).app K ≪≫
        (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (rings l E n)) c₁).mapIso alpha.symm ≪≫
        properTransportRefinement (rings l E n) r L ≪≫
        (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (rings l E n)) c₂).mapIso alpha := by
  sorry

include F hl overX overY separatedX finiteTypeX quasiCompactX
  separatedY finiteTypeY quasiCompactY overF separatedF finiteTypeF in
/-- Normalized constructible finite-Tor systems are closed under the stated operations,
with the individual Tor intervals and both actual transition formulas.
Source: Stacks 07A4, 06YS, 08FZ; blueprint lem-sf-tensor-ctf (i),(ii)
(blueprint: lem-pur-system-refinement-constructible-domain).
Proof: the scalar-adjunction transpose defining scalarPull is the canonical inverse
image/extension comparison. Pull the actual transition and transpose; the unit
identity of restrictionPull gives the first displayed reduction formula. Since N is
normalized, its pull reduction is invertible. Apply normalized_tensor_closure on X
to M and that pull, obtaining tensor normalization and the second displayed formula.
At each positive level, exact inverse-image evaluation and pullback-tor-amplitude
preserve bounded constructibility and the Tor interval of N. Tensor-ctf preserves
bounded constructibility and adds its interval to that of M. Apply these results
separately for every level to obtain ctf for both objects, without a common bound.
Their domain assertions permit gamma_isIso, level_origin and theta_evaluation for
M and for the tensor. This asserts nothing about normalization after proper image. -/
theorem normalized_operations (A : ∀ W : Scheme.{u}, Calculus l E W)
    (M : VaryingRing.Derived (rings l E) (transitions l E) X)
    (N : VaryingRing.Derived (rings l E) (transitions l E) Y)
    (hM : normalized l E A X M) (hN : normalized l E A Y N)
    (hcM : ctf l E X M) (hcN : ctf l E Y N) :
    normalized l E A X ((VaryingRing.G (rings l E) (transitions l E) f).obj N) ∧
    normalized l E A X ((A X).closed.tensor.obj
      (M, (VaryingRing.G (rings l E) (transitions l E) f).obj N)) ∧
    ctf l E X ((VaryingRing.G (rings l E) (transitions l E) f).obj N) ∧
    ctf l E X ((A X).closed.tensor.obj
      (M, (VaryingRing.G (rings l E) (transitions l E) f).obj N)) ∧
    (∀ (n : ℕ) (a b c d : ℤ), tor l E X n M a b → tor l E Y n N c d →
      tor l E X n ((VaryingRing.G (rings l E) (transitions l E) f).obj N) c d ∧
      tor l E X n ((A X).closed.tensor.obj
        (M, (VaryingRing.G (rings l E) (transitions l E) f).obj N)) (a + c) (b + d)) ∧
    (∀ {m n : ℕ} (h : n ≤ m),
      reduction l E A X h ((VaryingRing.G (rings l E) (transitions l E) f).obj N) ≫
          (VaryingRing.evalG (rings l E) (transitions l E) f n).hom.app N =
        ((A X).scalar h).T.map
            ((VaryingRing.evalG (rings l E) (transitions l E) f m).hom.app N) ≫
          (scalarPull l E A f h).inv.app
            ((VaryingRing.ev (rings l E) (transitions l E) Y m).obj N) ≫
          (StrictTower.modulePullback (rings l E n) f).mapDerivedCategory.map
            (reduction l E A Y h N)) ∧
    (∀ {m n : ℕ} (h : n ≤ m),
      reduction l E A X h ((A X).closed.tensor.obj
          (M, (VaryingRing.G (rings l E) (transitions l E) f).obj N)) ≫
          ((A X).tensorEvaluation n).hom.app
            (M, (VaryingRing.G (rings l E) (transitions l E) f).obj N) =
        ((A X).scalar h).T.map (((A X).tensorEvaluation m).hom.app
            (M, (VaryingRing.G (rings l E) (transitions l E) f).obj N)) ≫
          ((A X).scalarTensor h).hom.app
            ((VaryingRing.ev (rings l E) (transitions l E) X m).obj M,
              (VaryingRing.ev (rings l E) (transitions l E) X m).obj
                ((VaryingRing.G (rings l E) (transitions l E) f).obj N)) ≫
          ((A X).levelClosed n).tensor.map
            (Prod.mkHom (reduction l E A X h M)
              (reduction l E A X h
                ((VaryingRing.G (rings l E) (transitions l E) f).obj N)))) := by
  sorry

end Geometry
end AlgebraicGeometry.ProEtale.SystemRefinement
