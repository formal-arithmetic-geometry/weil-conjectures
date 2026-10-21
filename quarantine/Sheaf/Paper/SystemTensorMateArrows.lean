/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.FiniteFieldFiber
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows
import Sheaf.AlgebraicGeometry.VaryingRingTensorSupport
import Sheaf.AlgebraicGeometry.VaryingRingTensorComparison

/-!
# Canonical tensor and proper/open arrows for varying coefficient systems

Source: Stacks Project, Tags 0941, 0F7B, 0E8I and 0B56; the simultaneous
system construction of Zheng, Construction 4.1 and Lemma 4.10
(blueprint: def-pur-system-tensor-mate-arrows).

The site is the published vertical sequence site. Level `n` means exponent `n+1`.
All derived categories are ordinary unbounded localizations of module systems.
The choices below are universal constructions: adjoints to specified sectionwise
functors, or unique section-normalized maps. In particular no transformation is
chosen merely because its source and target are isomorphic.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open WeilConjectures.SemilinearSections

namespace WeilConjectures.SystemTensorMate

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The original pro-etale site is small in the coefficient universe.
Source: the published size convention (blueprint: def-pur-system-tensor-mate-arrows). -/
instance proEtSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The vertical sequence site retains the site's distinct object and morphism sizes.
Source: Stacks 0941 (blueprint: def-pur-system-tensor-mate-arrows). -/
instance sequenceSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} (ℕ × X.ProEt) :=
  essentiallySmallSelf.{0, u, u + 1} _

/-- The actual varying commutative coefficient ring on the vertical sequence site.
Source: Stacks 0941 (blueprint: def-pur-system-tensor-mate-arrows). -/
abbrev R (X : Scheme.{u}) := coefficientSequenceCommRingSheaf l E X

/-- Strict semilinear module systems, with the published quotient transitions.
Source: Zheng 4.1; Stacks 0941 (blueprint: def-pur-system-tensor-mate-arrows). -/
abbrev S (X : Scheme.{u}) :=
  @SemilinearSections.Mod.{u + 1, u, u + 1} _ _ (essentiallySmallSelf.{0, u, u + 1} _)
    (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E X)

/-- The ordinary unbounded derived category of these systems.
Source: Stacks 05RU, 0941 (blueprint: def-pur-system-tensor-mate-arrows). -/
abbrev D (X : Scheme.{u}) :=
  @SemilinearSections.D.{u + 1, u, u + 1} _ _ (essentiallySmallSelf.{0, u, u + 1} _)
    (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E X)

/-- The dependency's canonical abelian structure, at the original site universes.
Source: Stacks 03D1 (blueprint: def-pur-system-tensor-mate-arrows). -/
instance systemAbelian (X : Scheme.{u}) : Abelian (S l E X) :=
  @SemilinearSections.moduleAbelian.{u + 1, u, u + 1} _ _ (essentiallySmallSelf.{0, u, u + 1} _)
    (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E X)

/-- The dependency's standard unbounded localization instance.
Source: Stacks 05RU (blueprint: def-pur-system-tensor-mate-arrows). -/
instance systemDerived (X : Scheme.{u}) : HasDerivedCategory.{u + 2} (S l E X) :=
  HasDerivedCategory.standard _

/-- A constant scalar section at positive exponent `n+1`.
Source: Stacks 0H7J (blueprint: def-pur-system-tensor-mate-arrows). -/
def scalar (X : Scheme.{u}) (n : ℕ) (U : X.ProEt) :
    ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)) →
      (R l E X).obj.obj (op (n, U)) :=
  letI : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
    integralCoefficientRingSheafify.{u, u + 1} X
  (toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of.{u + 1}
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).app (op U)

/-- Base change keeps the coefficient index.
Source: Stacks 0941, 09A5 (blueprint: def-pur-system-tensor-mate-arrows). -/
def base {X Y : Scheme.{u}} (f : X ⟶ Y) : ℕ × Y.ProEt ⥤ ℕ × X.ProEt :=
  (𝟭 ℕ).prod (Scheme.proEtaleBaseChange f)

/-- Base change is continuous for vertical coverings.
Source: Stacks 0941, 09A5 (blueprint: def-pur-system-tensor-mate-arrows).
Proof: restrict a system sheaf to a vertical slice. Pro-etale base change is
continuous there. The horizontal maps retain their index and commute with the
same vertical restrictions, giving the system sheaf condition. -/
theorem base_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (base f).IsContinuous (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) := by
  exact ProEtale.VaryingRing.baseChange_continuous f

attribute [instance] base_continuous

private instance commRingSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u + 1} X

private theorem constantDirect_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {A B : CommRingCat.{u + 1}} (a : A ⟶ B) :
    (constantSheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).map a ≫
        Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} B =
      Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} A ≫
        (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
          ((constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}).map a) := by
  apply ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    ((Functor.const Y.ProEtᵒᵖ).obj A) _).injective
  dsimp only [constantSheaf, Functor.comp_map]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  erw [Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply,
    Scheme.proEtaleConstantDirectImageMap, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext U
  exact congrArg (fun t ↦ t.app ((Scheme.proEtaleBaseChange f).op.obj U))
    (toSheafify_naturality (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).map a))

private theorem ring_vertical_map (W : Scheme.{u}) (n : ℕ)
    {U V : W.ProEtᵒᵖ} (a : U ⟶ V) :
    (R l E W).obj.map ((Prod.sectR n W.ProEt).op.map a) =
      (integralCoefficientCommRingSheaf l E W n).obj.map a := by
  change ((coefficientSequenceCommRingSystem l E W).map (𝟙 (op n))).hom.app U ≫
    (integralCoefficientCommRingSheaf l E W n).obj.map a = _
  erw [CategoryTheory.Functor.map_id]
  rfl

private def coefficient_system {X Y : Scheme.{u}} (f : X ⟶ Y) :
    coefficientSequenceCommRingSystem l E Y ⟶
    coefficientSequenceCommRingSystem l E X ⋙
      Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1} :=
  NatTrans.ofOpSequence
    (fun n ↦ Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
    (fun n ↦ by
      dsimp only [Functor.comp_map, coefficientSequenceCommRingSystem]
      rw [Functor.ofOpSequence_map_homOfLE_succ,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact constantDirect_naturality f _)

private def sequenceMap
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D] (F : C ⥤ D)
    (A : ℕᵒᵖ ⥤ Cᵒᵖ ⥤ CommRingCat.{u + 1})
    (B : ℕᵒᵖ ⥤ Dᵒᵖ ⥤ CommRingCat.{u + 1})
    (d : A ⟶ B ⋙ (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ CommRingCat.{u + 1}).obj F.op) :
    (prodOpEquiv (C := ℕ) (D := C)).functor ⋙ Functor.uncurry.obj A ⟶
      ((𝟭 ℕ).prod F).op ⋙ (prodOpEquiv (C := ℕ) (D := D)).functor ⋙
        Functor.uncurry.obj B where
  app U := (d.app (op U.unop.1)).app (op U.unop.2)
  naturality U V a := by
    have hd := congrArg (fun t ↦ t.app (op U.unop.2)) (d.naturality a.unop.1.op)
    have hv := (d.app (op V.unop.1)).naturality a.unop.2.op
    change ((A.map a.unop.1.op).app (op U.unop.2) ≫
      (A.obj (op V.unop.1)).map a.unop.2.op) ≫
        (d.app (op V.unop.1)).app (op V.unop.2) =
      (d.app (op U.unop.1)).app (op U.unop.2) ≫
        ((B.map a.unop.1.op).app (F.op.obj (op U.unop.2)) ≫
          (B.obj (op V.unop.1)).map (F.op.map a.unop.2.op))
    rw [Category.assoc, hv, ← Category.assoc]
    exact congrArg (fun t ↦ t ≫ _) hd

private def coefficient_candidate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R l E Y ⟶ ((base f).sheafPushforwardContinuous CommRingCat.{u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology Y))
    (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj (R l E X) :=
  ⟨sequenceMap (Scheme.proEtaleBaseChange f)
    (coefficientSequenceCommRingSystem l E Y ⋙
      sheafToPresheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (coefficientSequenceCommRingSystem l E X ⋙
      sheafToPresheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (Functor.whiskerRight (coefficient_system l E f)
      (sheafToPresheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1}))⟩

/-- The ring map on the diagram site is uniquely fixed by constant sections.
Source: Stacks 0H7J, 0941 (blueprint: def-pur-system-tensor-mate-arrows).
Proof: on slice n use proEtaleConstantDirectImageMap for the ring A_(n+1).
Naturality of that map in the coefficient ring proves compatibility with the
quotient transitions, so the maps assemble. Uniqueness follows slice by slice
from the constant-presheaf sheafification universal property. -/
theorem coefficient_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! c : R l E Y ⟶ ((base f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj (R l E X),
      ∀ (n : ℕ) (U : Y.ProEt)
        (a : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))),
        c.hom.app (op (n, U)) (scalar l E Y n U a) =
          scalar l E X n ((Scheme.proEtaleBaseChange f).obj U) a := by
  let d := coefficient_system l E f
  let c := coefficient_candidate l E f
  have hc (n : ℕ) (U : Y.ProEt)
      (a : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) :
      c.hom.app (op (n, U)) (scalar l E Y n U a) =
        scalar l E X n ((Scheme.proEtaleBaseChange f).obj U) a := by
    have h := Equiv.apply_symm_apply
      ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
        ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
          (integralCoefficientCommRingSheaf l E X n)))
      (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
        (toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of
            (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))))
    exact congrArg (fun t ↦ (t.app (op U)).hom a) h
  refine ⟨c, hc, ?_⟩
  intro c' hc'
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  let n := V.unop.1
  let e : integralCoefficientCommRingSheaf l E Y n ⟶
      (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (integralCoefficientCommRingSheaf l E X n) :=
    ⟨{ app := fun U ↦ c'.hom.app (op (n, U.unop))
       naturality := fun U U' a ↦ by
         have h := c'.hom.naturality ((Prod.sectR n Y.ProEt).op.map a)
         change (R l E Y).obj.map ((Prod.sectR n Y.ProEt).op.map a) ≫ _ =
           _ ≫ (R l E X).obj.map
             ((Prod.sectR n X.ProEt).op.map ((Scheme.proEtaleBaseChange f).op.map a)) at h
         erw [ring_vertical_map, ring_vertical_map] at h
         exact h }⟩
  have he : e = d.app (op n) := by
    apply ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) _).injective
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (hc' n U.unop a).trans (hc n U.unop a).symm
  exact congrArg (fun t ↦ t.hom.app (op V.unop.2)) he


/-- The unique constant-section-preserving structural ring map.
Source: Stacks 0H7J, 0941 (blueprint: def-pur-system-tensor-mate-arrows). -/
def coefficient {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (coefficient_existsUnique l E f).choose

/-- Actual sectionwise system direct image with its specified scalar action.
Source: Stacks 03D7, 0941 (blueprint: def-pur-system-tensor-mate-arrows). -/
def direct {X Y : Scheme.{u}} (f : X ⟶ Y) : S l E X ⥤ S l E Y :=
  SheafOfModules.pushforward.{u + 1} (F := base f)
    (S := (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R l E Y))
    (R := (sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R l E X))
    ⟨Functor.whiskerRight (coefficient l E f).hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

/-- Sectionwise direct image is additive.
Source: Stacks 03D7 (blueprint: def-pur-system-tensor-mate-arrows).
Proof: restrictions and scalar restriction leave addition of maps unchanged,
so the equality holds on every section, including the horizontal restrictions. -/
theorem direct_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (direct l E f).Additive := by
  constructor
  intro M N a b
  ext V x
  rfl

open SheafOfModules in
/-- The actual system category has K-injective resolutions.
Source: Stacks 079P; semilinearDerivedSections
(blueprint: def-pur-system-tensor-mate-arrows).
Proof: semilinearDerivedSections makes this module category on the small
vertical ringed site Grothendieck abelian. Apply K-injective existence for a
Grothendieck abelian category, in the recorded standard derived universe. -/
theorem system_kInjective (X : Scheme.{u}) :
    Abelian.HasKInjectiveResolutions (S l E X) := by
  let : IsGrothendieckAbelian.{u + 1} (S l E X) :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E X)).1
  infer_instance

attribute [instance] direct_additive system_kInjective

/-- Total right derived sectionwise direct image of actual systems.
Source: Stacks 07A4 (blueprint: def-pur-system-tensor-mate-arrows). -/
abbrev pushDerived {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (direct l E f).rightDerivedFunctor

section

attribute [local irreducible] coefficientSequenceCommRingSheaf

open CategoryTheory.MonoidalCategory in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def laxTensorPresheaf {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : S l E X) :
    ((direct l E f).obj M).val ⊗ ((direct l E f).obj N).val ⟶
      ((direct l E f).obj (ordinaryTensor.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E X) M N)).val := by
  let JX := coefficientSequenceTopology (Scheme.ProEt.topology X)
  let RX := R l E X
  let RY := R l E Y
  let := SheafOfModules.isMonoidal_W_independentCoefficients RX
  let φ := Functor.whiskerRight (coefficient l E f).hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let F := PresheafOfModules.pushforward.{u + 1} (F := base f)
    (R := RX.obj ⋙ forget₂ CommRingCat RingCat)
    (S := RY.obj ⋙ forget₂ CommRingCat RingCat) φ
  let : F.LaxMonoidal := PresheafOfModules.pushforwardLaxMonoidal
    (F := base f) (R := RX.obj) (S := RY.obj) φ
  let adjX := PresheafOfModules.sheafificationAdjunction
    (𝟙 (ring.{u + 1, u, u + 1} JX RX).obj)
  let eX := SheafOfModules.tensorObjIsoSheafification (R := RX) M N
  exact Functor.LaxMonoidal.μ F M.val N.val ≫ F.map
    (adjX.unit.app (M.val ⊗ N.val) ≫ eX.inv.val)

open CategoryTheory.MonoidalCategory in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem laxTensorPresheaf_tmul {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : S l E X) (V : (ℕ × Y.ProEt)ᵒᵖ)
    (x : ((direct l E f).obj M).val.obj V)
    (y : ((direct l E f).obj N).val.obj V) :
    (laxTensorPresheaf l E f M N).app V
      (x ⊗ₜ[(R l E Y).obj.obj V] y) =
      tensorSection.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E X)
        M N ((base f).op.obj V) x y := by
  let JX := coefficientSequenceTopology (Scheme.ProEt.topology X)
  let RX := R l E X
  let RY := R l E Y
  let := SheafOfModules.isMonoidal_W_independentCoefficients RX
  let φ := Functor.whiskerRight (coefficient l E f).hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let F := PresheafOfModules.pushforward.{u + 1} (F := base f)
    (R := RX.obj ⋙ forget₂ CommRingCat RingCat)
    (S := RY.obj ⋙ forget₂ CommRingCat RingCat) φ
  let : F.LaxMonoidal := PresheafOfModules.pushforwardLaxMonoidal
    (F := base f) (R := RX.obj) (S := RY.obj) φ
  let adjX := PresheafOfModules.sheafificationAdjunction
    (𝟙 (ring.{u + 1, u, u + 1} JX RX).obj)
  let eX := SheafOfModules.tensorObjIsoSheafification (R := RX) M N
  change (F.map (adjX.unit.app (M.val ⊗ N.val) ≫ eX.inv.val)).app V
    ((Functor.LaxMonoidal.μ F M.val N.val).app V (x ⊗ₜ[RY.obj.obj V] y)) = _
  have hm := PresheafOfModules.pushforward_μ_app_tmul
    (F := base f) (R := RX.obj) (S := RY.obj) φ M.val N.val V x y
  exact congrArg (fun z ↦ (F.map
    (adjX.unit.app (M.val ⊗ N.val) ≫ eX.inv.val)).app V z) hm

attribute [local irreducible] laxTensorPresheaf

open CategoryTheory.MonoidalCategory in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The lax tensor map of sectionwise direct image has its usual pure-tensor formula.
Source: Stacks 03EK, 0B56 (blueprint: def-pur-system-tensor-mate-arrows).
Proof: on every object the map sends x tensor y to x tensor y over the pulled
back ring. It is bilinear over the structural ring map, commutes with both
vertical and horizontal restrictions, and therefore sheafifies. Pure tensors
locally generate the sheaf tensor, proving uniqueness. -/
theorem laxTensor_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : S l E X) :
    ∃! t : ordinaryTensor.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y)) (R l E Y)
        ((direct l E f).obj M) ((direct l E f).obj N) ⟶
      (direct l E f).obj
        (ordinaryTensor.{u + 1, u, u + 1}
          (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E X) M N),
      ∀ (V : (ℕ × Y.ProEt)ᵒᵖ)
        (x : ((direct l E f).obj M).val.obj V)
        (y : ((direct l E f).obj N).val.obj V),
        t.val.app V
          (tensorSection.{u + 1, u, u + 1}
            (coefficientSequenceTopology (Scheme.ProEt.topology Y)) (R l E Y)
            ((direct l E f).obj M) ((direct l E f).obj N) V x y) =
          tensorSection.{u + 1, u, u + 1}
            (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E X)
            M N ((base f).op.obj V) x y := by
  let JX := coefficientSequenceTopology (Scheme.ProEt.topology X)
  let JY := coefficientSequenceTopology (Scheme.ProEt.topology Y)
  let RX := R l E X
  let RY := R l E Y
  let := SheafOfModules.isMonoidal_W_independentCoefficients RX
  let := SheafOfModules.isMonoidal_W_independentCoefficients RY
  let adjY := PresheafOfModules.sheafificationAdjunction
    (𝟙 (ring.{u + 1, u, u + 1} JY RY).obj)
  let A := (direct l E f).obj M
  let B := (direct l E f).obj N
  let H := (direct l E f).obj (ordinaryTensor.{u + 1, u, u + 1} JX RX M N)
  let eY := SheafOfModules.tensorObjIsoSheafification (R := RY) A B
  let q := laxTensorPresheaf l E f M N
  let a := (adjY.homEquiv (A.val ⊗ B.val) H).symm q
  let t := eY.hom ≫ a
  have ht (V : (ℕ × Y.ProEt)ᵒᵖ) (x : A.val.obj V) (y : B.val.obj V) :
      t.val.app V (tensorSection.{u + 1, u, u + 1} JY RY A B V x y) =
        tensorSection.{u + 1, u, u + 1} JX RX M N ((base f).op.obj V) x y := by
    have h := (adjY.homEquiv (A.val ⊗ B.val) H).apply_symm_apply q
    rw [Adjunction.homEquiv_unit] at h
    have hh := congrArg (fun k ↦ (k.app V) (x ⊗ₜ[RY.obj.obj V] y)) h
    have hi := congrArg (fun k ↦ k.val.app V
      ((adjY.unit.app (A.val ⊗ B.val)).app V (x ⊗ₜ[RY.obj.obj V] y)))
      eY.inv_hom_id
    change a.val.app V ((adjY.unit.app (A.val ⊗ B.val)).app V
      (x ⊗ₜ[RY.obj.obj V] y)) = q.app V (x ⊗ₜ[RY.obj.obj V] y) at hh
    change eY.hom.val.app V (eY.inv.val.app V _) =
      (adjY.unit.app (A.val ⊗ B.val)).app V (x ⊗ₜ[RY.obj.obj V] y) at hi
    change a.val.app V (eY.hom.val.app V (eY.inv.val.app V _)) = _
    rw [hi, hh]
    exact laxTensorPresheaf_tmul l E f M N V x y
  refine ⟨t, ht, ?_⟩
  intro t' ht'
  apply (cancel_epi eY.inv).1
  apply (adjY.homEquiv (A.val ⊗ B.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  ext z
  change (t'.val.app V).hom ((eY.inv.val.app V).hom
      (((adjY.unit.app (A.val ⊗ B.val)).app V).hom z)) =
    (t.val.app V).hom ((eY.inv.val.app V).hom
      (((adjY.unit.app (A.val ⊗ B.val)).app V).hom z))
  induction z using TensorProduct.induction_on with
  | zero =>
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    simp only [map_zero]
  | tmul x y => exact (ht' V x y).trans (ht V x y).symm
  | add z w hz hw =>
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    simp only [map_add, hz, hw]


end

/-- The normalized lax tensor map, used to fix inverse-image tensor comparison.
Source: Stacks 03EK, 0B56 (blueprint: def-pur-system-tensor-mate-arrows). -/
def laxTensor {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : S l E X) :=
  (laxTensor_existsUnique l E f M N).choose

private theorem coefficient_scalar {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (U : Y.ProEt) (a : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) :
    (coefficient l E f).hom.app (op (n, U)) (scalar l E Y n U a) =
      scalar l E X n ((Scheme.proEtaleBaseChange f).obj U) a :=
  (coefficient_existsUnique l E f).choose_spec.1 n U a

private theorem scalar_map (X : Scheme.{u}) (n : ℕ) {U V : X.ProEt}
    (b : U ⟶ V) (a : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) :
    (R l E X).obj.map ((Prod.sectR n X.ProEt).map b).op (scalar l E X n V a) =
      scalar l E X n U a := by
  erw [ring_vertical_map l E X n b.op]
  have h := (toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).naturality b.op
  exact (congrArg (fun t ↦ t.hom a) h).symm

/-- Sectionwise direct-image composition is the fibre-product pasting map.
Source: Stacks 0D6D (blueprint: def-pur-system-tensor-mate-arrows).
Proof: restrict sections along pullbackComp, keeping the coefficient index.
The constant-section normalization makes this linear. Its inverse is restriction
along the inverse pasting map. Naturality and uniqueness are checked on sections. -/
theorem directComp_existsUnique {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃! e : direct l E f ⋙ direct l E g ≅ direct l E (f ≫ g),
      ∀ (M : S l E X) (n : ℕ) (U : Z.ProEt)
        (x : ((direct l E f ⋙ direct l E g).obj M).val.obj (op (n, U))),
        (e.hom.app M).val.app (op (n, U)) x =
          M.val.map (CategoryTheory.Prod.mkHom (𝟙 n)
            ((MorphismProperty.Over.pullbackComp f g (f ≫ g) rfl).hom.app U)).op x := by
  let e : base (f ≫ g) ≅ base g ⋙ base f :=
    NatIso.ofComponents
      (fun U ↦ Iso.prod (Iso.refl U.1)
        ((MorphismProperty.Over.pullbackComp f g (f ≫ g) rfl).app U.2))
      (by
        intro U V a
        apply CategoryTheory.Prod.hom_ext
        · exact Subsingleton.elim _ _
        · exact (MorphismProperty.Over.pullbackComp f g (f ≫ g) rfl).hom.naturality a.2)
  have : (base g ⋙ base f).IsContinuous
      (coefficientSequenceTopology (Scheme.ProEt.topology Z))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) :=
    Functor.isContinuous_comp _ _ _ (coefficientSequenceTopology (Scheme.ProEt.topology Y)) _
  let c : R l E Z ⟶ ((base g ⋙ base f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology Z))
      (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj (R l E X) :=
    coefficient l E g ≫ ((base g).sheafPushforwardContinuous CommRingCat.{u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology Z))
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))).map (coefficient l E f)
  have hc : c ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom CommRingCat.{u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology Z))
      (coefficientSequenceTopology (Scheme.ProEt.topology X))).app (R l E X) =
        coefficient l E (f ≫ g) := by
    apply (coefficient_existsUnique l E (f ≫ g)).choose_spec.2
    intro n U a
    change (R l E X).obj.map ((Prod.sectR n X.ProEt).map
      ((MorphismProperty.Over.pullbackComp f g (f ≫ g) rfl).hom.app U)).op
        ((coefficient l E f).hom.app (op (n, (Scheme.proEtaleBaseChange g).obj U))
          ((coefficient l E g).hom.app (op (n, U)) (scalar l E Z n U a))) = _
    rw [coefficient_scalar, coefficient_scalar]
    exact scalar_map l E X n _ a
  let φf := (direct l E f)
  let φg := (direct l E g)
  let a : φf ⋙ φg ≅ direct l E (f ≫ g) :=
    SheafOfModules.pushforwardComp _ _ ≪≫ SheafOfModules.pushforwardCongr₂ _ e (by
      apply Sheaf.hom_ext
      exact congrArg (fun t ↦ Functor.whiskerRight t.hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) hc)
  have ha (M : S l E X) (n : ℕ) (U : Z.ProEt)
      (x : ((direct l E f ⋙ direct l E g).obj M).val.obj (op (n, U))) :
      (a.hom.app M).val.app (op (n, U)) x =
        M.val.map (CategoryTheory.Prod.mkHom (𝟙 n)
          ((MorphismProperty.Over.pullbackComp f g (f ≫ g) rfl).hom.app U)).op x := by
    rfl
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  ext V x
  exact (ha' M V.unop.1 V.unop.2 x).trans (ha M V.unop.1 V.unop.2 x).symm


/-- The unique section-normalized direct-image compositor.
Source: Stacks 0D6D (blueprint: def-pur-system-tensor-mate-arrows). -/
def directComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  (directComp_existsUnique l E f g).choose

/-- Universal geometric operations on the actual varying-ring system categories.
Tensor comparisons retain both their ordinary unit formula and their complete
K-flat total-summand normalization. Open extension is the exact left adjoint to
inverse image; its canonical identification with sectionwise extension is the
unique adjunction-compatible identification.
Source: Zheng 4.1, 4.10; Stacks 03DI, 07A4, 0E8I
(blueprint: def-pur-system-tensor-mate-arrows). -/
structure Operations where
  systems : ∀ X : Scheme.{u}, @Data.{u + 1, u, u + 1} _ _
    (Scheme.ProEt.topology X) (essentiallySmallSelf.{0, u, u + 1} _)
    (integralCoefficientCommRingSheaf.{u, u + 1} l E X)
    (coefficientSequenceCommRingTransition.{u, u + 1} l E X)
  pull : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → S l E Y ⥤ S l E X
  adj : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), pull f ⊣ direct l E f
  [pullAdditive : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (pull f).Additive]
  [pullLimits : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteLimits (pull f)]
  [pullColimits : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteColimits (pull f)]
  extension : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j], S l E U ⥤ S l E X
  openAdj : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j], extension j ⊣ pull j
  [extensionAdditive : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
    (extension j).Additive]
  [extensionLimits : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
    PreservesFiniteLimits (extension j)]
  [extensionColimits : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
    PreservesFiniteColimits (extension j)]

attribute [instance] Operations.pullAdditive Operations.pullLimits Operations.pullColimits
  Operations.extensionAdditive
  Operations.extensionLimits Operations.extensionColimits

namespace Operations
variable {l E}
variable (o : Operations l E)

/-- Inverse-image composition is the conjugate of sectionwise direct-image pasting.
Source: Stacks 0D6D, 07A7 (blueprint: def-pur-system-tensor-mate-arrows). -/
def pullComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    o.pull g ⋙ o.pull f ≅ o.pull (f ≫ g) :=
  Adjunction.leftAdjointCompIso (o.adj g) (o.adj f) (o.adj (f ≫ g))
    (directComp l E f g)

/-- Exact system pullback on the ordinary derived category.
Source: Stacks 07A4 (blueprint: def-pur-system-tensor-mate-arrows). -/
abbrev P {X Y : Scheme.{u}} (f : X ⟶ Y) := (o.pull f).mapDerivedCategory

/-- The canonical derived adjunction of the actual ordinary adjunction.
Source: Stacks 07A4 (blueprint: def-pur-system-tensor-mate-arrows). -/
def derivedAdj {X Y : Scheme.{u}} (f : X ⟶ Y) : o.P f ⊣ pushDerived l E f :=
  (o.adj f).mapDerivedCategoryRightDerivedAdjunction

/-- Exact open extension on complexes and their ordinary localization.
Source: Stacks 03DI, 07A4 (blueprint: def-pur-system-tensor-mate-arrows). -/
abbrev J {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (o.extension j).mapDerivedCategory

/-- The exact derived open adjunction, with the ordinary unit normalization.
Source: Stacks 03DI, 07A4 (blueprint: def-pur-system-tensor-mate-arrows). -/
def derivedOpenAdj {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] : o.J j ⊣ o.P j :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction (o.openAdj j)

/-- Tensor is the dependency's K-flat modeled closed tensor on systems.
Source: Stacks 06YS, 08J9 (blueprint: def-pur-system-tensor-mate-arrows). -/
abbrev T (X : Scheme.{u}) := (o.systems X).closed.tensor

/-- The derived pullback compositor is localized from the actual ordinary one.
Source: Stacks 07A4 (blueprint: def-pur-system-tensor-mate-arrows). -/
def pComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    o.P g ⋙ o.P f ≅ o.P (f ≫ g) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (o.pullComp f g)

/-- The pullback-square comparison, oriented from the top/right to bottom/left route.
Source: Stacks 07A7 (blueprint: def-pur-system-tensor-mate-arrows). -/
def square {A B C F : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ F) (i : C ⟶ F) (h : k ≫ p = r ≫ i) :
    o.P p ⋙ o.P k ≅ o.P i ⋙ o.P r :=
  o.pComp k p ≪≫ eqToIso (congrArg (fun f ↦ o.P f) h) ≪≫ (o.pComp r i).symm

end Operations

/-- Canonical system tensor comparisons, fixed on ordinary units and K-flat total
summands. This extends universal operations, rather than postulating arbitrary
isomorphisms between tensor expressions.
Source: Stacks 07A4, 0B56 (blueprint: def-pur-system-tensor-mate-arrows). -/
structure TensorOperations extends Operations l E where
  mu : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    toOperations.T Y ⋙ toOperations.P f ≅
      ((toOperations.P f).prod (toOperations.P f)) ⋙ toOperations.T X
  model : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    TensorComparisonModel.{u + 1, u, u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E Y) (R l E X)
      (pull f) (systems Y).closed (systems X).closed
      (systems Y).tensorModels (systems X).tensorModels (mu f)
  ordinary_unit : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : S l E Y),
    (adj f).homEquiv _ _ ((model f).ordinary M N).hom =
      ordinaryTensorHom.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y)) (R l E Y)
        ((adj f).unit.app M) ((adj f).unit.app N) ≫
          laxTensor l E f ((pull f).obj M) ((pull f).obj N)

private abbrev constantRings (n : ℕ) := CommRingCat.of
  (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
private def quotientMaps (n : ℕ) : constantRings l E (n + 1) ⟶ constantRings l E n :=
  CommRingCat.ofHom
    ((ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).symm.toRingHom.comp
      ((Padic.coefficientExtensionTransition l E (n + 1)).comp
        (ULift.ringEquiv : ULift.{u + 1} _ ≃+* _).toRingHom))
private theorem map_bijective_of_unit_iso
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (X Y : C) [IsIso (adj.unit.app Y)] :
    Function.Bijective (fun f : X ⟶ Y ↦ L.map f) := by
  let e : (X ⟶ Y) ≃ (L.obj X ⟶ L.obj Y) :=
    (Iso.homCongr (Iso.refl X) (asIso (adj.unit.app Y))).trans
      (adj.homEquiv X (L.obj Y)).symm
  have he (f : X ⟶ Y) : e f = L.map f := by
    apply (adj.homEquiv X (L.obj Y)).injective
    dsimp only [e, Equiv.trans_apply]
    erw [Equiv.apply_symm_apply]
    rw [Adjunction.homEquiv_unit]
    change (𝟙 X) ≫ f ≫ adj.unit.app Y = _
    rw [Category.id_comp]
    exact adj.unit.naturality f
  simpa only [show (fun f : X ⟶ Y ↦ e f) = (fun f ↦ L.map f) from funext he]
    using e.bijective

private theorem map_bijective_of_counit_iso
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (X Y : D) [IsIso (adj.counit.app X)] :
    Function.Bijective (fun f : X ⟶ Y ↦ R.map f) := by
  let e : (X ⟶ Y) ≃ (R.obj X ⟶ R.obj Y) :=
    (Iso.homCongr (asIso (adj.counit.app X)).symm (Iso.refl Y)).trans
      (adj.homEquiv (R.obj X) Y)
  have he (f : X ⟶ Y) : e f = R.map f := by
    apply (adj.homEquiv (R.obj X) Y).symm.injective
    dsimp only [e, Equiv.trans_apply]
    erw [Equiv.symm_apply_apply]
    rw [Adjunction.homEquiv_counit]
    change adj.counit.app X ≫ f ≫ (𝟙 Y) = _
    rw [Category.comp_id]
    exact (adj.counit.naturality f).symm
  simpa only [show (fun f : X ⟶ Y ↦ e f) = (fun f ↦ R.map f) from funext he]
    using e.bijective

private theorem map_bijective_of_iso
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F ≅ G)
    (X Y : C) (hF : Function.Bijective (fun f : X ⟶ Y ↦ F.map f)) :
    Function.Bijective (fun f : X ⟶ Y ↦ G.map f) := by
  have hb := (Iso.homCongr (e.app X) (e.app Y)).bijective.comp hF
  convert hb using 1
  funext f
  change G.map f = e.inv.app X ≫ F.map f ≫ e.hom.app Y
  rw [← Category.assoc, ← e.inv.naturality f]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

private theorem map_bijective_of_obj_iso
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y X' Y' : C} (a : X ≅ X') (b : Y ≅ Y')
    (h : Function.Bijective (fun f : X ⟶ Y ↦ F.map f)) :
    Function.Bijective (fun f : X' ⟶ Y' ↦ F.map f) := by
  have hb := (Iso.homCongr (F.mapIso a) (F.mapIso b)).bijective.comp h
  have he : (Iso.homCongr (F.mapIso a) (F.mapIso b)) ∘
      (fun f : X ⟶ Y ↦ F.map f) =
      (fun f : X' ⟶ Y' ↦ F.map f) ∘ (Iso.homCongr a b) := by
    funext f
    simp only [Function.comp_apply, Iso.homCongr_apply, Functor.map_comp,
      Functor.mapIso_inv, Functor.mapIso_hom]
  rw [he] at hb
  exact (Function.Bijective.of_comp_iff _ (Iso.homCongr a b).bijective).1 hb

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem canonical_bijective
    (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
    {A B C F : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C) (p : B ⟶ F) (i : C ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i)
    (N : ProEtale.VaryingRing.Modules R φ C) (M : ProEtale.VaryingRing.Modules R φ A) :
    Function.Bijective (fun a : (ProEtale.VaryingRing.pull R φ p).obj
      ((ProEtale.VaryingRing.extension R φ i).obj N) ⟶
        (ProEtale.VaryingRing.extension R φ k).obj M ↦
          (ProEtale.VaryingRing.pull R φ k).map a) := by
  let s := ProEtale.StrictTower.squareLift k r p i h
  let v := pullback.fst p i
  let t := pullback.snd p i
  have hs : IsOpenImmersion s := inferInstance
  have hsc : IsClosedImmersion s := inferInstance
  have hv : IsOpenImmersion v := inferInstance
  let eX := (ProEtale.VaryingRing.moduleBeta R φ t v i p pullback.condition.symm
    (IsPullback.of_hasPullback p i).flip).app N
  let eY : (ProEtale.VaryingRing.extension R φ k).obj M ≅
      (ProEtale.VaryingRing.extension R φ v).obj ((ProEtale.VaryingRing.extension R φ s).obj M) :=
    (ProEtale.VaryingRing.moduleJCongr R φ (pullback.lift_fst k r h)).symm.app M ≪≫
      (ProEtale.VaryingRing.moduleJComp R φ s v).symm.app M
  apply map_bijective_of_obj_iso (ProEtale.VaryingRing.pull R φ k) eX.symm eY.symm
  let X := (ProEtale.VaryingRing.extension R φ v).obj ((ProEtale.VaryingRing.pull R φ t).obj N)
  let Y := (ProEtale.VaryingRing.extension R φ v).obj ((ProEtale.VaryingRing.extension R φ s).obj M)
  let ev := ProEtale.VaryingRing.moduleJAdj R φ v
  have := ProEtale.VaryingRing.moduleJAdj_unit_isIso R φ v
  let ff := ev.fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : IsIso (ev.counit.app X) := ev.isIso_counit_app_of_iso (Iso.refl _)
  have hb := map_bijective_of_counit_iso ev X Y
  have := ProEtale.VaryingRing.moduleOpenToP_isIso R φ s
  have := ProEtale.VaryingRing.moduleJAdj_unit_isIso R φ s
  let fs := ((ProEtale.VaryingRing.moduleJAdj R φ s).fullyFaithfulLOfIsIsoUnit).ofIso
    (asIso (ProEtale.VaryingRing.moduleOpenToP R φ s))
  have := fs.full
  have := fs.faithful
  let e : (ProEtale.VaryingRing.pull R φ v).obj Y ≅ (ProEtale.VaryingRing.push R φ s).obj M :=
    ((asIso ev.unit).app ((ProEtale.VaryingRing.extension R φ s).obj M)).symm ≪≫
      (asIso (ProEtale.VaryingRing.moduleOpenToP R φ s)).app M
  have : IsIso ((ProEtale.VaryingRing.moduleAdj R φ s).unit.app
      ((ProEtale.VaryingRing.pull R φ v).obj Y)) :=
    (ProEtale.VaryingRing.moduleAdj R φ s).isIso_unit_app_of_iso e
  have hc := map_bijective_of_unit_iso (ProEtale.VaryingRing.moduleAdj R φ s)
    ((ProEtale.VaryingRing.pull R φ v).obj X) ((ProEtale.VaryingRing.pull R φ v).obj Y)
  let eF : ProEtale.VaryingRing.pull R φ k ≅
      ProEtale.VaryingRing.pull R φ v ⋙ ProEtale.VaryingRing.pull R φ s :=
    eqToIso (congrArg (ProEtale.VaryingRing.pull R φ) (pullback.lift_fst k r h).symm) ≪≫
      ProEtale.VaryingRing.moduleGComp R φ s v
  exact map_bijective_of_iso eF.symm X Y (hc.comp hb)

private theorem coefficient_eq_candidate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    coefficient l E f = coefficient_candidate l E f := by
  symm
  apply (coefficient_existsUnique l E f).choose_spec.2
  intro n U a
  have h := Equiv.apply_symm_apply
    ((sheafificationAdjunction (Scheme.ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
      ((Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (integralCoefficientCommRingSheaf l E X n)))
    (Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of
          (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))))
  exact congrArg (fun t ↦ (t.app (op U)).hom a) h

private theorem direct_eq_varying {X Y : Scheme.{u}} (f : X ⟶ Y) :
    direct l E f = ProEtale.VaryingRing.push (constantRings l E) (quotientMaps l E) f := by
  unfold direct ProEtale.VaryingRing.push
  rw [coefficient_eq_candidate]
  rfl

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor

private def ordinaryOperations : Operations l E := {
  systems := fun X ↦ (semilinearDerivedSections.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (integralCoefficientCommRingSheaf l E X)
    (coefficientSequenceCommRingTransition l E X)).some.systems
  pull := fun f ↦ ProEtale.VaryingRing.pull (constantRings l E) (quotientMaps l E) f
  adj := fun f ↦
    (ProEtale.VaryingRing.moduleAdj (constantRings l E) (quotientMaps l E) f).ofNatIsoRight
      (eqToIso (direct_eq_varying l E f)).symm
  extension := fun j ↦
    ProEtale.VaryingRing.extension (constantRings l E) (quotientMaps l E) j
  openAdj := fun j ↦
    ProEtale.VaryingRing.moduleJAdj (constantRings l E) (quotientMaps l E) j
  pullAdditive := fun f ↦
    ProEtale.VaryingRing.pullAdditive (constantRings l E) (quotientMaps l E) f
  pullLimits := fun f ↦
    ProEtale.VaryingRing.pullLimits (constantRings l E) (quotientMaps l E) f
  pullColimits := fun f ↦
    ProEtale.VaryingRing.pullColimits (constantRings l E) (quotientMaps l E) f
  extensionAdditive := fun j ↦
    ProEtale.VaryingRing.extensionAdditive (constantRings l E) (quotientMaps l E) j
  extensionLimits := fun j ↦
    ProEtale.VaryingRing.extensionLimits (constantRings l E) (quotientMaps l E) j
  extensionColimits := fun j ↦
    ProEtale.VaryingRing.extensionColimits (constantRings l E) (quotientMaps l E) j }

attribute [local irreducible] ordinaryOperations

/-- Universal presentations of the canonical system operations exist.
Source: Zheng 4.1, 4.10; Stacks 03DI, 07A4, 0E8I, 0941
(blueprint: def-pur-system-tensor-mate-arrows).
Proof: use semilinearDerivedSections for each actual quotient sequence. On the
vertical site form the module inverse image left adjoint to direct. The constant
section map identifies its coefficient ring with the given quotient sequence,
so this inverse image is exact. Open localization has the direct-sum and
sheafification extension, which is exact and left adjoint to this inverse image.
Their universal properties give the ordinary adjunctions. Derive on the ordinary
system category, using its Grothendieck abelianness and K-injectives. The ordinary
tensor inverse-image comparison is the transpose of laxTensor after the two
units. It is invertible for inverse image of constant coefficients. Its inverse
on every total summand gives the chain comparison; localize on flat-term K-flat
systems to get mu and its TensorComparisonModel, precisely as in the geometric
part of semilinearDerivedSections. No equalities are inferred from evaluation. -/
theorem tensorOperations_nonempty : Nonempty (TensorOperations l E) := by
  let o := ordinaryOperations l E
  let : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), (o.pull f).Additive := o.pullAdditive
  let : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteLimits (o.pull f) :=
    o.pullLimits
  let : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), PreservesFiniteColimits (o.pull f) :=
    o.pullColimits
  have h (X Y : Scheme.{u}) (f : X ⟶ Y) :
      ∃ mu : o.T Y ⋙ o.P f ≅ (o.P f).prod (o.P f) ⋙ o.T X,
        ∃ model : TensorComparisonModel.{u + 1, u, u + 1}
          (coefficientSequenceTopology (Scheme.ProEt.topology Y))
          (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E Y) (R l E X)
          (o.pull f) (o.systems Y).closed (o.systems X).closed
          (o.systems Y).tensorModels (o.systems X).tensorModels mu,
          ∀ M N : S l E Y,
            (o.adj f).homEquiv _ _ (model.ordinary M N).hom =
              ordinaryTensorHom.{u + 1, u, u + 1}
                (coefficientSequenceTopology (Scheme.ProEt.topology Y)) (R l E Y)
                ((o.adj f).unit.app M) ((o.adj f).unit.app N) ≫
                laxTensor l E f ((o.pull f).obj M) ((o.pull f).obj N) := by
    apply ProEtale.VaryingRing.tensorComparison_exists
      (constantRings l E) (quotientMaps l E) f (direct l E f) (direct_eq_varying l E f)
      (o.pull f) (o.adj f) (o.systems Y).closed (o.systems X).closed
      (o.systems Y).tensorModels (o.systems X).tensorModels (laxTensor l E f)
    intro M N V x y
    change (laxTensor l E f M N).val.app V
      (tensorSection.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y)) (R l E Y)
        ((direct l E f).obj M) ((direct l E f).obj N) V x y) =
      tensorSection.{u + 1, u, u + 1}
        (coefficientSequenceTopology (Scheme.ProEt.topology X)) (R l E X)
        M N ((base f).op.obj V) x y
    exact (laxTensor_existsUnique l E f M N).choose_spec.1 V x y
  choose mu model hm using h
  exact ⟨{ toOperations := o
           mu := fun {_ _} f ↦ mu _ _ f
           model := fun {_ _} f ↦ model _ _ f
           ordinary_unit := fun {_ _} f ↦ hm _ _ f }⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Restriction is a bijection on maps from a module pulled back from the larger
open and into a module extended from the proper clopen component.

Source: Stacks Project, Tags 0F7B and 09AE; the clopen-lift step of
`lem-cbc-strict-tower-proper-open-calculus`.
(blueprint: def-pur-system-tensor-mate-arrows).

Proof: put `V = B ×[F] C`, with its open map `v : V → B`. The lift
`s = (k,r) : A → V` is open because `k` is open, and closed because `r` is
proper. It is therefore a clopen immersion. On the actual vertical module
site, base change for open extension identifies `Pp (Ei N)` with extension
from `V`. The unit-normalized adjunctions identify `Ek M` with extension
along `v` of extension along `s`. Extension along `v` is fully faithful.
For the clopen immersion `s`, extension by zero is also direct image:
decompose `V` into `s(A)` and its complementary open, use `M` on the first
component and zero on the second. Thus a map into this extension is exactly
a map on `A`, and its inverse is extension of the map by zero on the
complement. These two maps are inverse on sections of the two disjoint opens.
Their sheaf and coefficient-transition naturality is inherited from restriction
and zero. The quotient rings are pulled back constant sheaves, so the specified
direct images have exactly these restriction adjoints. Uniqueness of adjoints
transports the bijection to the supplied `Pk`, `Pp`, `Pi`, `Ek` and `Ei`;
the transported map on Hom is precisely `Pk.map`. No derived object, tensor
comparison, natural transformation in `N`, or choice of compositor is used. -/
private theorem properOpen_restriction_bijective
    {A B C F : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ F) (i : C ⟶ F) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i)
    (Pk : S l E B ⥤ S l E A) (ak : Pk ⊣ direct l E k)
    (Pp : S l E F ⥤ S l E B) (ap : Pp ⊣ direct l E p)
    (Pi : S l E F ⥤ S l E C) (ai : Pi ⊣ direct l E i)
    (Ek : S l E A ⥤ S l E B) (ek : Ek ⊣ Pk)
    (Ei : S l E C ⥤ S l E F) (ei : Ei ⊣ Pi)
    (N : S l E C) (M : S l E A) :
    Function.Bijective
      (fun a : Pp.obj (Ei.obj N) ⟶ Ek.obj M ↦ Pk.map a) := by
  let ck := (ProEtale.VaryingRing.moduleAdj (constantRings l E) (quotientMaps l E) k).ofNatIsoRight
    (eqToIso (direct_eq_varying l E k)).symm
  let cp := (ProEtale.VaryingRing.moduleAdj (constantRings l E) (quotientMaps l E) p).ofNatIsoRight
    (eqToIso (direct_eq_varying l E p)).symm
  let ci := (ProEtale.VaryingRing.moduleAdj (constantRings l E) (quotientMaps l E) i).ofNatIsoRight
    (eqToIso (direct_eq_varying l E i)).symm
  let eK := ak.leftAdjointUniq ck
  let eP := ap.leftAdjointUniq cp
  let eI := ai.leftAdjointUniq ci
  let eEk := (ek.ofNatIsoRight eK).leftAdjointUniq
    (ProEtale.VaryingRing.moduleJAdj (constantRings l E) (quotientMaps l E) k)
  let eEi := (ei.ofNatIsoRight eI).leftAdjointUniq
    (ProEtale.VaryingRing.moduleJAdj (constantRings l E) (quotientMaps l E) i)
  let a := eP.app (Ei.obj N) ≪≫
    (ProEtale.VaryingRing.pull (constantRings l E) (quotientMaps l E) p).mapIso (eEi.app N)
  let b := eEk.app M
  have hb := canonical_bijective (constantRings l E) (quotientMaps l E) k r p i h N M
  have hc := map_bijective_of_obj_iso
    (ProEtale.VaryingRing.pull (constantRings l E) (quotientMaps l E) k) a.symm b.symm hb
  exact map_bijective_of_iso eK.symm _ _ hc

namespace Operations
variable {l E}
variable (o : Operations l E)

/-- The ordinary pullback square induced by the section-normalized compositors.
Source: Stacks 07A7 (blueprint: def-pur-system-tensor-mate-arrows). -/
def ordinarySquare {A B C F : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ F) (i : C ⟶ F) (h : k ≫ p = r ≫ i) :
    o.pull p ⋙ o.pull k ≅ o.pull i ⋙ o.pull r :=
  o.pullComp k p ≪≫ eqToIso (congrArg (fun f ↦ o.pull f) h) ≪≫
    (o.pullComp r i).symm

/-- The open unit is an isomorphism already on strict module systems.
Source: Stacks 03DI, 0941 (blueprint: def-pur-system-tensor-mate-arrows).
Proof: compare the universal left adjoints with extension on the localized
vertical site. Over an object in the open the extension presheaf has exactly
its original summand; sheafification retains it. Thus the unit is invertible.
Transport by the unique adjunction-compatible comparison to the supplied
universal presentation. -/
theorem ordinaryOpenUnit_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (o.openAdj j).unit := by
  let c := (ProEtale.VaryingRing.moduleAdj (constantRings l E) (quotientMaps l E) j).ofNatIsoRight
    (eqToIso (direct_eq_varying l E j)).symm
  let ep := (o.adj j).leftAdjointUniq c
  let ee := ((o.openAdj j).ofNatIsoRight ep).leftAdjointUniq
    (ProEtale.VaryingRing.moduleJAdj (constantRings l E) (quotientMaps l E) j)
  have := ProEtale.VaryingRing.moduleJAdj_unit_isIso
    (constantRings l E) (quotientMaps l E) j
  let e : o.extension j ⋙ o.pull j ≅ 𝟭 (S l E U) :=
    Functor.isoWhiskerRight ee (o.pull j) ≪≫
      Functor.isoWhiskerLeft
        (ProEtale.VaryingRing.extension (constantRings l E) (quotientMaps l E) j) ep ≪≫
      (asIso (ProEtale.VaryingRing.moduleJAdj
        (constantRings l E) (quotientMaps l E) j).unit).symm
  exact (o.openAdj j).isIso_unit_of_iso e

private theorem derivedOpenUnit_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (o.derivedOpenAdj j).unit := by
  have := o.ordinaryOpenUnit_isIso j
  let e : o.J j ⋙ o.P j ≅ 𝟭 (D l E U) :=
    (Functor.mapDerivedCategoryCompIso (o.extension j) (o.pull j)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso (o.openAdj j).unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso _
  exact (o.derivedOpenAdj j).isIso_unit_of_iso e

private theorem tensor_openSupported {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (M : D l E U) (N : D l E X) :
    (o.J j).essImage ((o.T X).obj ((o.J j).obj M, N)) := by
  let c := (ProEtale.VaryingRing.moduleAdj (constantRings l E) (quotientMaps l E) j).ofNatIsoRight
     (eqToIso (direct_eq_varying l E j)).symm
  let ep := (o.adj j).leftAdjointUniq c
  let ee := ((o.openAdj j).ofNatIsoRight ep).leftAdjointUniq
    (ProEtale.VaryingRing.moduleJAdj (constantRings l E) (quotientMaps l E) j)
  have := ProEtale.VaryingRing.extensionAdditive (constantRings l E) (quotientMaps l E) j
  have := ProEtale.VaryingRing.extensionLimits (constantRings l E) (quotientMaps l E) j
  have := ProEtale.VaryingRing.extensionColimits (constantRings l E) (quotientMaps l E) j
  let e := Functor.mapDerivedCategoryNatIso ee
  have hs := ProEtale.VaryingRing.tensor_openSupported
    (constantRings l E) (quotientMaps l E) j (o.systems X).closed
      (o.systems X).tensorModels M N
  have ht := Functor.essImage.ofIso
    ((o.T X).mapIso (Iso.prod (e.app M).symm (Iso.refl N))) hs
  exact Functor.essImage.ofNatIso e.symm ht

/-- The inverse open unit is fixed by its two inverse identities.
Source: Stacks 03DI (blueprint: def-pur-system-tensor-mate-arrows). -/
def ordinaryOpenUnitInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  @inv _ _ _ _ (o.openAdj j).unit (o.ordinaryOpenUnit_isIso j)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The intrinsic ordinary proper/open map is uniquely determined by its open
restriction. This characterization specifies exactly the clopen projection
composite, including the noncartesian and refinement cases.
Source: Stacks 0F7B, 09AE (blueprint: def-pur-system-tensor-mate-arrows).
Proof: form B_C and s=(k,r). Use squareLift_clopen from the recorded strict-tower
calculus, whose geometric conclusion is independent of coefficients. On module
systems, open base change is the transpose of the open unit. Follow it with the
projection which is identity on s(A) and zero on its complementary open, then
with open and inverse-image composition. This gives alpha and its displayed
restriction equation. A morphism of module sheaves with target extended by zero
is determined by its restriction to that open: on the complement its target is
zero, and the two opens cover. Hence the equation determines every component of
alpha uniquely. All constructions take place on the vertical site, so commute
with the quotient transitions before passing to derived categories. -/
theorem alpha_existsUnique {A B C F : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ F) (i : C ⟶ F) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    ∃! a : o.extension i ⋙ o.pull p ⟶ o.pull r ⋙ o.extension k,
      ∀ N : S l E C,
        (o.pull k).map (a.app N) =
          (o.ordinarySquare k r p i h).hom.app ((o.extension i).obj N) ≫
            (o.pull r).map ((o.ordinaryOpenUnitInv i).app N) ≫
              (o.openAdj k).unit.app ((o.pull r).obj N) := by
  let q : o.extension i ⋙ o.pull p ⋙ o.pull k ⟶
      o.pull r ⋙ o.extension k ⋙ o.pull k :=
    Functor.whiskerLeft (o.extension i) (o.ordinarySquare k r p i h).hom ≫
      (Functor.associator (o.extension i) (o.pull i) (o.pull r)).inv ≫
      Functor.whiskerRight (o.ordinaryOpenUnitInv i) (o.pull r) ≫
      (Functor.leftUnitor (o.pull r)).hom ≫
      Functor.whiskerLeft (o.pull r) (o.openAdj k).unit
  have hb (N : S l E C) (M : S l E A) :=
    properOpen_restriction_bijective l E k r p i h
      (o.pull k) (o.adj k) (o.pull p) (o.adj p) (o.pull i) (o.adj i)
      (o.extension k) (o.openAdj k) (o.extension i) (o.openAdj i) N M
  let a (N : S l E C) : (o.pull p).obj ((o.extension i).obj N) ⟶
      (o.extension k).obj ((o.pull r).obj N) :=
    ((hb N ((o.pull r).obj N)).2 (q.app N)).choose
  have ha (N : S l E C) : (o.pull k).map (a N) = q.app N :=
    ((hb N ((o.pull r).obj N)).2 (q.app N)).choose_spec
  let t : o.extension i ⋙ o.pull p ⟶ o.pull r ⋙ o.extension k :=
    { app := a
      naturality := fun N N' f ↦ by
        apply (hb N ((o.pull r).obj N')).1
        change (o.pull k).map (_ ≫ _) = (o.pull k).map (_ ≫ _)
        rw [Functor.map_comp, Functor.map_comp, ha N, ha N']
        exact q.naturality f }
  have ht (N : S l E C) :
      (o.pull k).map (t.app N) =
        (o.ordinarySquare k r p i h).hom.app ((o.extension i).obj N) ≫
          (o.pull r).map ((o.ordinaryOpenUnitInv i).app N) ≫
            (o.openAdj k).unit.app ((o.pull r).obj N) := by
    simpa only [q, t, Functor.map_id, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.associator_inv_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
      Category.id_comp, Category.comp_id, Category.assoc, Functor.comp_obj,
      Functor.id_obj, Functor.id_map] using ha N
  refine ⟨t, ht, ?_⟩
  intro t' ht'
  apply NatTrans.ext
  funext N
  apply (hb N ((o.pull r).obj N)).1
  exact (ht' N).trans (ht N).symm

/-- The actual ordinary clopen-projection transformation, chosen by a unique
section-level characterization, not from existence of an arbitrary arrow.
Source: Stacks 0F7B, 09AE (blueprint: def-pur-system-tensor-mate-arrows). -/
def ordinaryAlpha {A B C F : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ F) (i : C ⟶ F) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :=
  (o.alpha_existsUnique k r p i h).choose

/-- Localize the actual clopen-projection composite termwise on complexes.
Source: Stacks 0F7B, 07A4 (blueprint: def-pur-system-tensor-mate-arrows). -/
def alpha {A B C F : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ F) (i : C ⟶ F) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : o.J i ⋙ o.P p ⟶ o.P r ⋙ o.J k :=
  (Functor.mapDerivedCategoryCompIso _ _).inv ≫
    Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso (S l E C) (.up ℤ))
      (((o.extension i ⋙ o.pull p).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q)
      (((o.pull r ⋙ o.extension k).mapHomologicalComplex (.up ℤ)) ⋙ DerivedCategory.Q)
      (o.extension i ⋙ o.pull p).mapDerivedCategory
      (o.pull r ⋙ o.extension k).mapDerivedCategory
      (Functor.whiskerRight
        (NatTrans.mapHomologicalComplex (o.ordinaryAlpha k r p i h) (.up ℤ))
        DerivedCategory.Q) ≫
      (Functor.mapDerivedCategoryCompIso _ _).hom

/-- The proper-adjunction mate of the clopen-projection composite. Equivalently
this is eta_p followed by R_p(alpha R_r), then R_p(k_! epsilon_r).
Source: Stacks 0F7B, 07A7 (blueprint: def-pur-system-tensor-mate-arrows). -/
def gamma {A B C F : Scheme.{u}} (k : A ⟶ B) (r : A ⟶ C)
    (p : B ⟶ F) (i : C ⟶ F) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : pushDerived l E r ⋙ o.J i ⟶ o.J k ⋙ pushDerived l E p :=
  mateEquiv (o.derivedAdj r) (o.derivedAdj p) (o.alpha k r p i h)

end Operations

namespace TensorOperations
variable {l E}
variable (o : TensorOperations l E)

/-- The counit-defined projection morphism on arbitrary unbounded systems.
Source: Stacks 0B56 (blueprint: def-pur-system-tensor-mate-arrows). -/
def projection {X Y : Scheme.{u}} (f : X ⟶ Y) (M : D l E X) (N : D l E Y) :
    (o.T Y).obj ((pushDerived l E f).obj M, N) ⟶
      (pushDerived l E f).obj ((o.T X).obj (M, (o.P f).obj N)) :=
  (o.derivedAdj f).homEquiv _ _
    ((o.mu f).hom.app ((pushDerived l E f).obj M, N) ≫
      (o.T X).map (Prod.mkHom ((o.derivedAdj f).counit.app M) (𝟙 _)))

/-- The inverse open tensor comparison is the open-unit transpose under the
canonical restriction/tensor identification.
Source: Stacks 0E8I (blueprint: def-pur-system-tensor-mate-arrows). -/
def deltaInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : D l E U) (N : D l E X) :
    (o.J j).obj ((o.T U).obj (M, (o.P j).obj N)) ⟶
      (o.T X).obj ((o.J j).obj M, N) :=
  ((o.derivedOpenAdj j).homEquiv _ _).symm
    ((o.T U).map (Prod.mkHom ((o.derivedOpenAdj j).unit.app M) (𝟙 _)) ≫
      (o.mu j).inv.app ((o.J j).obj M, N))

/-- The specified open tensor map is invertible for arbitrary unbounded inputs.
Source: Stacks 0E8I; lem-sf-open-tensor-normalization
(blueprint: def-pur-system-tensor-mate-arrows).
Proof: compare universal operations with localized module extension/restriction.
The ordinary tensor comparison is fixed by its unit formula, so is the ordinary
sectionwise comparison. Its total K-flat normalization is model. Thus the map
is the gamma-inverse of openTensorNormalization on the ringed diagram topos,
under the unique compatible comparisons of universal presentations. That theorem
applies with arbitrary coefficient transitions and arbitrary unbounded inputs. -/
theorem deltaInv_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : D l E U) (N : D l E X) : IsIso (o.deltaInv j M N) := by
  have := o.toOperations.derivedOpenUnit_isIso j
  let ff := (o.derivedOpenAdj j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have hs := o.toOperations.tensor_openSupported j M N
  have hc : IsIso ((o.derivedOpenAdj j).counit.app
      ((o.T X).obj ((o.J j).obj M, N))) :=
    (o.derivedOpenAdj j).isIso_counit_app_of_iso hs.getIso.symm
  have hu : IsIso ((o.derivedOpenAdj j).unit.app M) := by infer_instance
  have hp : IsIso (Prod.mkHom ((o.derivedOpenAdj j).unit.app M)
      (𝟙 ((o.P j).obj N))) := (isIso_prod_iff _ _).2 ⟨hu, inferInstance⟩
  unfold deltaInv
  rw [Adjunction.homEquiv_counit]
  infer_instance

/-- The canonical open tensor isomorphism, oriented toward extension of tensor.
Source: Stacks 0E8I (blueprint: def-pur-system-tensor-mate-arrows). -/
def delta {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : D l E U) (N : D l E X) :
    (o.T X).obj ((o.J j).obj M, N) ≅
      (o.J j).obj ((o.T U).obj (M, (o.P j).obj N)) :=
  (@asIso _ _ _ _ (o.deltaInv j M N) (o.deltaInv_isIso j M N)).symm

end TensorOperations

end WeilConjectures.SystemTensorMate
