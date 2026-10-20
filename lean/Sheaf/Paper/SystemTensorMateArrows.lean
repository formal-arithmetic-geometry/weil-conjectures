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
import Mathlib.CategoryTheory.Adjunction.Triple

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

private theorem sequence_isSheaf_of_slices {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) (P : (ℕ × C)ᵒᵖ ⥤ Type (u + 1))
    (hP : ∀ n : ℕ, Presieve.IsSheaf J ((Prod.sectR n C).op ⋙ P)) :
    Presieve.IsSheaf (coefficientSequenceTopology J) P := by
  intro X S hS x hx
  let xv : Presieve.FamilyOfElements ((Prod.sectR X.1 C).op ⋙ P)
      (S.functorPullback (Prod.sectR X.1 C)).arrows :=
    fun Y f hf ↦ x ((Prod.sectR X.1 C).map f) hf
  have hxv : xv.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ he
    exact hx ((Prod.sectR X.1 C).map g₁) ((Prod.sectR X.1 C).map g₂)
      hf₁ hf₂ (by simpa only [← Functor.map_comp] using
        (congrArg (fun f ↦ (Prod.sectR X.1 C).map f) he))
  obtain ⟨a, ha, hua⟩ := hP X.1 _ hS xv hxv
  refine ⟨a, ?_, ?_⟩
  · intro Y f hf
    apply ((hP Y.1).isSeparated _ (J.pullback_stable f.2 hS)).ext
    intro Z g hg
    let v : (X.1, Z) ⟶ X := (Prod.sectR X.1 C).map (g ≫ f.2)
    let k : (Y.1, Z) ⟶ (X.1, Z) := Prod.mkHom f.1 (𝟙 Z)
    have hv : S v := hg
    have he : k ≫ v = (Prod.sectR Y.1 C).map g ≫ f := by
      ext <;> simp [k, v]
    have hc := hx k ((Prod.sectR Y.1 C).map g) hv hf he
    have hag := congrArg (P.map k.op) (ha (g ≫ f.2) hv)
    change P.map ((Prod.sectR Y.1 C).map g).op (P.map f.op a) = _
    erw [← P.map_comp_apply, ← op_comp, ← he]
    have hp : P.map (k ≫ v).op a = P.map k.op (P.map v.op a) := by
      rw [op_comp, P.map_comp]
      rfl
    exact hp.trans (hag.trans hc)
  · intro b hb
    apply hua b
    intro Y f hf
    exact hb ((Prod.sectR X.1 C).map f) hf

/-- Base change is continuous for vertical coverings.
Source: Stacks 0941, 09A5 (blueprint: def-pur-system-tensor-mate-arrows).
Proof: restrict a system sheaf to a vertical slice. Pro-etale base change is
continuous there. The horizontal maps retain their index and commute with the
same vertical restrictions, giving the system sheaf condition. -/
theorem base_continuous {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (base f).IsContinuous (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) := by
  constructor
  intro G
  apply sequence_isSheaf_of_slices
  intro n
  have hG := (Prod.sectR n X.ProEt).op_comp_isSheaf_of_isSheaf_type
    (Scheme.ProEt.topology X) ((isSheaf_iff_isSheaf_of_type _ _).1 G.property)
  have h := (Scheme.proEtaleBaseChange f).op_comp_isSheaf_of_isSheaf_type
    (Scheme.ProEt.topology Y) hG
  exact h

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
  sorry

private theorem ringHom_ext_scalar (W : Scheme.{u})
    {H : Sheaf (coefficientSequenceTopology (Scheme.ProEt.topology W))
      CommRingCat.{u + 1}} (a b : (R l E W).obj ⟶ H.obj)
    (h : ∀ n U z, a.app (op (n, U)) (scalar l E W n U z) =
      b.app (op (n, U)) (scalar l E W n U z)) : a = b := by
  let e (c : (R l E W).obj ⟶ H.obj) (n : ℕ) : integralCoefficientCommRingSheaf l E W n ⟶
      ((Prod.sectR n W.ProEt).sheafPushforwardContinuous CommRingCat.{u + 1}
        (Scheme.ProEt.topology W)
        (coefficientSequenceTopology (Scheme.ProEt.topology W))).obj H :=
    ⟨{ app := fun U ↦ c.app (op (n, U.unop))
       naturality := fun U V f ↦ by
         have hc := c.naturality ((Prod.sectR n W.ProEt).op.map f)
         erw [ring_vertical_map l E W n f] at hc
         exact hc }⟩
  have he (n : ℕ) : e a n = e b n := by
    apply ((sheafificationAdjunction (Scheme.ProEt.topology W) CommRingCat.{u + 1}).homEquiv
      ((Functor.const W.ProEtᵒᵖ).obj (CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) _).injective
    apply NatTrans.ext
    funext U
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    exact h n U.unop z
  apply NatTrans.ext
  funext V
  exact congrArg (fun c ↦ c.hom.app (op V.unop.2)) (he V.unop.1)

private def openBase {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    ℕ × U.ProEt ⥤ ℕ × X.ProEt :=
  (𝟭 ℕ).prod (Scheme.proEtaleOpenComposition j)

private instance openComposition_continuous {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (Scheme.proEtaleOpenComposition j).IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) :=
  Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)

private instance openBase_continuous {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (openBase j).IsContinuous (coefficientSequenceTopology (Scheme.ProEt.topology U))
      (coefficientSequenceTopology (Scheme.ProEt.topology X)) := by
  constructor
  intro G
  apply sequence_isSheaf_of_slices
  intro n
  have hG := (Prod.sectR n X.ProEt).op_comp_isSheaf_of_isSheaf_type
    (Scheme.ProEt.topology X) ((isSheaf_iff_isSheaf_of_type _ _).1 G.property)
  have : (Scheme.proEtaleOpenComposition j).IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)
  exact (Scheme.proEtaleOpenComposition j).op_comp_isSheaf_of_isSheaf_type
    (Scheme.ProEt.topology U) hG

private def openConstant {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    constantSheaf (Scheme.ProEt.topology U) CommRingCat.{u + 1} ⟶
      constantSheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1} ⋙
        (Scheme.proEtaleOpenComposition j).sheafPushforwardContinuous
          CommRingCat.{u + 1} (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) := by
  let G := Scheme.proEtaleOpenComposition j
  have : G.IsContinuous (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)
  have : G.IsCocontinuous (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  exact Functor.whiskerLeft (Functor.const X.ProEtᵒᵖ)
    (G.pushforwardContinuousSheafificationCompatibility CommRingCat.{u + 1}
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)).hom

private def openCoefficient_system {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    coefficientSequenceCommRingSystem l E U ⟶
    coefficientSequenceCommRingSystem l E X ⋙
      (Scheme.proEtaleOpenComposition j).sheafPushforwardContinuous CommRingCat.{u + 1}
        (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) :=
  NatTrans.ofOpSequence
    (fun n ↦ (openConstant j).app (CommRingCat.of
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))
    (fun n ↦ by
      dsimp only [Functor.comp_map, coefficientSequenceCommRingSystem]
      rw [Functor.ofOpSequence_map_homOfLE_succ,
        Functor.ofOpSequence_map_homOfLE_succ]
      exact (openConstant j).naturality _)

private def openCoefficient {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    R l E U ⟶ ((openBase j).sheafPushforwardContinuous CommRingCat.{u + 1}
      (coefficientSequenceTopology (Scheme.ProEt.topology U))
      (coefficientSequenceTopology (Scheme.ProEt.topology X))).obj (R l E X) :=
  ⟨sequenceMap (Scheme.proEtaleOpenComposition j)
    (coefficientSequenceCommRingSystem l E U ⋙
      sheafToPresheaf (Scheme.ProEt.topology U) CommRingCat.{u + 1})
    (coefficientSequenceCommRingSystem l E X ⋙
      sheafToPresheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (Functor.whiskerRight (openCoefficient_system l E j)
      (sheafToPresheaf (Scheme.ProEt.topology U) CommRingCat.{u + 1}))⟩

private theorem openCoefficient_scalar {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (n : ℕ) (V : U.ProEt)
    (z : ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) :
    (openCoefficient l E j).hom.app (op (n, V)) (scalar l E U n V z) =
      scalar l E X n ((Scheme.proEtaleOpenComposition j).obj V) z := by
  let G := Scheme.proEtaleOpenComposition j
  have : G.IsContinuous (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)
  have : G.IsCocontinuous (Scheme.ProEt.topology U) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isCocontinuous_overMap (inferInstance : WeaklyEtale j)
  exact congrArg (fun c ↦ c.app (op V) z)
    (G.toSheafify_pullbackSheafificationCompatibility CommRingCat.{u + 1}
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))))

private def openSiteAdjunction {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    openBase j ⊣ base j := by
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  exact
    { unit :=
        { app V := Prod.mkHom (𝟙 V.1) (a.unit.app V.2)
          naturality := fun V W f ↦ by
            ext
            · simp [openBase, base]
            · exact a.unit.naturality f.2 }
      counit :=
        { app V := Prod.mkHom (𝟙 V.1) (a.counit.app V.2)
          naturality := fun V W f ↦ by
            ext
            · simp [openBase, base]
            · exact a.counit.naturality f.2 }
      left_triangle_components V := by
        ext
        · simp [openBase, base]
        · exact a.left_triangle_components V.2
      right_triangle_components V := by
        ext
        · simp [openBase, base]
        · exact a.right_triangle_components V.2 }

private theorem openSiteAdjunction_unit_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : IsIso (openSiteAdjunction j).unit := by
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  have : IsIso a.unit := inferInstance
  let e : 𝟭 (ℕ × U.ProEt) ≅ openBase j ⋙ base j :=
    NatIso.ofComponents (fun V ↦ Iso.prod (Iso.refl V.1) ((asIso a.unit).app V.2))
      (by
        intro V W f
        ext
        · simp [openBase, base]
        · exact a.unit.naturality f.2)
  change IsIso e.hom
  infer_instance

private theorem pushforwardAdj_counit_isIso
    {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : C ⥤ D} {G : D ⥤ C}
    [F.IsContinuous J K] [G.IsContinuous K J]
    {S : Sheaf J RingCat.{u + 1}} {R : Sheaf K RingCat.{u + 1}}
    (a : F ⊣ G) [IsIso a.unit]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1} J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u + 1} K J).obj S)
    (H₁ : Functor.whiskerRight (NatTrans.op a.counit) R.obj =
      ψ.hom ≫ G.op.whiskerLeft φ.hom)
    (H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit) S.obj = 𝟙 S.obj) :
    IsIso (SheafOfModules.pushforwardPushforwardAdj a φ ψ H₁ H₂).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [← isIso_iff_of_reflects_iso _
    (SheafOfModules.forget S ⋙ PresheafOfModules.toPresheaf S.obj)]
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  change IsIso (M.val.presheaf.map (a.unit.app V.unop).op)
  infer_instance

section

attribute [local irreducible] coefficientSequenceCommRingSheaf

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem openCoefficient_counit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    Functor.whiskerRight (NatTrans.op (openSiteAdjunction j).counit) (R l E X).obj =
      (coefficient l E j).hom ≫ (base j).op.whiskerLeft
        (openCoefficient l E j).hom := by
  let JU := coefficientSequenceTopology (Scheme.ProEt.topology U)
  let JX := coefficientSequenceTopology (Scheme.ProEt.topology X)
  let a := openSiteAdjunction j
  let F := openBase j
  let G := base j
  have : (G ⋙ F).IsContinuous JX JX := Functor.isContinuous_comp _ _ _ JU _
  apply ringHom_ext_scalar l E X
    (H := ((G ⋙ F).sheafPushforwardContinuous CommRingCat.{u + 1}
      JX JX).obj (R l E X))
  intro n V z
  change (R l E X).obj.map (a.counit.app (n, V)).op
        (scalar l E X n V z) =
      (openCoefficient l E j).hom.app (op (n, (Scheme.proEtaleBaseChange j).obj V))
        ((coefficient l E j).hom.app (op (n, V)) (scalar l E X n V z))
  rw [coefficient_scalar, openCoefficient_scalar]
  have hc : a.counit.app (n, V) =
      (Prod.sectR n X.ProEt).map (a.counit.app (n, V)).2 := rfl
  rw [hc]
  exact scalar_map l E X n _ z

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem openCoefficient_unit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (openCoefficient l E j).hom ≫ (openBase j).op.whiskerLeft (coefficient l E j).hom ≫
      Functor.whiskerRight (NatTrans.op (openSiteAdjunction j).unit) (R l E U).obj =
        𝟙 (R l E U).obj := by
  let a := openSiteAdjunction j
  apply ringHom_ext_scalar l E U (H := R l E U)
  intro n V z
  change (R l E U).obj.map (a.unit.app (n, V)).op
        ((coefficient l E j).hom.app
          (op (n, (Scheme.proEtaleOpenComposition j).obj V))
          ((openCoefficient l E j).hom.app (op (n, V)) (scalar l E U n V z))) =
      scalar l E U n V z
  rw [openCoefficient_scalar, coefficient_scalar]
  have hc : a.unit.app (n, V) =
      (Prod.sectR n U.ProEt).map (a.unit.app (n, V)).2 := rfl
  rw [hc]
  exact scalar_map l E U n _ z

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem direct_open_counit_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    ∃ (L : S l E X ⥤ S l E U) (a : L ⊣ direct l E j), IsIso a.counit := by
  let JU := coefficientSequenceTopology (Scheme.ProEt.topology U)
  let JX := coefficientSequenceTopology (Scheme.ProEt.topology X)
  let a := openSiteAdjunction j
  let F := openBase j
  let G := base j
  let d := openCoefficient l E j
  let c := coefficient l E j
  have H₁c := openCoefficient_counit l E j
  have H₂c := openCoefficient_unit l E j
  let φ : ring.{u + 1, u, u + 1} JU (R l E U) ⟶
      (F.sheafPushforwardContinuous RingCat.{u + 1} JU JX).obj
        (ring.{u + 1, u, u + 1} JX (R l E X)) :=
    ⟨Functor.whiskerRight d.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let ψ : ring.{u + 1, u, u + 1} JX (R l E X) ⟶
      (G.sheafPushforwardContinuous RingCat.{u + 1} JX JU).obj
        (ring.{u + 1, u, u + 1} JU (R l E U)) :=
    ⟨Functor.whiskerRight c.hom (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have H₁ : Functor.whiskerRight (NatTrans.op a.counit)
      (ring.{u + 1, u, u + 1} JX (R l E X)).obj = ψ.hom ≫ G.op.whiskerLeft φ.hom :=
    congrArg (fun t ↦ Functor.whiskerRight t
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) H₁c
  have H₂ : φ.hom ≫ F.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op a.unit)
        (ring.{u + 1, u, u + 1} JU (R l E U)).obj = 𝟙 _ :=
    congrArg (fun t ↦ Functor.whiskerRight t
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) H₂c
  let radj := SheafOfModules.pushforwardPushforwardAdj a φ ψ H₁ H₂
  refine ⟨SheafOfModules.pushforward φ, radj, ?_⟩
  have : IsIso a.unit := openSiteAdjunction_unit_isIso j
  exact pushforwardAdj_counit_isIso a φ ψ H₁ H₂

end

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
  obtain ⟨L, a, ha⟩ := direct_open_counit_isIso l E j
  have : IsIso a.counit := ha
  have : (direct l E j).Full := a.fullyFaithfulROfIsIsoCounit.full
  have : (direct l E j).Faithful := a.fullyFaithfulROfIsIsoCounit.faithful
  have : IsIso (o.adj j).counit := (o.adj j).counit_isIso_of_R_fully_faithful
  exact (Adjunction.Triple.isIso_unit_iff_isIso_counit
    (⟨o.openAdj j, o.adj j⟩ : Adjunction.Triple _ _ _)).2 inferInstance

/-- The inverse open unit is fixed by its two inverse identities.
Source: Stacks 03DI (blueprint: def-pur-system-tensor-mate-arrows). -/
def ordinaryOpenUnitInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  @inv _ _ _ _ (o.openAdj j).unit (o.ordinaryOpenUnit_isIso j)

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
  sorry

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
  sorry

/-- The canonical open tensor isomorphism, oriented toward extension of tensor.
Source: Stacks 0E8I (blueprint: def-pur-system-tensor-mate-arrows). -/
def delta {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : D l E U) (N : D l E X) :
    (o.T X).obj ((o.J j).obj M, N) ≅
      (o.J j).obj ((o.T U).obj (M, (o.P j).obj N)) :=
  (@asIso _ _ _ _ (o.deltaInv j M N) (o.deltaInv_isIso j M N)).symm

end TensorOperations

end WeilConjectures.SystemTensorMate
