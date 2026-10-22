/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Paper.RegularQuotientCompletionUnit
public import Sheaf.Algebra.Homology.ChangeOfRingsComplex
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Paper.FiniteFreeQuotientTower
import Sheaf.Paper.FiniteFreeScalarExtension
import Sheaf.CategoryTheory.FinitePowerRoosComparison
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit

/-! # Finite free transport of quotient completion units

Source: Bhatt--Scholze, Lemma 3.4.12, pp. 22-23; Stacks Project, Modules on Sites,
Tags 03CY, 03DA, 03DB and Section 03EK
(blueprint: lem-pur-finite-free-quotient-completion).

Finite powers are categorical finite products, hence also finite direct sums in this
abelian category. The quotient tower uses the positive powers `n+1`. Both cone blocks
are specified below, so the comparison is the basis-induced strict cone comparison.

## Main definitions

* `IsFiniteFreeQuotientCompletionComparison`: the three isomorphisms with their
  basis-coordinate, quotient, cone-block and unit normalizations.

## Main statements

* `finiteFreeQuotientCompletion`: existence of that comparison and preservation of
  local derived principal completeness.
-/

@[expose] public noncomputable section

set_option autoImplicit false
-- Avoid traversing the large dependent tensor transports for tactic style linting.
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u wR wS

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped ChangeOfRings

namespace CategoryTheory

attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local irreducible] roosF limit reductionTensorTower koszulTensorFunctor
  regularQuotientCompletionUnit

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable {R S : Sheaf J CommRingCat.{u}}

/-- The usual degreewise products of module complexes, with the existing limit
instance supplied directly to avoid recursive instance search through evaluation.
Source: Stacks Project, Tag 03DB
(blueprint: lem-pur-finite-free-quotient-completion). -/
instance (priority := 1100) finiteFreeQuotientComplexProducts
    (T : Sheaf J CommRingCat.{u}) (I : Type)
    (H : I → CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)) ℤ) : HasProduct H :=
  (@HomologicalComplex.instHasLimitsOfShape _ ℤ (Discrete I) _ _ (.up ℤ) _
    (SheafOfModules.hasLimitsOfShape.{u} (D := Discrete I)
      (R := (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T))).has_limit
        (Discrete.functor H)

/-- Apply the coefficient map to a global section, using the existing sections functor.
Source: Stacks Project, Section 03EK; Bhatt--Scholze, Lemma 3.4.12
(blueprint: lem-pur-finite-free-quotient-completion). -/
def finiteFreeCoefficientSection (φ : R ⟶ S)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).sections) :
    (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)).sections :=
  (Functor.sectionsFunctor Cᵒᵖ).map (Functor.whiskerRight φ.hom (forget CommRingCat.{u})) a

/-- An elementary tensor followed by the actual sheafification unit. This does not assert
that all sections of the tensor sheaf are sectionwise tensors.
Source: Stacks Project, Tags 03CY and 03EK
(blueprint: lem-pur-finite-free-quotient-completion). -/
def finiteFreeExtendedTensorSection (φ : R ⟶ S)
    (M : ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (V : Cᵒᵖ) (s : S.obj.obj V) (m : M.val.obj V) :
    (SheafOfModules.changeOfRings φ M).val.obj V :=
  (toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app V
    (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] m)

/-- The shifted-product block of the specified quotient cone, projected to its nth term.
Source: Stacks Project, Tag 0941, and Bhatt--Scholze, Lemma 3.4.12
(blueprint: lem-pur-finite-free-quotient-completion). -/
def finiteFreeQuotientConeShiftedProjection
    (T : Sheaf J CommRingCat.{u})
    (H : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)) ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)).sections)
    (p : ℤ) (n : ℕ) :
    (regularQuotientCompletion T H a).X (p + 1) ⟶
      ((reductionTensorTower T H a).obj (op n)).X p :=
  (roosχ (koszulTowerComplex T (reductionTensorTower T H a)) p).hom ≫
    biprod.fst ≫ (Pi.π (fun n : ℕ ↦ (reductionTensorTower T H a).obj (op n)) n).f p

/-- The unshifted-product block of the specified quotient cone, projected to its nth term.
Source: Stacks Project, Tag 0941, and Bhatt--Scholze, Lemma 3.4.12
(blueprint: lem-pur-finite-free-quotient-completion). -/
def finiteFreeQuotientConeProductProjection
    (T : Sheaf J CommRingCat.{u})
    (H : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)) ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)).sections)
    (p : ℤ) (n : ℕ) :
    (regularQuotientCompletion T H a).X (p + 1) ⟶
      ((reductionTensorTower T H a).obj (op n)).X (p + 1) :=
  (roosχ (koszulTowerComplex T (reductionTensorTower T H a)) p).hom ≫
    biprod.snd ≫ (Pi.π (fun n : ℕ ↦ (reductionTensorTower T H a).obj (op n)) n).f (p + 1)

/-- The basis-induced scalar, quotient-tower and strict-cone isomorphisms, including
both cone blocks and the specified zero-component completion unit.
Source: Bhatt--Scholze, Lemma 3.4.12; Stacks Project, Tags 03CY, 03DA, 03DB and 03EK
(blueprint: lem-pur-finite-free-quotient-completion). -/
def IsFiniteFreeQuotientCompletionComparison
    (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ≅
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
          (SheafOfModules.unit
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).sections)
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) : Prop :=
  let U := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let Q := SheafOfModules.changeOfRingsComplex.{u, u} φ P
  let aS := finiteFreeCoefficientSection φ a
  let VR := reductionTensorTower R P a
  let VS := reductionTensorTower S Q aS
  let CR := regularQuotientCompletion R P a
  let CS := regularQuotientCompletion S Q aS
  ∃ (α : UC.obj Q ≅ ∏ᶜ fun _ : Fin d ↦ P)
    (θ : ∀ n : ℕ, UC.obj (VS.obj (op n)) ≅ ∏ᶜ fun _ : Fin d ↦ VR.obj (op n))
    (β : UC.obj CS ≅ ∏ᶜ fun _ : Fin d ↦ CR),
    (∀ (k : ℤ) (V : Cᵒᵖ) (s : S.obj.obj V) (p : (P.X k).val.obj V) (i : Fin d),
      (((α.hom ≫ Pi.π (fun _ : Fin d ↦ P) i).f k).val.app V)
        (finiteFreeExtendedTensorSection φ (P.X k) V s p) =
      @SMul.smul (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj.obj V)
        ((P.X k).val.obj V) (inferInstanceAs (SMul
          (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj.obj V)
          ((P.X k).val.obj V)))
        ((e.inv ≫ Pi.π (fun _ : Fin d ↦ SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) i).val.app V s) p) ∧
    (∀ n : ℕ, UC.map (koszulRepresentativeQuotient S Q aS n) ≫ (θ n).hom =
      α.hom ≫ Limits.Pi.map (f := fun _ : Fin d ↦ P)
        (g := fun _ : Fin d ↦ VR.obj (op n))
        (fun _ : Fin d ↦ koszulRepresentativeQuotient R P a n)) ∧
    (∀ (p : ℤ) (n : ℕ) (i : Fin d),
      (β.hom ≫ Pi.π (fun _ : Fin d ↦ CR) i).f (p + 1) ≫
        finiteFreeQuotientConeShiftedProjection R P a p n =
      U.map (finiteFreeQuotientConeShiftedProjection S Q aS p n) ≫
        ((θ n).hom ≫ Pi.π (fun _ : Fin d ↦ VR.obj (op n)) i).f p) ∧
    (∀ (p : ℤ) (n : ℕ) (i : Fin d),
      (β.hom ≫ Pi.π (fun _ : Fin d ↦ CR) i).f (p + 1) ≫
        finiteFreeQuotientConeProductProjection R P a p n =
      U.map (finiteFreeQuotientConeProductProjection S Q aS p n) ≫
        ((θ n).hom ≫ Pi.π (fun _ : Fin d ↦ VR.obj (op n)) i).f (p + 1)) ∧
    UC.map (regularQuotientCompletionUnit S Q aS) ≫ β.hom =
      α.hom ≫ Limits.Pi.map (f := fun _ : Fin d ↦ P)
        (g := fun _ : Fin d ↦ CR) (fun _ : Fin d ↦ regularQuotientCompletionUnit R P a)


attribute [local irreducible] finiteFreeQuotientConeShiftedProjection
  finiteFreeQuotientConeProductProjection

private theorem roosAugment_shifted
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {D : CochainComplex A ℤ}
    (γ : ∀ n : ℕ, D ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (p : ℤ) (n : ℕ) :
    (roosAugment γ hγ).f (p + 1) ≫ (roosχ X p).hom ≫ biprod.fst ≫
      (Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n).f p = 0 := by
  rw [← Category.assoc, ← Category.assoc, roosAugment_χ,
    biprod.lift_fst, zero_comp]

private theorem roosAugment_product
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    {X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} {D : CochainComplex A ℤ}
    (γ : ∀ n : ℕ, D ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (p : ℤ) (n : ℕ) :
    (roosAugment γ hγ).f (p + 1) ≫ (roosχ X p).hom ≫ biprod.snd ≫
      (Pi.π (fun n : ℕ ↦ X.asFunctor.obj (op n)) n).f (p + 1) =
        (γ n).f (p + 1) := by
  rw [← Category.assoc, ← Category.assoc, roosAugment_χ,
    biprod.lift_snd, ← HomologicalComplex.comp_f, Pi.lift_π]

private theorem finiteFree_unit_shifted
    (T : Sheaf J CommRingCat.{u})
    (H : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)) ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)).sections)
    (p : ℤ) (n : ℕ) :
    (regularQuotientCompletionUnit T H a).f (p + 1) ≫
      finiteFreeQuotientConeShiftedProjection T H a p n = 0 := by
  unfold finiteFreeQuotientConeShiftedProjection regularQuotientCompletionUnit
    principalTowerRoosUnit id
  exact roosAugment_shifted _ _ p n

private theorem finiteFree_unit_product
    (T : Sheaf J CommRingCat.{u})
    (H : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)) ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)).sections)
    (p : ℤ) (n : ℕ) :
    (regularQuotientCompletionUnit T H a).f (p + 1) ≫
      finiteFreeQuotientConeProductProjection T H a p n =
        (koszulRepresentativeQuotient T H a n).f (p + 1) := by
  unfold finiteFreeQuotientConeProductProjection regularQuotientCompletionUnit
    principalTowerRoosUnit id
  exact (roosAugment_product _ _ p n).trans
    (congrArg (fun f ↦ f.f (p + 1))
      (koszulRepresentativeAugmentation_quotient T H a n))

private theorem finiteFree_completion_ext
    (T : Sheaf J CommRingCat.{u})
    (H : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)) ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)).sections)
    {D : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj T)) ℤ}
    (f g : D ⟶ regularQuotientCompletion T H a)
    (hs : ∀ (p : ℤ) (n : ℕ), f.f (p + 1) ≫
      finiteFreeQuotientConeShiftedProjection T H a p n = g.f (p + 1) ≫
        finiteFreeQuotientConeShiftedProjection T H a p n)
    (hp : ∀ (p : ℤ) (n : ℕ), f.f (p + 1) ≫
      finiteFreeQuotientConeProductProjection T H a p n = g.f (p + 1) ≫
        finiteFreeQuotientConeProductProjection T H a p n) : f = g := by
  apply HomologicalComplex.Hom.ext
  funext k
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, k = p + 1 := ⟨k - 1, by omega⟩
  apply (cancel_mono (roosχ (koszulTowerComplex T (reductionTensorTower T H a)) p).hom).mp
  apply biprod.hom_ext
  · apply (isLimitOfPreserves (HomologicalComplex.eval _ (.up ℤ) p)
      (productIsProduct (fun n : ℕ ↦ (reductionTensorTower T H a).obj (op n)))).hom_ext
    rintro ⟨n⟩
    have h := hs p n
    unfold finiteFreeQuotientConeShiftedProjection at h
    simpa only [Functor.mapCone_π_app, Fan.mk_π_app,
      HomologicalComplex.eval_map, Category.assoc] using h
  · apply (isLimitOfPreserves (HomologicalComplex.eval _ (.up ℤ) (p + 1))
      (productIsProduct (fun n : ℕ ↦ (reductionTensorTower T H a).obj (op n)))).hom_ext
    rintro ⟨n⟩
    have h := hp p n
    unfold finiteFreeQuotientConeProductProjection at h
    simpa only [Functor.mapCone_π_app, Fan.mk_π_app,
      HomologicalComplex.eval_map, Category.assoc] using h

attribute [local irreducible] SheafOfModules.changeOfRingsComplex

private theorem finiteFree_unit_square
    (φ : R ⟶ S) (d : ℕ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).sections)
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (Q : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ) :
    let U := SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)
    let UC := U.mapHomologicalComplex (.up ℤ)
    let aS := finiteFreeCoefficientSection φ a
    ∀ (α : UC.obj Q ≅ ∏ᶜ fun _ : Fin d ↦ P)
      (θ : ∀ n : ℕ, UC.obj ((reductionTensorTower S Q aS).obj (op n)) ≅
        ∏ᶜ fun _ : Fin d ↦ (reductionTensorTower R P a).obj (op n))
      (β : UC.obj (regularQuotientCompletion S Q aS) ≅
        ∏ᶜ fun _ : Fin d ↦ regularQuotientCompletion R P a),
      (∀ n : ℕ, UC.map (koszulRepresentativeQuotient S Q aS n) ≫ (θ n).hom =
        α.hom ≫ Limits.Pi.map (fun _ : Fin d ↦ koszulRepresentativeQuotient R P a n)) →
      (∀ (p : ℤ) (n : ℕ) (i : Fin d),
        (β.hom ≫ Pi.π (fun _ : Fin d ↦ regularQuotientCompletion R P a) i).f (p + 1) ≫
          finiteFreeQuotientConeShiftedProjection R P a p n =
        U.map (finiteFreeQuotientConeShiftedProjection S Q aS p n) ≫
          ((θ n).hom ≫ Pi.π
            (fun _ : Fin d ↦ (reductionTensorTower R P a).obj (op n)) i).f p) →
      (∀ (p : ℤ) (n : ℕ) (i : Fin d),
        (β.hom ≫ Pi.π (fun _ : Fin d ↦ regularQuotientCompletion R P a) i).f (p + 1) ≫
          finiteFreeQuotientConeProductProjection R P a p n =
        U.map (finiteFreeQuotientConeProductProjection S Q aS p n) ≫
          ((θ n).hom ≫ Pi.π
            (fun _ : Fin d ↦ (reductionTensorTower R P a).obj (op n)) i).f (p + 1)) →
      UC.map (regularQuotientCompletionUnit S Q aS) ≫ β.hom =
        α.hom ≫ Limits.Pi.map (fun _ : Fin d ↦ regularQuotientCompletionUnit R P a) := by
  classical
  intro U UC aS α θ β hquot hs' hp'
  apply Pi.hom_ext
  intro i
  simp only [Category.assoc, Pi.map_π]
  apply finiteFree_completion_ext R P a
  · intro p n
    simp only [HomologicalComplex.comp_f, Category.assoc]
    have hs₀ := hs' p n i
    simp only [HomologicalComplex.comp_f, Category.assoc] at hs₀
    rw [hs₀]
    change U.map ((regularQuotientCompletionUnit S Q aS).f (p + 1)) ≫
      U.map (finiteFreeQuotientConeShiftedProjection S Q aS p n) ≫ _ = _
    have hz := congrArg U.map (finiteFree_unit_shifted S Q aS p n)
    simp only [Functor.map_comp, Functor.map_zero] at hz
    rw [← Category.assoc, hz, zero_comp]
    have hzR := finiteFree_unit_shifted R P a p n
    rw [← Category.assoc, hzR, comp_zero]
  · intro p n
    simp only [HomologicalComplex.comp_f, Category.assoc]
    have hp₀ := hp' p n i
    simp only [HomologicalComplex.comp_f, Category.assoc] at hp₀
    rw [hp₀]
    change U.map ((regularQuotientCompletionUnit S Q aS).f (p + 1)) ≫
      U.map (finiteFreeQuotientConeProductProjection S Q aS p n) ≫ _ = _
    have hq := congrArg U.map (finiteFree_unit_product S Q aS p n)
    simp only [Functor.map_comp] at hq
    rw [← Category.assoc, hq]
    have hqR := finiteFree_unit_product R P a p n
    rw [← Category.assoc, hqR]
    have h := congrArg (fun f ↦ (f ≫ Pi.π
      (fun _ : Fin d ↦ (reductionTensorTower R P a).obj (op n)) i).f (p + 1)) (hquot n)
    simp only [Category.assoc, Pi.map_π, HomologicalComplex.comp_f] at h
    change U.map ((koszulRepresentativeQuotient S Q aS n).f (p + 1)) ≫
      (θ n).hom.f (p + 1) ≫
        (Pi.π (fun _ : Fin d ↦ (reductionTensorTower R P a).obj (op n)) i).f (p + 1) =
      α.hom.f (p + 1) ≫ (Pi.π (fun _ : Fin d ↦ P) i).f (p + 1) ≫
        (koszulRepresentativeQuotient R P a n).f (p + 1) at h
    exact h

private instance finiteFree_restrict_countable_limits (φ : R ⟶ S) :
    PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)) := by
  let U := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)
  let G := SheafOfModules.forget.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      PresheafOfModules.toPresheaf.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj
  have : PreservesLimitsOfShape (Discrete ℕ) (U ⋙ G) :=
    inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
      (SheafOfModules.forget.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
          PresheafOfModules.toPresheaf.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S).obj))
  have : ReflectsLimitsOfShape (Discrete ℕ) G :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves U G

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteFree_tower_cone_comparison
    (φ : R ⟶ S) (d : ℕ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).sections)
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (Q : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ) :
  let U := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let aS := finiteFreeCoefficientSection φ a
  let VR := reductionTensorTower R P a
  let VS := reductionTensorTower S Q aS
  let CR := regularQuotientCompletion R P a
  let CS := regularQuotientCompletion S Q aS
  ∀ (α : UC.obj Q ≅ ∏ᶜ fun _ : Fin d ↦ P),
  ∃ (θ : ∀ n : ℕ, UC.obj (VS.obj (op n)) ≅ ∏ᶜ fun _ : Fin d ↦ VR.obj (op n))
    (β : UC.obj CS ≅ ∏ᶜ fun _ : Fin d ↦ CR),
    (∀ n : ℕ, UC.map (koszulRepresentativeQuotient S Q aS n) ≫ (θ n).hom =
      α.hom ≫ Limits.Pi.map (f := fun _ : Fin d ↦ P)
        (g := fun _ : Fin d ↦ VR.obj (op n))
        (fun _ : Fin d ↦ koszulRepresentativeQuotient R P a n)) ∧
    (∀ (p : ℤ) (n : ℕ) (i : Fin d),
      (β.hom ≫ Pi.π (fun _ : Fin d ↦ CR) i).f (p + 1) ≫
        finiteFreeQuotientConeShiftedProjection R P a p n =
      U.map (finiteFreeQuotientConeShiftedProjection S Q aS p n) ≫
        ((θ n).hom ≫ Pi.π (fun _ : Fin d ↦ VR.obj (op n)) i).f p) ∧
    (∀ (p : ℤ) (n : ℕ) (i : Fin d),
      (β.hom ≫ Pi.π (fun _ : Fin d ↦ CR) i).f (p + 1) ≫
        finiteFreeQuotientConeProductProjection R P a p n =
      U.map (finiteFreeQuotientConeProductProjection S Q aS p n) ≫
        ((θ n).hom ≫ Pi.π (fun _ : Fin d ↦ VR.obj (op n)) i).f (p + 1)) ∧
    UC.map (regularQuotientCompletionUnit S Q aS) ≫ β.hom =
      α.hom ≫ Limits.Pi.map (f := fun _ : Fin d ↦ P)
        (g := fun _ : Fin d ↦ CR) (fun _ : Fin d ↦ regularQuotientCompletionUnit R P a) := by
  classical
  intro U UC aS VR VS CR CS α
  let X := koszulTowerComplex S (reductionTensorTower S Q aS)
  let Y := koszulTowerComplex R (reductionTensorTower R P a)
  obtain ⟨τ₀, hquot₀⟩ := finiteFreeQuotientTower φ d P Q α a
  let τ : ((((Functor.whiskeringRight ℕᵒᵖ _ _).obj U).mapHomologicalComplex
      (.up ℤ)).obj X) ≅ ∏ᶜ fun _ : Fin d ↦ Y := τ₀
  let E (n : ℕ) := ((evaluation ℕᵒᵖ (SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))).obj
      (op n)).mapHomologicalComplex (.up ℤ)
  let θ (n : ℕ) : UC.obj ((reductionTensorTower S Q aS).obj (op n)) ≅
      ∏ᶜ fun _ : Fin d ↦ (reductionTensorTower R P a).obj (op n) :=
    (E n).mapIso τ ≪≫ PreservesProduct.iso (E n) (fun _ : Fin d ↦ Y)
  have hquot (n : ℕ) :
      UC.map (koszulRepresentativeQuotient S Q aS n) ≫ (θ n).hom =
        α.hom ≫ Limits.Pi.map (fun _ : Fin d ↦ koszulRepresentativeQuotient R P a n) :=
    hquot₀ n
  obtain ⟨β₀, hs, hp⟩ := finitePowerRoosComparison U d X Y τ
  let β : UC.obj (regularQuotientCompletion S Q aS) ≅
      ∏ᶜ fun _ : Fin d ↦ regularQuotientCompletion R P a := β₀
  have hs' (p : ℤ) (n : ℕ) (i : Fin d) :
      (β.hom ≫ Pi.π (fun _ : Fin d ↦ regularQuotientCompletion R P a) i).f (p + 1) ≫
        finiteFreeQuotientConeShiftedProjection R P a p n =
      U.map (finiteFreeQuotientConeShiftedProjection S Q aS p n) ≫
        ((θ n).hom ≫ Pi.π
          (fun _ : Fin d ↦ (reductionTensorTower R P a).obj (op n)) i).f p := by
    unfold finiteFreeQuotientConeShiftedProjection
    exact hs p n i
  have hp' (p : ℤ) (n : ℕ) (i : Fin d) :
      (β.hom ≫ Pi.π (fun _ : Fin d ↦ regularQuotientCompletion R P a) i).f (p + 1) ≫
        finiteFreeQuotientConeProductProjection R P a p n =
      U.map (finiteFreeQuotientConeProductProjection S Q aS p n) ≫
        ((θ n).hom ≫ Pi.π
          (fun _ : Fin d ↦ (reductionTensorTower R P a).obj (op n)) i).f (p + 1) := by
    unfold finiteFreeQuotientConeProductProjection
    exact hp p n i
  have hunit := finiteFree_unit_square φ d a P Q α θ β hquot hs' hp'
  exact ⟨θ, β, hquot, hs', hp', hunit⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem finiteFree_complete_of_unit_square
    [HasDerivedCategory.{wR} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S))]
    [∀ V : C, HasDerivedCategory.{wR} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over V)))]
    [∀ V : C, HasDerivedCategory.{wS} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat.{u} RingCat.{u})).obj (S.over V)))]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S))]
    (φ : R ⟶ S) (d : ℕ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).sections)
    (_haR : Mono (globalSectionMultiplication R a))
    (_haS : Mono (globalSectionMultiplication S (finiteFreeCoefficientSection φ a)))
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (Q : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (hQi : CochainComplex.IsKFlatIndependentCoefficients (R := S) Q) :
  let U := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let aS := finiteFreeCoefficientSection φ a
  ∀ (α : UC.obj Q ≅ ∏ᶜ fun _ : Fin d ↦ P)
    (β : UC.obj (regularQuotientCompletion S Q aS) ≅
      ∏ᶜ fun _ : Fin d ↦ regularQuotientCompletion R P a),
    UC.map (regularQuotientCompletionUnit S Q aS) ≫ β.hom =
      α.hom ≫ Limits.Pi.map (fun _ : Fin d ↦ regularQuotientCompletionUnit R P a) →
    IsLocallyDerivedRingedIdealComplete R
      (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      (globalSectionMultiplication R a) (DerivedCategory.Q.{wR}.obj P) →
    IsLocallyDerivedRingedIdealComplete S
      (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
      (globalSectionMultiplication S aS) (DerivedCategory.Q.{wS}.obj Q) := by
  classical
  intro U UC aS α β hunit hcomplete
  have (T : Sheaf J RingCat.{u}) : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} T) :=
    (moduleSheaves_colimits_forgetful.{u, u, u, u} T).2.1
  have (T : Sheaf J RingCat.{u}) : PreservesFiniteColimits (SheafOfModules.toSheaf.{u} T) :=
    (moduleSheaves_colimits_forgetful.{u, u, u, u} T).2.2.1
  have : PreservesFiniteLimits U := by
    have : PreservesFiniteLimits (U ⋙ SheafOfModules.toSheaf.{u} _) :=
      inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} _))
    exact preservesFiniteLimits_of_reflects_of_preserves U (SheafOfModules.toSheaf.{u} _)
  have : PreservesFiniteColimits U := by
    have : PreservesFiniteColimits (U ⋙ SheafOfModules.toSheaf.{u} _) :=
      inferInstanceAs (PreservesFiniteColimits (SheafOfModules.toSheaf.{u} _))
    exact preservesFiniteColimits_of_reflects_of_preserves U (SheafOfModules.toSheaf.{u} _)
  have : U.ReflectsIsomorphisms := by
    have : (U ⋙ SheafOfModules.toSheaf.{u} _).ReflectsIsomorphisms :=
      inferInstanceAs ((SheafOfModules.toSheaf.{u} _).ReflectsIsomorphisms)
    exact reflectsIsomorphisms_of_comp U (SheafOfModules.toSheaf.{u} _)
  have hR : IsIso (DerivedCategory.Q.{wR}.map (regularQuotientCompletionUnit R P a)) :=
    (regularQuotientCompletionUnit_criterion R a _haR P _hP).2.1.mp hcomplete
  have hqR : QuasiIso (regularQuotientCompletionUnit R P a) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hR
  let : HasExactLimitsOfShape (Discrete (Fin d)) (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :=
    hasExactLimitsOfShape_discrete_finite _
  have hpi : QuasiIso (Limits.Pi.map (fun _ : Fin d ↦
      regularQuotientCompletionUnit R P a)) := by
    have (j : Discrete (Fin d)) : QuasiIso
        ((Discrete.natTrans (F := Discrete.functor (fun _ : Fin d ↦ P))
          (G := Discrete.functor (fun _ : Fin d ↦ regularQuotientCompletion R P a))
          (fun _ ↦ regularQuotientCompletionUnit R P a)).app j) := hqR
    exact HomologicalComplex.quasiIso_limMap
      (Discrete.natTrans (F := Discrete.functor (fun _ : Fin d ↦ P))
        (G := Discrete.functor (fun _ : Fin d ↦ regularQuotientCompletion R P a))
        (fun _ ↦ regularQuotientCompletionUnit R P a))
  have hUunit : QuasiIso (UC.map (regularQuotientCompletionUnit S Q aS)) := by
    apply (quasiIso_iff_comp_right _ β.hom).mp
    rw [hunit]
    infer_instance
  have hSunit : QuasiIso (regularQuotientCompletionUnit S Q aS) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ U).mp hUunit
  exact (regularQuotientCompletionUnit_criterion S aS _haS Q hQi).2.1.mpr
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mpr hSunit)

set_option backward.isDefEq.respectTransparency true in
/-- The chosen finite basis identifies scalar extension and its strict quotient cone
with finite sums, preserves the specified zero-component unit, and carries locally
principal-derived-complete objects to locally principal-derived-complete objects.

Source: Bhatt--Scholze, Lemma 3.4.12, pp. 22-23, with the explicit finite-free
ringed-site argument; Stacks Project, Tags 03CY, 03DA, 03DB, 03EK and 0G7E
(blueprint: lem-pur-finite-free-quotient-completion).

Proof plan:
1. Restriction leaves underlying abelian sheaves unchanged. By the module-sheaf
limits/colimits theorem (03DA, 03DB), it is exact, preserves products and finite sums,
and reflects acyclicity and quasi-isomorphisms, without any assumption on points.
2. Write lambda_i for the inverse basis coordinates. The maps s tensor p maps to
(lambda_i(s) p)_i and (p_i)_i maps to sum_i b_i tensor p_i are mutually inverse.
They are balanced, respect restrictions, extend by sheafification (03CY, 03EK), and
commute with differentials. These give alpha, including the empty basis case.
3. Identify H tensor T/a^(n+1) with H/a^(n+1)H by local lifts and sheafification.
The basis coordinates commute with multiplication by a, giving theta_n, characterized
by its quotient square. Reduction commutes with the coordinates, so theta is a strict
tower isomorphism after finite reindexing.
4. Products are sectionwise; reindex ((x_ni)_i)_n as ((x_ni)_n)_i. This commutes
with the tower shift and one minus shift. Apply the same map separately to both
cone blocks. It respects the signed cone differential and gives beta with exactly
the two displayed block normalizations.
5. The specified unit has quotient components and zero shifted-product component.
The quotient square of theta and the block normalizations give the displayed equality
of chain maps beta U(eta_S) = eta_R^d alpha.
6. If P is locally derived complete, its specified unit is invertible by the regular
quotient criterion. Its finite sum is a quasi-isomorphism. The equality in step 5 and
reflection of quasi-isomorphisms show that the specified unit over S is invertible.
7. K-flat change of rings with flat terms (0G7E) gives K-flatness of Q. The regular
quotient criterion over S then gives internal-Hom vanishing on every slice for every
local element of the principal ideal in S, without assuming those elements lift to R.
-/
theorem finiteFreeQuotientCompletion
    [HasDerivedCategory.{wR} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S))]
    [∀ V : C, HasDerivedCategory.{wR} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over V)))]
    [∀ V : C, HasDerivedCategory.{wS} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat.{u} RingCat.{u})).obj (S.over V)))]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S))]
    (φ : R ⟶ S) (d : ℕ)
    (e : (∏ᶜ fun _ : Fin d ↦ SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ≅
      (SheafOfModules.restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
          (SheafOfModules.unit
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)))
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).sections)
    (_haR : Mono (globalSectionMultiplication R a))
    (_haS : Mono (globalSectionMultiplication S (finiteFreeCoefficientSection φ a)))
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P)
    (_hflat : ∀ k : ℤ, exactFunctor _ _ (tensorRight (P.X k))) :
    IsFiniteFreeQuotientCompletionComparison φ d e a P ∧
    (IsLocallyDerivedRingedIdealComplete R
        (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
        (globalSectionMultiplication R a) (DerivedCategory.Q.{wR}.obj P) →
      IsLocallyDerivedRingedIdealComplete S
        (SheafOfModules.unit
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
        (globalSectionMultiplication S (finiteFreeCoefficientSection φ a))
        (DerivedCategory.Q.{wS}.obj (SheafOfModules.changeOfRingsComplex.{u, u} φ P))) := by
  classical
  let U := SheafOfModules.restrictScalars.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let Q : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S)) ℤ :=
    SheafOfModules.changeOfRingsComplex.{u, u} φ P
  let aS := finiteFreeCoefficientSection φ a
  obtain ⟨α, hα⟩ := SheafOfModules.finiteFreeScalarExtension φ d e P
  obtain ⟨θ, β, hquot, hs', hp', hunit⟩ :=
    finiteFree_tower_cone_comparison φ d a P Q α
  have hc : IsFiniteFreeQuotientCompletionComparison φ d e a P :=
    ⟨α, θ, β, hα, hquot, hs', hp', hunit⟩
  refine ⟨hc, ?_⟩
  intro hcomplete
  have hK := (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp _hP
  have hQ := (SheafOfModules.changeOfRings_isKFlat_of_flat_terms φ P hK _hflat).1
  have hQi : CochainComplex.IsKFlatIndependentCoefficients (R := S) Q :=
    (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q).mpr hQ
  exact finiteFree_complete_of_unit_square φ d a _haR _haS P Q _hP hQi
    α β hunit hcomplete

end CategoryTheory
