/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Paper.RegularQuotientCompletionUnit
public import Sheaf.Algebra.Homology.ChangeOfRingsComplex
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

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
set_option backward.isDefEq.respectTransparency false

universe u wR wS

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped ChangeOfRings

namespace CategoryTheory

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
  sorry

end CategoryTheory
