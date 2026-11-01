/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.Monoidal.Dualizable
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.TraceFormula.CategoricalTraceBiproduct
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.WeaklyEtaleIhom

/-!
# Perfect coefficient duals and their evaluation

Source: current blueprint, sec-six-functors/sk-prop-sf-dualizable-biduality,
prop-sf-dualizable; Stacks Project, Tags 08JI and 08JJ
(blueprint: prop-sf-dualizable).

For every commutative condensed coefficient ring the derived dual of a site-perfect
complex is site-perfect. Its local model is the signed termwise dual of the given
bounded finite-projective model. The evaluation is the tensor-Hom adjunction counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u a b

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures

/-- The canonical evaluation in the order K tensor K dual is the counit of the
ambient derived tensor-Hom adjunction at the coefficient unit.
Source: current blueprint prop-sf-dualizable, last sentence
(blueprint: prop-sf-dualizable). -/
def sixFunctorCoefficientEvaluation
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : AlgebraicGeometry.Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y)
      Ab.{u + 1}) (AlgebraicGeometry.ProEtale.condensedRingObj Λ Y))) :
    ((AlgebraicGeometry.ProEtale.CondensedRing.derivedTensor Λ Y).obj K).obj
      (((AlgebraicGeometry.ProEtale.CondensedRing.derivedHom Λ Y).obj (op K)).obj
        (𝟙_ _)) ⟶ 𝟙_ _ :=
  (AlgebraicGeometry.ProEtale.CondensedRing.derivedTensorHomAdjunction Λ K).counit.app (𝟙_ _)

end WeilConjectures

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

@[instance_reducible]
private def freePairing (Y : Scheme.{u}) (m : ℕ) :
    ExactPairing (Mod.finiteFree (condensedRingObj Λ Y) m)
      (Mod.finiteFree (condensedRingObj Λ Y) m) :=
  let A := Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)
  let : ExactPairing (Mod.regular (condensedRingObj Λ Y))
      (Mod.regular (condensedRingObj Λ Y)) :=
    inferInstanceAs (ExactPairing (𝟙_ A) (𝟙_ A))
  Bicone.exactPairing
    (biproduct.isBilimit fun _ : Fin m ↦ Mod.regular (condensedRingObj Λ Y))
    (biproduct.isBilimit fun _ : Fin m ↦ Mod.regular (condensedRingObj Λ Y))

private theorem projective_dualizable (Y : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : IsFiniteProjectiveOnCoefficientSite Λ Y M) : IsDualizable M := by
  obtain ⟨m, ⟨r⟩⟩ := hM
  let : HasRightDual (Mod.finiteFree (condensedRingObj Λ Y) m) :=
    { rightDual := _, exact := freePairing Λ Y m }
  exact IsDualizable.of_retract r ⟨inferInstance⟩

private theorem projective_rightDual (Y : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    [HasRightDual M] (hM : IsFiniteProjectiveOnCoefficientSite Λ Y M) :
    IsFiniteProjectiveOnCoefficientSite Λ Y Mᘁ := by
  obtain ⟨m, ⟨r⟩⟩ := hM
  let : HasRightDual (Mod.finiteFree (condensedRingObj Λ Y) m) :=
    { rightDual := _, exact := freePairing Λ Y m }
  refine ⟨m, ⟨{ i := r.rᘁ, r := r.iᘁ, retract := ?_ }⟩⟩
  rw [← comp_rightAdjointMate, r.retract, rightAdjointMate_id]

end AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures

open AlgebraicGeometry AlgebraicGeometry.ProEtale
  AlgebraicGeometry.ProEtale.CondensedRing

/-- The derived internal Hom into the pulled-back condensed coefficient ring of a
site-perfect complex is site-perfect, uniformly for all coefficient rings.
Source: current blueprint prop-sf-dualizable; Stacks Tags 08JI and 08JJ
(blueprint: prop-sf-dualizable).

Proof: on each member of the perfect cover choose the supplied bounded complex P.
Each term is a retract of a finite sum of the unit, so is dualizable. The signed
termwise right dual of P is bounded on the reflected interval; dualizing its term
retractions makes its terms finite projective. The existing chain-level exact
pairing descends through the K-flat localization, identifying this model with the
derived internal Hom into the unit. Weakly etale pullback commutes with that Hom
and preserves the unit. Composing these comparisons gives a perfect model on the
original cover. This includes zero ranks, empty intervals, and the empty scheme. -/
theorem sixFunctor_sitePerfect_dual
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u})
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)))
    (hK : IsPerfectOnCoefficientSite Λ Y K) :
    IsPerfectOnCoefficientSite Λ Y (((derivedHom Λ Y).obj (op K)).obj (𝟙_ _)) := by
  classical
  obtain ⟨C, hC⟩ := hK
  refine ⟨C, fun i ↦ ?_⟩
  obtain ⟨P, a, b, ha, hb, hP, ⟨eP⟩⟩ := hC i
  let := ha
  let := hb
  let (n : ℤ) : HasRightDual (P.X n) := (projective_dualizable Λ _ _ (hP n)).some
  let A := Mod (Sheaf (Scheme.ProEt.topology (C.X i)) Ab.{u + 1})
    (condensedRingObj Λ (C.X i))
  let := DerivedCategory.braidedCategory' (C := A)
  obtain ⟨pair⟩ := DerivedCategory.nonempty_exactPairing_Q_obj P a b
  let := pair
  let : ExactPairing (DerivedCategory.Q.obj P.rightDual) (DerivedCategory.Q.obj P) :=
    BraidedCategory.exactPairing_swap _ _
  have hf : WeaklyEtale (C.f i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ C.mem₀ (.mk i)
  let := hf
  let F := (upperStar Λ (C.f i)).leftDerivedFunctor
  let e := (leftDerivedUpperStarIsoMapDerivedCategory Λ (C.f i)).app K ≪≫ eP
  have := isIso_ihomComparison_leftDerivedUpperStar_of_weaklyEtale Λ (C.f i) K
  let h := asIso ((Functor.LaxMonoidal.ihomComparison F K).natTrans.app (𝟙_ _))
  let t := (derivedHom Λ (C.X i)).mapIso e.symm.op
  refine ⟨P.rightDual, -b, -a, inferInstance, inferInstance,
    (fun n ↦ projective_rightDual Λ _ _ (hP (-n))), ⟨?_⟩⟩
  exact ((leftDerivedUpperStarIsoMapDerivedCategory Λ (C.f i)).app _).symm ≪≫ h ≪≫
    (ihom (F.obj K)).mapIso (leftDerivedUpperStarUnitIso Λ (C.f i)) ≪≫
    t.app (𝟙_ _) ≪≫ MonoidalClosed.ihomObjUnitIso _ _

end WeilConjectures
