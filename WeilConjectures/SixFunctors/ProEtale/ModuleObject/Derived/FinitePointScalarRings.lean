/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Field.ULift
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Conv
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
public import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import WeilConjectures.CategoryTheory.RingObjects.Condensed.PadicAlgClGlobalSections

/-! # Noetherian scalar rings in the cohomological finiteness theorem
Source: latest blueprint sk-lem-finite, Complement
(blueprint: lem-sf-finite-point-scalar-rings).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.CondensedRing

private def constantSection (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (S : Profinite.{u}ᵒᵖ) :
    A →+* (Profinite.continuousCoefficientRingPresheaf A).obj S where
  toFun a := ULift.up (ContinuousMap.const _ a)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private def constantGlobal (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] : A →+* Γ (Profinite.continuousCoefficientRingObj A) :=
  Sheaf.ringHomΓSheafCompose (coherentTopology Profinite.{u})
    (Profinite.continuousCoefficientRingSheaf A) (constantSection A) fun _ _ ↦ rfl

private theorem constantGlobal_surjective (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] : Function.Surjective (constantGlobal A) := by
  intro x
  let adj := sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}
  let x' := adj.homEquiv _ _
    (inv (Functor.LaxMonoidal.ε (presheafToSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
      ≫ x.hom)
  let b := x'.app (op (Profinite.of PUnit.{u + 1})) (ULift.up 1)
  refine ⟨b.down PUnit.unit, ?_⟩
  have hx : x' = (Functor.ringHomΓCompForget₂
      (Profinite.continuousCoefficientRingSheaf A).obj (constantSection A)
      (fun _ _ ↦ rfl) (b.down PUnit.unit)).hom := by
    ext S n
    obtain ⟨m⟩ := n
    have key : x'.app S (ULift.up 1) = (Profinite.continuousCoefficientRingObj A).obj.map
        (Profinite.isTerminalPUnit.from S.unop).op b :=
      NatTrans.naturality_apply x' (Profinite.isTerminalPUnit.from S.unop).op (ULift.up 1)
    have hm : (ULift.up m : ULift.{u + 1} ℤ) = m • ULift.up 1 := by
      ext
      simp
    refine (congrArg (x'.app S) hm).trans ?_
    rw [map_zsmul, key]
    exact (zsmul_eq_mul (α := (Profinite.continuousCoefficientRingPresheaf A).obj S)
      _ m).trans rfl
  ext1
  rw [constantGlobal, Sheaf.ringHomΓSheafCompose, RingHom.comp_apply, RingHom.comp_apply,
    Γ.map_hom, Γ.mapFunctor_hom, ← hx, Category.assoc,
    Sheaf.sheafifyRingPresheafIso, asIso_hom, ← Adjunction.homEquiv_counit,
    Equiv.symm_apply_apply, IsIso.hom_inv_id_assoc]

private theorem integral_scalar_noetherian (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type u) [Field E] [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] :
    IsNoetherianRing (Γ (DerivedNakayama.integerRing ℓ E)) := by
  let := (Padic.coefficientExtensionAbsoluteValue ℓ E).toNormedField
  have h := (Padic.extension_integers_dvr ℓ E (Padic.coefficientExtensionAbsoluteValue ℓ E)
    (spectralNorm_extends (K := Padic ℓ) (L := E))).choose_spec.choose_spec
  let : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers ℓ E) :=
    h.2.2.2.2.2.2.2.2.1
  exact isNoetherianRing_of_surjective (Padic.coefficientExtensionIntegers ℓ E)
    (Γ (DerivedNakayama.integerRing ℓ E))
    (constantGlobal (Padic.coefficientExtensionIntegers ℓ E)) (constantGlobal_surjective _)

/-- The exact scalar rings Γ Λ used in the statement are Noetherian at the integral
and both rational stages. This includes the chosen universe lift of the coefficient
field; no equality of that ring with an auxiliary scalar ring is presumed.

Source: latest blueprint sec-six-functors/sk-lem-finite/sk-lem-finite.proof.md,
first paragraph and Complement (blueprint: lem-sf-finite-point-scalar-rings).

Proof: a global section of a continuous condensed ring is a map from the sheafified
constant integer presheaf. Adjunction turns it into a natural presheaf map; its value
on 1 at the one-point profinite set determines it. Every such value is a constant
continuous function, so the coefficient ring surjects onto Γ Λ. The same assertion
for Qbar follows from the recorded finite-subextension constant-section theorem.
The chosen integral coefficient ring is a principal ideal ring by the DVR theorem,
hence Noetherian; the rational coefficient rings are fields. A surjective image of a
Noetherian ring is Noetherian. -/
theorem finite_point_scalar_rings (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    IsNoetherianRing (Γ (DerivedNakayama.integerRing ℓ (ULift.{u} E))) ∧
    IsNoetherianRing (Γ (Profinite.continuousMapRingObj.{u} E)) ∧
    IsNoetherianRing (Γ (Profinite.padicAlgClRingObj.{u} ℓ)) := by
  refine ⟨integral_scalar_noetherian ℓ (ULift.{u} E), ?_, ?_⟩
  · exact isNoetherianRing_of_surjective E _ (Profinite.continuousMapConstRingHom E)
      (Profinite.continuousMapConstRingHom_surjective E)
  · exact isNoetherianRing_of_surjective (PadicAlgCl ℓ) _ (Profinite.PadicAlgCl.constRingHom ℓ)
      (Profinite.PadicAlgCl.constRingHom_surjective ℓ)

end AlgebraicGeometry.ProEtale.CondensedRing
