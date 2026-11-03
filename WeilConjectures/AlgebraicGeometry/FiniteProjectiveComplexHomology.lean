/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.InternalHomDualTorAmplitude
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import all WeilConjectures.AlgebraicGeometry.CondensedGeometricPoint.CondensedCoefficientPoint
import WeilConjectures.CategoryTheory.ModuleObjects.FreeMap
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators

/-! # Homology of condensed finite projective complexes

This is the coefficient-specific point cohomology step used by locally constant perfect duality.
-/

@[expose] public noncomputable section
set_option synthInstance.maxSize 4096
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

set_option maxHeartbeats 1200000 in
-- The scalar-point transport proof generates large categorical terms.
open CondensedGeometricPoint in
private theorem homology_of_scalar_properties
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : scalar_properties Λ)
    (F : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) ℤ)
    (hF : ∀ n : ℤ, FiniteProjectiveCondensedModule (Mon.mk Λ) (F.X n)) (q : ℤ) :
    Mod.IsFinitelyPresented Λ (F.homology q) := by
  classical
  let k := AlgebraicClosure (ULift.{u} ℚ)
  let R := condensedScalarRing Λ
  let e := ((upperStarFromPoint (Spec (.of k))).mapMod Λ).asEquivalence
  let S := CondensedRing.Evaluation.sections (coherentTopology Profinite.{u}) Λ
    (⊤_ Profinite.{u})
  let J := CondensedRing.ordinaryScalarRealization (Mon.mk Λ) (Spec (.of k))
  obtain ⟨ha, hl, hc, _⟩ := CondensedRing.flat_ordinaryScalarRealization
    (Mon.mk Λ) hΛ.2 (Spec (.of k))
  let := ha
  let := hl
  let := hc
  let L := J ⋙ e.inverse
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  have : L.Additive := inferInstanceAs (J ⋙ e.inverse).Additive
  have : PreservesFiniteLimits L := inferInstanceAs (PreservesFiniteLimits (J ⋙ e.inverse))
  have : PreservesFiniteColimits L := inferInstanceAs (PreservesFiniteColimits (J ⋙ e.inverse))
  let adj := ordinary_adjunction Λ k
  let a : L ⊣ S := (adj.comp e.symm.toAdjunction).ofNatIsoRight
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.unitIso.symm S ≪≫ Functor.leftUnitor S)
  have : IsIso a.unit := CondensedRing.Evaluation.contractible_realization_ordinary_unit
    (coherentTopology Profinite.{u}) Λ (⊤_ Profinite.{u}) terminalIsTerminal
    (singleton_sections_colimits Λ) L a
  have : L.Full := a.fullyFaithfulLOfIsIsoUnit.full
  have : L.Faithful := a.fullyFaithfulLOfIsIsoUnit.faithful
  have : PreservesColimitsOfSize.{u + 1, u + 1} S := singleton_sections_colimits Λ
  have : S.Additive := Functor.additive_of_preserves_binary_products _
  let r := condensed_regular_iso Λ L a
  have hregular : IsIso (a.counit.app (Mod.regular Λ)) :=
    a.isIso_counit_app_of_iso r.symm
  have hfree (n : ℕ) : IsIso (a.counit.app (Mod.finiteFree Λ n)) := by
    let K := Discrete.functor (fun _ : Fin n ↦ Mod.regular Λ)
    have hK : IsIso (Functor.whiskerLeft K a.counit) := by
      have (j : Discrete (Fin n)) : IsIso ((Functor.whiskerLeft K a.counit).app j) :=
        hregular
      exact NatIso.isIso_of_isIso_app _
    exact isIso_app_coconePt_of_preservesColimit K a.counit
      (biproduct.bicone (fun _ : Fin n ↦ Mod.regular Λ)).toCocone
      (biproduct.isColimit _)
  have hterm (n : ℤ) : IsIso (a.counit.app (F.X n)) := by
    obtain ⟨m, i, p, hip⟩ := hF n
    have := hfree m
    exact a.counit.isIso_app_of_retract (⟨i, p, hip⟩ : Retract _ _)
  let C := (S.mapHomologicalComplex (.up ℤ)).obj F
  let d : (L.mapHomologicalComplex (.up ℤ)).obj C ≅ F :=
    HomologicalComplex.Hom.isoOfComponents (fun n ↦ asIso (a.counit.app (F.X n)))
      (by
        intro i j hij
        change a.counit.app (F.X i) ≫ F.d i j =
          L.map (S.map (F.d i j)) ≫ a.counit.app (F.X j)
        exact (a.counit.naturality (F.d i j)).symm)
  let dh : L.obj (C.homology q) ≅ F.homology q :=
    ((L.mapHomologicalComplexHomologyIso (.up ℤ) q).app C).symm ≪≫
      (HomologicalComplex.homologyFunctor _ (.up ℤ) q).mapIso d
  let sr : S.obj (Mod.regular Λ) ≅ ModuleCat.of R R :=
    (S.mapIso r).symm ≪≫ (asIso (a.unit.app (ModuleCat.of R R))).symm
  let b (n : ℕ) : S.obj (Mod.finiteFree Λ n) ≅ ModuleCat.of R (Fin n → R) :=
    S.mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
      biproduct.mapIso (fun _ ↦ sr) ≪≫
      ModuleCat.biproductIsoPi (fun _ : Fin n ↦ ModuleCat.of R R)
  let := hΛ.1
  obtain ⟨n, i, p, hip⟩ := hF q
  let : IsSplitMono i := ⟨⟨p, hip⟩⟩
  have : Mono i := inferInstance
  have : Module.Finite R (S.obj (Mod.finiteFree Λ n)) :=
    Module.Finite.equiv (b n).toLinearEquiv.symm
  have : Module.Finite R (S.obj (F.X q)) :=
    Module.Finite.of_injective (S.map i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  have : Module.Finite R (C.X q) := inferInstanceAs (Module.Finite R (S.obj (F.X q)))
  have : Module.Finite R (C.cycles q) :=
    Module.Finite.of_injective (C.iCycles q).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  have : Module.Finite R (C.homology q) :=
    Module.Finite.of_surjective (C.homologyπ q).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  exact (scalar_models_iff Λ L r (F.homology q)).mpr
    ⟨C.homology q, inferInstance, ⟨dh⟩⟩

private theorem homology_of_coefficient_iso
    {Λ Ω : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Ω] [IsCommMonObj Ω]
    (e : Mon.mk Λ ≅ Mon.mk Ω)
    (hΩ : ∀ (C : CochainComplex
      (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Ω) ℤ),
      (∀ n : ℤ, FiniteProjectiveCondensedModule (Mon.mk Ω) (C.X n)) →
      ∀ q : ℤ, Mod.IsFinitelyPresented Ω (C.homology q))
    (F : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) ℤ)
    (hF : ∀ n : ℤ, FiniteProjectiveCondensedModule (Mon.mk Λ) (F.X n)) (q : ℤ) :
    Mod.IsFinitelyPresented Λ (F.homology q) := by
  let G : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ ⥤
      Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Ω := Mod.comap e.inv.hom
  have : G.IsEquivalence := (Mod.comapEquivalenceOfIsIso e.inv.hom).isEquivalence_functor
  let C := (G.mapHomologicalComplex (.up ℤ)).obj F
  have hC (n : ℤ) : FiniteProjectiveCondensedModule (Mon.mk Ω) (C.X n) := by
    obtain ⟨m, i, p, hip⟩ := hF n
    let r : Retract (F.X n) (Mod.finiteFree Λ m) := ⟨i, p, hip⟩
    let t := (r.map G).trans (Retract.ofIso (Mod.finiteFreeIsoComap e.inv.hom m))
    exact ⟨m, t.i, t.r, t.retract⟩
  have h := (hΩ C hC q).of_iso ((G.mapHomologicalComplexHomologyIso (.up ℤ) q).app F)
  exact h.of_comap e.inv.hom

/-- Homology of a condensed complex with finite projective terms is finitely presented for an
admissible coefficient ring. Only the three terms adjacent to the requested degree are used.
Source: internal-Hom stability proof, paragraph 3.
(blueprint: lem-sfb-condensed-finite-projective-homology).

Proof: choose finite-free retracts for the three adjacent terms and dualize the two
corresponding maps to scalar matrices. For each of the six admissible coefficient cases, the
scalar ring is Noetherian and scalar realization is exact on the finite presentations. Kernels
and cokernels of the finite matrices therefore have finite presentations. Transport the resulting
cokernel presentation through the point realization comparison. The argument also covers zero
terms and the finite-subextension algebraic-closure coefficient by descending the finitely many
matrix entries to one finite subextension before extending scalars. -/
theorem finiteProjectiveComplex_homology_finitelyPresented
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (F : CochainComplex (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) ℤ)
    (hF : ∀ n : ℤ, FiniteProjectiveCondensedModule (Mon.mk Λ) (F.X n))
    (q : ℤ) :
    Mod.IsFinitelyPresented Λ (F.homology q) := by
  classical
  open CondensedGeometricPoint in
    rcases hΛ with h | h | h | h | h | h
    · obtain ⟨A, _, _, _, _, hfin, _, ⟨e⟩⟩ := h
      let := hfin
      have hp : scalar_properties (Profinite.continuousMapRingObj.{u} A) := by
        apply continuous_scalar_properties A
        intro S
        rw [show ContinuousMap.C (α := S) (R := A) (A := A) = algebraMap A C(S, A)
          from rfl, RingHom.flat_algebraMap_iff]
        apply Module.Flat.of_linearEquiv
          (LinearEquiv.ofBijective (LocallyConstant.toContinuousMapLinearMap A) ?_).symm
        exact ⟨LocallyConstant.toContinuousMap_injective,
          fun f ↦ ⟨⟨f, (IsLocallyConstant.iff_continuous _).2 f.continuous⟩, rfl⟩⟩
      exact homology_of_coefficient_iso e
        (fun C hC q ↦ homology_of_scalar_properties _ hp C hC q) F hF q
    · obtain ⟨e⟩ := h
      have hp : scalar_properties (Profinite.continuousMapRingObj.{u} ℤ_[ℓ]) := by
        apply continuous_scalar_properties ℤ_[ℓ]
        intro S
        rw [show ContinuousMap.C (α := S) (R := ℤ_[ℓ]) (A := ℤ_[ℓ]) =
          algebraMap ℤ_[ℓ] C(S, ℤ_[ℓ]) from rfl, RingHom.flat_algebraMap_iff]
        let : Module.IsTorsionFree ℤ_[ℓ] C(S, ℤ_[ℓ]) := by
          constructor
          intro a ha f g hfg
          apply ContinuousMap.ext
          intro x
          exact ha.left (ContinuousMap.congr_fun hfg x)
        infer_instance
      exact homology_of_coefficient_iso e
        (fun C hC q ↦ homology_of_scalar_properties _ hp C hC q) F hF q
    · obtain ⟨e⟩ := h
      exact homology_of_coefficient_iso e
        (fun C hC q ↦ homology_of_scalar_properties _ (field_scalar_properties ℚ_[ℓ]) C hC q)
        F hF q
    · obtain ⟨E, ⟨e⟩⟩ := h
      exact homology_of_coefficient_iso e
        (fun C hC q ↦ homology_of_scalar_properties _ (field_scalar_properties E) C hC q)
        F hF q
    · obtain ⟨E, ⟨e⟩⟩ := h
      exact homology_of_coefficient_iso e
        (fun C hC q ↦ homology_of_scalar_properties _ (integers_scalar_properties ℓ E) C hC q)
        F hF q
    · obtain ⟨e⟩ := h
      exact homology_of_coefficient_iso e
        (fun C hC q ↦ homology_of_scalar_properties _ (algClosure_scalar_properties ℓ) C hC q)
        F hF q

end AlgebraicGeometry.ProEtale
