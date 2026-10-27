/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import Sheaf.Paper.CoefficientHeartStratificationDefs
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import all Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import Sheaf.Paper.TAdmissibleDualizableTruncations
import Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels
import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import Sheaf.Topology.SemihereditaryContinuousCoefficients
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Lisse heart closure for all-continuous algebraic-closure coefficients

Source: Hemo--Richarz--Scholbach, arXiv:2305.18131, Definition 6.1, Theorem 6.2(2),
Theorem 4.13 and the stable-subcategory observation after Definition 3.3
(blueprint: lem-sfb-continuous-qbar-lisse-heart-closure).

The coefficient ring consists of all continuous functions into the normed field.
There is no restriction to functions valued in a finite subextension and no completeness
assumption. The existing continuousCoefficientRingObj is definitionally the common-universe
specialization of continuousMapRingObjOfUniverse.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject TensorProduct

namespace AlgebraicGeometry.ProEtale

/-- The finite-constant-model equivalence and the five ambient lisse closure assertions.
Kernels and cokernels are computed in the ambient internal-module category; extension
closure quantifies over short exact sequences with arbitrary middle term.
Source: Hemo--Richarz--Scholbach, Theorem 6.2(2) and Definition 3.3
(blueprint: lem-sfb-continuous-qbar-lisse-heart-closure). -/
def ContinuousQbarLisseHeartClosure (Ω : Type u) [NormedField Ω] (T : Scheme.{u}) : Prop :=
  (∀ M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj Ω) T),
    HasFiniteConstantLocalModel (Profinite.continuousCoefficientRingObj Ω) T M ↔
      IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj Ω) M) ∧
  ObjectProperty.ContainsZero
    (IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj Ω) (X := T)) ∧
  ObjectProperty.IsClosedUnderIsomorphisms
    (IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj Ω) (X := T)) ∧
  ObjectProperty.IsClosedUnderKernels
    (IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj Ω) (X := T)) ∧
  ObjectProperty.IsClosedUnderCokernels
    (IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj Ω) (X := T)) ∧
  ObjectProperty.IsClosedUnderExtensions
    (IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj Ω) (X := T))

attribute [local irreducible] CondensedRing.upperStar finiteConstantScalarExtension

private theorem lisse_models
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (T : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))
    (hM : IsLisseCoefficientModule Λ M) : HasFiniteConstantLocalModel Λ T M := by
  classical
  obtain ⟨U, hU⟩ := hM
  apply (finiteConstantLocalModel_iff_exists_cover Λ M).mpr
  refine ⟨U, ?_⟩
  intro i
  obtain ⟨n, ⟨e⟩⟩ := hU i
  let R := scalarRingObj Λ
  refine ⟨Mod.finiteFree R n, ?_, ⟨e ≪≫ (scalarFreeIso Λ (U.X i) n).symm⟩⟩
  exact ⟨n, n, 0, ⟨(cokernelZeroIsoTarget (X := Mod.finiteFree R n)
    (Y := Mod.finiteFree R n)).symm⟩⟩

private theorem models_iff_lisse (Ω : Type u) [NormedField Ω] (T : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj Ω) T)) :
    HasFiniteConstantLocalModel (Profinite.continuousCoefficientRingObj Ω) T M ↔
      IsLisseCoefficientModule (Profinite.continuousCoefficientRingObj Ω) M := by
  constructor
  · exact models_free_cover _ M (scalarField_finitelyPresented_isFree Ω)
  · exact lisse_models _ T M

private theorem continuous_tAdmissible (Ω : Type u) [NormedField Ω] :
    CondensedRing.IsTAdmissible (Mon.mk (Profinite.continuousCoefficientRingObj Ω)) := by
  have h := Profinite.semihereditary_continuous_coefficients_admissible.{u, u} Ω
    (fun I _ ↦ inferInstance)
  exact h.2.2.2.2

open CategoryTheory.Pretriangulated in
private theorem single_heart_closed
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (P : ObjectProperty (DerivedCategory C)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms] (F : ObjectProperty C)
    (hF : ∀ M, P ((DerivedCategory.singleFunctor C 0).obj M) ↔ F M)
    (htr : ∀ K, P K → ∀ n : ℤ,
      P ((DerivedCategory.TStructure.t.truncLE n).obj K) ∧
      P ((DerivedCategory.TStructure.t.truncGE n).obj K)) :
    F.ContainsZero ∧ F.IsClosedUnderIsomorphisms ∧ F.IsClosedUnderKernels ∧
      F.IsClosedUnderCokernels ∧ F.IsClosedUnderExtensions := by
  let t := DerivedCategory.TStructure.t (C := C)
  let S := DerivedCategory.singleFunctor C 0
  let : t.Heart C :=
    { ι := S
      essImage_eq_heart := by
        ext K
        constructor
        · rintro ⟨M, ⟨e⟩⟩
          exact t.heart.prop_of_iso e (by
            rw [t.mem_heart_iff]
            constructor <;> infer_instance)
        · intro hK
          have : K.IsLE 0 := ⟨hK.1⟩
          have : K.IsGE 0 := ⟨hK.2⟩
          obtain ⟨M, ⟨e⟩⟩ := K.exists_iso_singleFunctor_obj_of_isGE_of_isLE 0
          exact ⟨M, ⟨e.symm⟩⟩ }
  have hI : F.IsClosedUnderIsomorphisms := ⟨fun e h ↦
    (hF _).mp (P.prop_of_iso (S.mapIso e) ((hF _).mpr h))⟩
  have : F.IsClosedUnderIsomorphisms := hI
  refine ⟨?_, hI, ?_, ?_, ?_⟩
  · exact ⟨0, isZero_zero C, (hF _).mp (P.prop_of_isZero
      (S.map_isZero (isZero_zero C)))⟩
  · constructor
    rintro _ ⟨f, k, hk, hf⟩
    obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle (S.map f)
    have hZ : P Z := P.ext_of_isTriangulatedClosed₃ _ hT
      ((hF _).mpr hf.1) ((hF _).mpr hf.2)
    obtain ⟨K, i, hi, hK, e, he⟩ :=
      t.exists_isLimit_kernelFork_of_distTriang f g δ hT
    have hp : P (S.obj K) := P.prop_of_iso
      ((shiftFunctorCompIsoId (DerivedCategory C) 1 (-1) (by omega)).app _)
      (P.le_shift (-1) _ (P.prop_of_iso e.symm (htr _ hZ (-1)).1))
    exact F.prop_of_iso (hK.conePointUniqueUpToIso hk) ((hF _).mp hp)
  · constructor
    rintro _ ⟨f, k, hk, hf⟩
    obtain ⟨Z, g, δ, hT⟩ := distinguished_cocone_triangle (S.map f)
    have hZ : P Z := P.ext_of_isTriangulatedClosed₃ _ hT
      ((hF _).mpr hf.1) ((hF _).mpr hf.2)
    obtain ⟨Q, p, hp, hQ, e, he⟩ :=
      t.exists_isColimit_cokernelCofork_of_distTriang f g δ hT
    exact F.prop_of_iso (hQ.coconePointUniqueUpToIso hk)
      ((hF _).mp (P.prop_of_iso e.symm (htr _ hZ 0).2))
  · constructor
    intro E hE h₁ h₃
    exact (hF _).mp (P.ext_of_isTriangulatedClosed₂ hE.singleTriangle
      hE.singleTriangle_distinguished ((hF _).mpr h₁) ((hF _).mpr h₃))

/-- All finite constant local models are lisse, and lisse modules form a class containing
zero and closed under isomorphisms, ambient kernels, ambient cokernels and extensions.
The normed algebra structure specifies the extension of the ell-adic norm to Ω.
Source: Hemo--Richarz--Scholbach, Definition 6.1, Theorems 4.13 and 6.2(2), and the
stable-subcategory observation after Definition 3.3
(blueprint: lem-sfb-continuous-qbar-lisse-heart-closure).

Proof, following the node's field specialization and heart argument:
1. The existing scalar-model comparison identifies a finite constant local model with
local scalar extension of a finitely presented module. Such a scalar module is finite
free over the field. Conversely a finite free scalar module extends to a finite free
coefficient module, on the same cover and including rank zero.
2. Every ideal of the field is projective. Apply the existing semihereditary continuous
coefficient theorem to obtain t-admissibility. No completeness or restriction to a finite
coefficient field is needed. Noetherian spaces have finitely many irreducible components.
3. Apply the t-admissible truncation theorem directly in the internal-module derived
category. Its degree-zero heart criterion and step 1 identify dualizable objects of the
standard heart with lisse modules.
4. Dualizable complexes form a triangulated class stable under standard truncations.
For a map of heart objects with cone Z, its ambient kernel shifted by one is the
nonpositive truncation of Z at -1, and its ambient cokernel is the nonnegative truncation
at 0. Truncation, shift and isomorphism stability imply both are lisse. Uniqueness of
limiting forks and colimiting coforks covers every ambient choice. The degree-zero
inclusion preserves zero and isomorphisms, giving those two closure clauses.
5. A short exact sequence gives a distinguished triangle of degree-zero complexes.
Triangulated extension closure puts its arbitrary middle object in the dualizable class,
so the heart criterion makes that module lisse. -/
theorem continuousQbar_lisse_heart_closure (ℓ : ℕ) [Fact ℓ.Prime]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    (T : Scheme.{u}) [TopologicalSpace.NoetherianSpace T] :
    ContinuousQbarLisseHeartClosure Ω T := by
  let Λ := Mon.mk (Profinite.continuousCoefficientRingObj Ω)
  let P := CondensedRing.dualizableProperty Λ T
  have hcomponents : CondensedRing.HasLocallyFiniteIrreducibleComponents T := by
    intro x
    let U : T.Opens := ⊤
    have : TopologicalSpace.NoetherianSpace U :=
      U.ι.isOpenEmbedding.isInducing.noetherianSpace
    exact ⟨U, by trivial, TopologicalSpace.NoetherianSpace.finite_irreducibleComponents⟩
  obtain ⟨htr, ⟨hP, ht⟩, hheart, hcohom⟩ :=
    CondensedRing.tAdmissible_dualizable_truncations Λ (continuous_tAdmissible Ω) T hcomponents
  have : P.IsTriangulated := hP
  have : P.IsClosedUnderIsomorphisms := by
    obtain ⟨hz, hi, hs, hc⟩ := condensed_dualizable_stable Λ.X T
    exact ⟨fun e h ↦ hi _ _ ⟨e⟩ h⟩
  have hF M : P ((DerivedCategory.singleFunctor _ 0).obj M) ↔
      IsLisseCoefficientModule Λ.X M :=
    (hheart M).trans ((finiteConstantLocalModel_iff_exists_cover Λ.X M).symm.trans
      (models_iff_lisse Ω T M))
  exact ⟨models_iff_lisse Ω T,
    single_heart_closed P (IsLisseCoefficientModule Λ.X) hF htr⟩

/-- The same assertions apply on every locally closed subscheme of a Noetherian scheme.
Source: Hemo--Richarz--Scholbach, Theorem 6.2(2), applied to a locally closed subspace
(blueprint: lem-sfb-continuous-qbar-lisse-heart-closure).

Proof plan, step 6 of the node: a locally Noetherian quasi-compact scheme has a
Noetherian underlying space by lem-weil-pbc-noetherian-scheme-closed-subsets-minimal
(applied to descending closed chains). An immersion identifies its source with a
subspace. Every subspace is Noetherian: close a descending chain in the ambient space,
use stabilization there, and intersect back with the subspace. Apply
continuousQbar_lisse_heart_closure with the same all-continuous coefficients. The empty
subscheme is included. -/
theorem continuousQbar_lisse_heart_closure_of_immersion (ℓ : ℕ) [Fact ℓ.Prime]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ℓ] Ω] [IsAlgClosure ℚ_[ℓ] Ω]
    {T X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (i : T ⟶ X) [IsImmersion i] :
    ContinuousQbarLisseHeartClosure Ω T := by
  have : IsNoetherian X := ⟨⟩
  have : TopologicalSpace.NoetherianSpace T := i.isEmbedding.isInducing.noetherianSpace
  exact continuousQbar_lisse_heart_closure ℓ Ω T

end AlgebraicGeometry.ProEtale
