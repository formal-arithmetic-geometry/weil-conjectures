/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import all Sheaf.AlgebraicGeometry.CondensedConstructibleSerre
import Sheaf.AlgebraicGeometry.FiniteConstantLocalModel
import Sheaf.CategoryTheory.SheafTensor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# Comparison of the two bounded constructibility predicates

Source: the finite coefficient comparison used in the proof of
`det-lem-coefficient-finite-descent-objects`
(blueprint: det-lem-coefficient-finite-descent-objects).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open MonoidalCategory MonObj Functor.LaxMonoidal Functor.OplaxMonoidal in
private lemma free_hasConstantModel
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
      Mod.IsFree (condensedRingObj Λ (U.X i)) ((CondensedRing.upperStar Λ (U.f i)).obj M)) :
    HasFiniteConstantLocalModel Λ Y M := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨n, ⟨e⟩⟩ := hU i
  have : PreservesFiniteColimits (upperStarFromPoint (U.X i)) := by
    let : pointUpperStar.{u}.IsLeftAdjoint := pointUpperStarLowerStarAdjunction.isLeftAdjoint
    unfold upperStarFromPoint
    infer_instance
  let F := (upperStarFromPoint (U.X i)).mapMod Λ
  have : PreservesFiniteColimits F := inferInstance
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  have : PreservesFiniteBiproducts F := inferInstance
  let en : F.obj (Mod.finiteFree Λ n) ≅ Mod.finiteFree (condensedRingObj Λ (U.X i)) n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular Λ) ≪≫
      biproduct.mapIso (fun _ ↦ Mod.isoMk (Iso.refl _) (by simp [Mod.act]))
  refine ⟨Mod.finiteFree Λ n, ⟨n, n, 0, ⟨cokernelZeroIsoTarget.symm⟩⟩, ⟨e ≪≫ en.symm⟩⟩

open MonoidalCategory MonObj in
private lemma constantModel_eq_of_localFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hLF : ∀ (Y : Scheme.{u}) [TopologicalSpace.NoetherianSpace Y]
      (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)),
      IsLocallyFinitelyPresented (condensedRingObj Λ Y) M →
      ∃ U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y, ∀ i,
        Mod.IsFree ((upperStar Ab.{u + 1} (U.f i)).obj (condensedRingObj Λ Y))
          (((upperStar Ab.{u + 1} (U.f i)).mapMod (condensedRingObj Λ Y)).obj M))
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    [TopologicalSpace.NoetherianSpace X] :
    constantModelBoundedConstructible Λ X = boundedConstructible (condensedRingObj Λ X) := by
  have hmod (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :
      IsConstantModelConstructible Λ X M ↔
        IsConstructibleModuleObject (condensedRingObj Λ X) M := by
    rw [IsConstantModelConstructible, if_pos ⟨inferInstance, inferInstance⟩]
    constructor
    · rintro ⟨S, hS⟩
      refine ⟨S, fun a ↦ ?_⟩
      let φ := condensedPullbackHom Λ (S.immersion a)
      have h := (hS a).isLocallyFinitelyPresented _
      exact lfp_of_comap (inv φ)
        (lfp_of_iso h ((Mod.extendScalarsIsoComapInv φ).app _))
    · rintro ⟨S, hS⟩
      refine ⟨S, fun a ↦ ?_⟩
      have : TopologicalSpace.NoetherianSpace (S.domain a) :=
        (S.immersion a).isEmbedding.isInducing.noetherianSpace
      let φ := condensedPullbackHom Λ (S.immersion a)
      have h := lfp_of_iso (lfp_comap (inv φ) (hS a))
        ((Mod.extendScalarsIsoComapInv φ).app _).symm
      obtain ⟨U, hU⟩ := hLF _ _ h
      apply free_hasConstantModel Λ _
      refine ⟨U, fun i ↦ ?_⟩
      let ψ := condensedPullbackHom Λ (U.f i)
      exact free_of_iso (free_comap (inv ψ) (hU i))
        ((Mod.extendScalarsIsoComapInv ψ).app _).symm
  funext K
  apply propext
  exact and_congr_right fun _ ↦ forall_congr' fun n ↦ hmod _

/-- For the coefficient fields occurring in finite descent, the finite-constant-model
predicate agrees with stratified local finite presentation on bounded cohomology.

Source: blueprint main-20261015, finite coefficient descent, the Sheaves and Complexes
paragraphs; Bhatt--Scholze, Section 6.8, as formalized by the finite-field and algebraic-closure
local-freeness theorems. (blueprint: lem-coefficient-finite-descent-predicate-comparison).

Proof: finite type over a field makes X Noetherian, hence qcqs. Finite constant local models
are locally finitely presented. Conversely, each locally closed stratum is topologically
Noetherian, so the coefficient-specific local-freeness theorem trivializes a locally finitely
presented module on a pro-etale cover. A free module of rank n is the inverse image of the
regular condensed coefficient module to the nth power. This condensed module has the finite
presentation given by the zero map from rank n to rank n. Inverse image preserves finite sums,
so these are finite constant local models. Transport through the invertible coefficient
pullback map identifies both conventions for restriction to every stratum and cover member.
The same finite stratification witnesses both notions. Applying the resulting equivalence to
every cohomology object and retaining the identical boundedness condition proves equality of
the two predicates. Empty strata and rank zero are included. -/
theorem constantModelBoundedConstructible_eq_boundedConstructible
    (k : Type u) [Field k] (p ℓ : ℕ) [CharP k p] [Fact ℓ.Prime]
    (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X =
        boundedConstructible (padicAlgClRingObj X ℓ) ∧
      ∀ E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ),
        constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X =
          boundedConstructible (padicSubfieldRingObj X ℓ E) := by
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType (X ↘ Spec (.of k))
  exact ⟨constantModel_eq_of_localFree _ (algcl_lf ℓ) X,
    fun E ↦ constantModel_eq_of_localFree _ (finite_lf ℓ E) X⟩

end AlgebraicGeometry.ProEtale
