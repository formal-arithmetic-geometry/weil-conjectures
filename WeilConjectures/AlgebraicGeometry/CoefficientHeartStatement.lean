/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartFiltration
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSmall
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartClosure

/-!
# Constructible coefficient sheaves

Source: blueprint latest,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/_section.md`,
clauses (1)--(3) (blueprint: sk-lem-coefficient-heart).

The coefficient ring is the condensed ring pulled back from the point.  The statement
uses the existing constructible full subcategory, the existing lisse predicate, and the
canonical locally closed extension from the dependency nodes.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- Finite free local charts give finite constant presentations, including rank zero. -/
private lemma statementHeart_free_model
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : IsLisseCoefficientModule Λ M) : HasFiniteConstantLocalModel Λ Y M := by
  open MonoidalCategory MonObj Functor.LaxMonoidal Functor.OplaxMonoidal in
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
  exact ⟨Mod.finiteFree Λ n, ⟨n, n, 0, ⟨cokernelZeroIsoTarget.symm⟩⟩, ⟨e ≪≫ en.symm⟩⟩

/-- Keep the counit image abstract while assembling its finite filtration. -/
private def statementHeart_filtrationImage
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (V : Y.Opens) : Subobject M :=
  imageSubobject (coefficientHeartOpenCounit Λ M V)

private theorem statementHeart_filtrationImage_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Y : Scheme.{u}}
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (V : Y.Opens) :
    statementHeart_filtrationImage Λ M V = coefficientHeartFiltrationStep Λ M V := rfl

/-- Constructible coefficient sheaves form an exact essentially small abelian heart and
admit finite filtrations by canonical locally closed extensions of lisse sheaves.

Source: blueprint latest,
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/_section.md`,
clauses (1)--(3), and
`part-six-operations/sec-reduction-finite-coefficients/`
`sec-constructible-sheaves-with-field-coefficients/sk-lem-coefficient-heart/`
`sk-lem-coefficient-heart.proof.md`,
steps (1)--(3)
(blueprint: lem-sfb-coefficient-heart-positive-characteristic-special-case).

The closure conjuncts render clause (1)'s closure under kernels, cokernels and extensions.
The `Abelian` witness and finite-limit/finite-colimit preservation render its abelian and
exact-inclusion conclusions.  The `EssentiallySmall` conjunct is clause (2).  The final
conjunct is clause (3): its filtration terms are subobjects, successive quotients are
cokernels of the inclusions, and each quotient is the canonical `a_!` of a lisse module.

Proof:
1. Build the Noetherian instance from finite type and quasi-compactness.
2. Apply the existing coefficientHeart_closure theorem for kernel/cokernel/extension
   closure, abelianity, exact inclusion and finite lisse stratifications. Apply the
   existing coefficientHeart_essentiallySmall theorem for the fixed-universe conclusion.
3. Convert lisse charts to finite constant models: pullback preserves finite biproducts
   of the regular module, and the finite free scalar module has a zero-map presentation.
   Refine one adapted stratification to one with ordered open prefixes.
4. Apply coefficientHeart_filtration and assemble its bottom/top image subobjects,
   successive inclusions, and cokernel isomorphisms with the lisse quotient witnesses.
   Rank zero, repeated terms and empty filtrations are included.

This proves the existing positive-characteristic tool interface. It does not certify the
separate current blueprint unit's finite-or-algebraically-closed-field statement or its
pending lattice/tower route repair.
-/
theorem coefficientHeartStatement (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) RingCat.{u + 1})
    [IsCommMonObj (coefficientHeartRingObj Λ)]
    (hΛ : (∃ E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ),
      FiniteDimensional ℚ_[ℓ] E ∧ Λ = Profinite.padicSubfieldCondensedRing ℓ E) ∨
      Λ = Profinite.padicAlgClCondensedRing ℓ)
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    ObjectProperty.IsClosedUnderKernels
        (IsConstantModelConstructible (coefficientHeartRingObj Λ) X) ∧
      ObjectProperty.IsClosedUnderCokernels
        (IsConstantModelConstructible (coefficientHeartRingObj Λ) X) ∧
      ObjectProperty.IsClosedUnderExtensions
        (IsConstantModelConstructible (coefficientHeartRingObj Λ) X) ∧
      Nonempty (Abelian (ConstantModelConstructible (coefficientHeartRingObj Λ) X)) ∧
      PreservesFiniteLimits
        (ObjectProperty.ι (IsConstantModelConstructible
          (coefficientHeartRingObj Λ) X)) ∧
      PreservesFiniteColimits
        (ObjectProperty.ι (IsConstantModelConstructible
          (coefficientHeartRingObj Λ) X)) ∧
      EssentiallySmall.{u + 1} (ConstantModelConstructible (coefficientHeartRingObj Λ) X) ∧
      @CoefficientHeartFiltrationAssertions (coefficientHeartRingObj Λ) _ _ X
        { toIsLocallyNoetherian :=
            LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
          toCompactSpace :=
            QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) } := by
  classical
  have _characteristic_separation := hpℓ
  have : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k)) }
  have hclosure := (coefficientHeart_closure ℓ Λ hΛ).2 X
  refine ⟨hclosure.1, hclosure.2.1, hclosure.2.2.1, hclosure.2.2.2.1,
    hclosure.2.2.2.2.1, hclosure.2.2.2.2.2.1,
    coefficientHeart_essentiallySmall ℓ Λ hΛ X, ?_⟩
  intro F
  obtain ⟨S, hS⟩ := (hclosure.2.2.2.2.2.2 F.obj).mp F.property
  have hcommon := coefficientHeart_commonStratification ℓ Λ X hΛ
  obtain ⟨R, hR, _, hopen⟩ := hcommon.1 1 (fun _ ↦ S)
  have hRfree := hcommon.2.1.2 S R F.obj
    (fun a ↦ statementHeart_free_model (coefficientHeartRingObj Λ) _ (hS a)) (hR 0)
  let V (a : Fin (R.n + 1)) : X.Opens := ⟨_, hopen a⟩
  have hfil := coefficientHeart_filtration ℓ Λ hΛ X F.obj F.property R
    (fun a ↦ statementHeart_free_model (coefficientHeartRingObj Λ) _ (hRfree a))
    V (fun _ ↦ rfl)
  simp only [← statementHeart_filtrationImage_eq] at hfil
  obtain ⟨h, hquot⟩ := hfil.2.2.2
  refine ⟨R.n, fun a ↦ statementHeart_filtrationImage (coefficientHeartRingObj Λ) F.obj (V a),
    hfil.2.1, hfil.2.2.1, h, fun a ↦ ?_⟩
  exact ⟨R.domain a, R.immersion a, R.isImmersion a,
    (CondensedRing.upperStar (coefficientHeartRingObj Λ) (R.immersion a)).obj F.obj,
    (hquot a).2, (hquot a).1⟩

end AlgebraicGeometry.ProEtale
