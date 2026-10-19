/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.ConstructibleHomContinuityDevissage
import Sheaf.Paper.IntegralLfpHomContinuity
import Sheaf.Paper.CondensedLocallyClosedExtensionTower
import all Sheaf.Paper.CondensedLocalPieceHomContinuity
import all Sheaf.Paper.CoefficientHeartLisseRestriction
import all Sheaf.Paper.ConstructibleExtContinuity
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Continuity of Ext out of integral constructible complexes

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-int-ext/
sk-lem-int-ext-continuity.md,
node det-lem-int-ext-continuity (blueprint: det-lem-int-ext-continuity).

The constructible category is `Dbc(X, 𝒪_E)` of sk-def-sfb-constructible (finite constant
scalar models), and the comparison is the canonical map `homContinuityComparison` of
det-lem-constructible-ext-continuity-devissage, built from the termwise colimit cocone.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj ZeroObject

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {ℓ : ℕ} {k : Type u} {E : Type} [Field k] [Field E]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [Fact ℓ.Prime] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 150000 in
-- Bounded devissage and dependent coefficient comparisons require extra elaboration.
omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- Ext out of an integral constructible complex commutes with a bounded-below filtered
termwise colimit: for `C ∈ Dbc(X, 𝒪_E)` and every `q`, the canonical map
`colim_i Hom(C, K_i[q]) ⟶ Hom(C, K[q])` induced by the colimit cocone is an isomorphism of
abelian groups.
Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-int-ext/
sk-lem-int-ext-continuity (blueprint: det-lem-int-ext-continuity).

Proof:
1. Equip E with the norm induced by its embedding into the algebraic closure. The norm
extends the ℓ-adic norm, so the continuous integral coefficients agree with the given
condensed valuation-ring coefficients.
2. Finite type over the field and quasi-compactness make X Noetherian. For the fixed
bounded-below diagram, constructibleHomContinuity_devissage makes the comparison locus
closed under shifts, isomorphisms and distinguished extensions.
3. A constant-model constructible sheaf has a finite stratification by constant models.
Each model is locally finitely presented by constantModel_lfp; the normalized pullback
isomorphism transports this to the constructible-module predicate. The existing
exists_condensedLocallyClosed_extension_tower gives a finite extension tower of pieces.
4. For each piece i_*j_!L, locally_closed_generators_continuity transports the canonical
Hom cocone through the closed-costalk and open adjunctions to a uniformly bounded-below
diagram on the stratum. Its proof uses the closed-support fibre triangle and continuity
of the complementary open direct image. Apply integral_lfp_hom_continuity there: the
length-one locally finite free resolution reduces the assertion to finite free
coefficients and bounded sections continuity. This computes the same finite-amplitude
dual calculation without constructing its internal-Hom object in the present module.
5. Finite extension closure gives continuity for every constructible sheaf in degree
zero. The zero sheaf also has a finite constant model, so the comparison locus is a
triangulated subcategory. DerivedCategory.prop_of_bounded applies truncation dévissage
to C using its boundedness and constructible cohomology. Convert bijectivity of the
comparison in degree q to its being an isomorphism of abelian groups. -/
theorem integralExtHomContinuous
    {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (C : DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)))
    (hC : constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X.left C)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (K : I ⥤ CochainComplex
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)) ℤ)
    [HasColimit K]
    (b : ℤ) (hK : ∀ i : I, ∀ r : ℤ, r < b → IsZero ((K.obj i).X r)) (q : ℤ) :
    IsIso (homContinuityComparison (K ⋙ DerivedCategory.Q)
      (DerivedCategory.Q.mapCocone (colimit.cocone K)) C q) := by
  classical
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  let : NormedAlgebra ℚ_[ℓ] E :=
    { norm_smul_le c x := by
        change ‖algebraMap E (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  let Λ := Profinite.padicIntegersRingObj.{u} ℓ E
  have : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : IsNoetherian X.left := ⟨⟩
  let A := Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
    (condensedRingObj Λ X.left)
  let P : ObjectProperty A := IsConstantModelConstructible Λ X.left
  let Q : ObjectProperty (DerivedCategory A) := complexHomContinuityLocus A K
  obtain ⟨hs, hi, he, _⟩ := constructibleHomContinuity_devissage Λ X.left K
  let : Q.IsClosedUnderIsomorphisms := ⟨fun e h ↦ hi _ _ e h⟩
  let : Q.IsStableUnderShift ℤ :=
    { isStableUnderShiftBy := fun n ↦ ⟨fun C h ↦ hs C n h⟩ }
  let : Q.IsTriangulatedClosed₂ := .mk' he
  let : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦ constant_model_of_iso Λ e h⟩
  have hsingle (M : A) (hM : P M) : Q ((DerivedCategory.singleFunctor A 0).obj M) := by
    have hstr : IsFiniteConstantStratified Λ X.left M := by
      simpa only [P, IsConstantModelConstructible, if_pos (show
        CompactSpace X.left ∧ QuasiSeparatedSpace X.left from ⟨inferInstance, inferInstance⟩)]
        using hM
    obtain ⟨S, hS⟩ := hstr
    have hM' : IsConstructibleModuleObject (condensedRingObj Λ X.left) M := by
      refine ⟨S, fun a ↦ ?_⟩
      have h := constantModel_lfp Λ (S.domain a) _ (hS a)
      exact lfp_of_comap (inv (condensedPullbackHom Λ (S.immersion a)))
        (lfp_of_iso h ((normalizedPullbackIso Λ (S.immersion a)).app M))
    obtain ⟨r, hr⟩ := exists_condensedLocallyClosed_extension_tower X.left Λ M hM'
    have hpieces : condensedLocallyClosedPiece Λ X.left ≤
        homColimitProperty (K ⋙ DerivedCategory.Q)
          (DerivedCategory.Q.mapCocone (colimit.cocone K)) := by
      apply locally_closed_generators_continuity X.left Λ K ⟨b, hK⟩
      intro U _ L hL N hN n
      have hc : continuousIntegers ℓ E = (PadicAlgCl.integers ℓ E).toSubring := rfl
      -- Normalize the scalar abbreviation before elaborating the dependent arguments.
      have hh := integral_lfp_hom_continuity U ℓ E
      simp only [integralCoeff] at hh
      clear hc
      exact hh L hL N hN n
    have hQpieces : condensedLocallyClosedPiece Λ X.left ≤ Q := by
      intro D hD n
      exact (ConcreteCategory.isIso_iff_bijective _).mp (hpieces D hD n)
    exact (condensedLocallyClosedPiece Λ X.left
      ).extensionProductIter_le_of_isTriangulatedClosed₂ hQpieces r _ hr
  let : Q.ContainsZero :=
    ⟨(DerivedCategory.singleFunctor A 0).obj 0,
      (DerivedCategory.singleFunctor A 0).map_isZero (isZero_zero A),
      hsingle 0 (constant_model_of_isZero Λ X.left 0 (isZero_zero A))⟩
  let : Q.IsTriangulated := {}
  have hCQ : Q C := DerivedCategory.prop_of_bounded Q P hsingle C hC.1 hC.2
  exact (ConcreteCategory.isIso_iff_bijective _).mpr (hCQ q)

end AlgebraicGeometry.ProEtale.CondensedRing
