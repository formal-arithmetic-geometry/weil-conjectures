/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.Paper.CompletedScalarShift
public import Sheaf.Paper.CompletedLineTensorCoherence
public import Sheaf.Paper.CompletedScalarChainShift
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
import Sheaf.Paper.ScalarCompletionAssociator
import Sheaf.Paper.CompletedScalarShiftDescent
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Canonical scalar shifts transport coherent towers

Source: blueprint `sk-thm-purity-transport`, coefficient-change argument;
Stacks Tags 011G, 014E, 06YY, 0G7D and 0D6D.
(blueprint: lem-pur-scalar-shift-line-tower-transport).

The auxiliary records bundle this node's shift comparisons and equations. The
ordinary normalization uses the identity-component termwise tensor shift, and
the strict normalization uses the actual quotient map with zero second coordinate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b c d
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures

/-- The three normalized shifts for one coefficient inclusion. The representative
property fixes the termwise identity comparison, the signed product coordinates,
the descent square and compatibility with the actual quotient-completion map.
Source: Stacks 011G, 014E, 06YY; blueprint coefficient transport
(blueprint: lem-pur-scalar-shift-line-tower-transport). -/
structure ScalarShiftLineData (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (W : AlgebraicGeometry.Scheme.{t}) where
  /-- The strict chain shift. -/
  chain : (integralScalarComplexFunctor l E L ι W).CommShift ℤ
  /-- The ordinary derived tensor shift, natural on all derived morphisms. -/
  ordinary : (completedDerivedScalarExtension l E L ι W).CommShift ℤ
  /-- The strict-tower derived shift, natural on all derived morphisms. -/
  integral : (integralScalarExtensionOfUniverses l E L ι W).CommShift ℤ
  /-- The existing complete representative normalization, including the cone signs. -/
  normalized : completedScalarShiftRepresentativeProperty ι W chain ordinary integral

/-- The map q = w[n] after the specified scalar shift. This also defines the completed
map r when w is replaced by chi inverse followed by w. All inverses are derived ones.
Source: blueprint coefficient-transport calculation
(blueprint: lem-pur-scalar-shift-line-tower-transport). -/
def scalarShiftTowerMap {A : Type a} [Category.{b} A] [HasShift A ℤ]
    {B : Type c} [Category.{d} B] [HasShift B ℤ]
    (F : A ⥤ B) (e : F.CommShift ℤ) {K : A} {L : B} (w : F.obj K ≅ L) (n : ℤ) :
    F.obj (K⟦n⟧) ≅ L⟦n⟧ :=
  (Functor.commShiftIso F (self := e) n).app K ≪≫ (shiftFunctor B n).mapIso w

/-- All equations of the scalar-shift tower assertion, with the published normalized
ordinary associator and its actual quotient-completion conjugate. No rank assumption
is made on the objects. Every integer shift and repeated coefficient field is allowed.
Source: blueprint coefficient transport; Stacks 011G, 014E and 0D6D
(blueprint: lem-pur-scalar-shift-line-tower-transport). -/
structure ScalarShiftLineTowerTransportData (l : ℕ) [Fact l.Prime]
    (W : AlgebraicGeometry.Scheme.{t}) where
  /-- The same normalized comparisons for every coefficient inclusion. -/
  comparison : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L), ScalarShiftLineData l E L ι W
  /-- Completeness is stable under every integer shift. -/
  shift_complete : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (K : DerivedCategory (integralTowerModules l E W)) (n : ℤ),
    IsDerivedCompleteUnrestricted l E W K → IsDerivedCompleteUnrestricted l E W (K⟦n⟧)
  /-- The ordinary shift/associator square, on arbitrary derived objects. -/
  associator_shift : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (ι : E →ₐ[ℚ_[l]] L) (κ : L →ₐ[ℚ_[l]] M)
    (K : DerivedCategory (integralTowerModules l E W)) (n : ℤ),
    (CompletedLineTensor.associatorData l E W L ι M κ).derived.hom.app (K⟦n⟧) ≫
      (Functor.commShiftIso (completedDerivedScalarExtension l E M (κ.comp ι) W)
        (self := (comparison E M (κ.comp ι)).ordinary) n).hom.app K =
    (completedDerivedScalarExtension l L M κ W).map
        ((Functor.commShiftIso (completedDerivedScalarExtension l E L ι W)
          (self := (comparison E L ι).ordinary) n).hom.app K) ≫
      (Functor.commShiftIso (completedDerivedScalarExtension l L M κ W)
        (self := (comparison L M κ).ordinary) n).hom.app
          ((completedDerivedScalarExtension l E L ι W).obj K) ≫
      ((CompletedLineTensor.associatorData l E W L ι M κ).derived.hom.app K)⟦n⟧'
  /-- The shifted maps q of every coherent ordinary tower remain coherent. -/
  ordinary_tower : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (ι : E →ₐ[ℚ_[l]] L) (κ : L →ₐ[ℚ_[l]] M)
    (K₀ : DerivedCategory (integralTowerModules l E W))
    (K₁ : DerivedCategory (integralTowerModules l L W))
    (K₂ : DerivedCategory (integralTowerModules l M W))
    (w₁₀ : (completedDerivedScalarExtension l E L ι W).obj K₀ ≅ K₁)
    (w₂₁ : (completedDerivedScalarExtension l L M κ W).obj K₁ ≅ K₂)
    (w₂₀ : (completedDerivedScalarExtension l E M (κ.comp ι) W).obj K₀ ≅ K₂)
    (n : ℤ),
    (CompletedLineTensor.associatorData l E W L ι M κ).derived.hom.app K₀ ≫ w₂₀.hom =
        (completedDerivedScalarExtension l L M κ W).map w₁₀.hom ≫ w₂₁.hom →
    (CompletedLineTensor.associatorData l E W L ι M κ).derived.hom.app (K₀⟦n⟧) ≫
        (scalarShiftTowerMap _ (comparison E M (κ.comp ι)).ordinary w₂₀ n).hom =
      (completedDerivedScalarExtension l L M κ W).map
          (scalarShiftTowerMap _ (comparison E L ι).ordinary w₁₀ n).hom ≫
        (scalarShiftTowerMap _ (comparison L M κ).ordinary w₂₁ n).hom
  /-- The identical tower equation after conjugating by the actual chi isomorphisms. -/
  completed_tower : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (ι : E →ₐ[ℚ_[l]] L) (κ : L →ₐ[ℚ_[l]] M)
    (K₀ : DerivedCategory (integralTowerModules l E W))
    (K₁ : DerivedCategory (integralTowerModules l L W))
    (K₂ : DerivedCategory (integralTowerModules l M W))
    (h₀ : IsDerivedCompleteUnrestricted l E W K₀)
    (h₁ : IsDerivedCompleteUnrestricted l L W K₁)
    (_h₂ : IsDerivedCompleteUnrestricted l M W K₂)
    (w₁₀ : (completedDerivedScalarExtension l E L ι W).obj K₀ ≅ K₁)
    (w₂₁ : (completedDerivedScalarExtension l L M κ W).obj K₁ ≅ K₂)
    (w₂₀ : (completedDerivedScalarExtension l E M (κ.comp ι) W).obj K₀ ≅ K₂)
    (n : ℤ),
    (CompletedLineTensor.associatorData l E W L ι M κ).derived.hom.app K₀ ≫ w₂₀.hom =
        (completedDerivedScalarExtension l L M κ W).map w₁₀.hom ≫ w₂₁.hom →
    (CompletedLineTensor.associator l E W L ι M κ (K₀⟦n⟧)
        (shift_complete E K₀ n h₀)).hom ≫
      (scalarShiftTowerMap _ (comparison E M (κ.comp ι)).integral
        ((CompletedLineTensor.chi l E W M (κ.comp ι) K₀ h₀).symm ≪≫ w₂₀) n).hom =
    (integralScalarExtensionOfUniverses l L M κ W).map
        (scalarShiftTowerMap _ (comparison E L ι).integral
          ((CompletedLineTensor.chi l E W L ι K₀ h₀).symm ≪≫ w₁₀) n).hom ≫
      (scalarShiftTowerMap _ (comparison L M κ).integral
        ((CompletedLineTensor.chi l L W M κ K₁ h₁).symm ≪≫ w₂₁) n).hom
  /-- Identity coefficient extensions commute with shift via tensor multiplication. -/
  ordinary_unit : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (K : DerivedCategory (integralTowerModules l E W)) (n : ℤ),
    (Functor.commShiftIso
        (completedDerivedScalarExtension l E E (AlgHom.id ℚ_[l] E) W)
        (self := (comparison E E (AlgHom.id ℚ_[l] E)).ordinary) n).hom.app K ≫
      ((CompletedLineTensor.ordinaryUnit l E W).hom.app K)⟦n⟧' =
    (CompletedLineTensor.ordinaryUnit l E W).hom.app (K⟦n⟧)
  /-- The completed identity comparison is the inverse completeness unit. -/
  completed_unit : ∀
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (K : DerivedCategory (integralTowerModules l E W))
    (hK : IsDerivedCompleteUnrestricted l E W K) (n : ℤ),
    (Functor.commShiftIso
        (integralScalarExtensionOfUniverses l E E (AlgHom.id ℚ_[l] E) W)
        (self := (comparison E E (AlgHom.id ℚ_[l] E)).integral) n).hom.app K ≫
      (CompletedLineTensor.unit l E W K hK).hom⟦n⟧' =
    (CompletedLineTensor.unit l E W (K⟦n⟧) (shift_complete E K n hK)).hom

/-- Canonical tensor shifts transport coherent coefficient towers, including the
quotient-normalized completed equation and identity extensions, for every integer shift.
Source: blueprint `sk-thm-purity-transport`, coefficient-change calculation;
Stacks Tags 011G, 014E, 06YS, 0G7D, 06YY, 0G7E and 0D6D
(blueprint: lem-pur-scalar-shift-line-tower-transport).

Proof:
1. Termwise extension of P[n] and the shift of the extension have the same
   components and differential (-1)^n d. The identity components give the
   natural chain shift, compatible with shifted homotopies.
2. Shifts preserve flat terms. On test degree a, the sign (-1)^(na) identifies
   tensoring with P[n] with the shifted total tensor. Thus shifts preserve K-flatness.
3. Site-derived-tensor descent and localization-universal-property descend these
   natural comparisons to all derived morphisms, including inverted quasi-isomorphisms.
4. ChangeOfRingsKFlat and successive-derived-quotient-normalization identify both
   routes of the associator square on generators with (p tensor a) tensor b mapped
   to p tensor ab. Faithfulness of the resolving localization gives associator_shift.
5. Substitute that square into q20 alpha and use naturality of s21 at w10 and
   the given tower equation to obtain ordinary_tower. No rank-one condition is used.
6. The actual quotient comparison is (c,0). Completed-scalar-chain-shift acts by
   (x,y) mapped to (x,(-1)^n y); it carries (c,0) to the shifted (c,0).
7. Completed-scalar-shift-descent gives the strict derived shift. The finite-free
   comparison gives chi and its invertibility on complete inputs. Shifting the
   defining Roos triangle proves shift_complete. The normalized chain square
   descends to t chi = chi[n] s, as in completedScalarShiftRepresentativeProperty.
8. Scalar-completion-associator identifies the actual completed associator with
   the ordinary one conjugated by chi. Precompose the completed tower equation
   by the invertible twofold chi. Naturality reduces it to ordinary_tower; cancel.
9. For n=0 all component maps and signs are identities; all signs are defined
   for negative integers too. For identity extensions multiplication commutes
   with shifts degreewise, and chi is the actual completeness unit under that
   multiplication. This gives ordinary_unit and completed_unit. No inverse of
   a chain-level completion map is required.
-/
theorem scalarShiftLineTowerTransport (l : ℕ) [Fact l.Prime]
    (W : AlgebraicGeometry.Scheme.{t}) :
    Nonempty (ScalarShiftLineTowerTransportData.{t, u} l W) := by
  sorry

end WeilConjectures
