/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SixFunctors.Finite.Dualizing.FiniteDualizingData
public import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierModels
public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierModels
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructibleSheafBidualityIntegral
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructibleSheafBidualityRational
public import WeilConjectures.SixFunctors.ConstructibleSheafBidualityQbar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ConstructibleSheafBidualityBaseField

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj
attribute [local instance] DerivedCategory.braidedCategory'
attribute [local irreducible] DerivedCategory.monoidalClosed
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]

/-- Transport Verdier biduality through all coefficient stages.

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/det-prop-sf-biduality-general.proof.md`, the single
coefficient paragraph.  The four premises are independent current stage
statements: derived-complete integral duality, rational scalar coherence,
common-stage Qbar duality, and reflection by the base-change functor.  The
missing argument pastes their evaluation-compatible comparisons, uses the
open--closed triangle on constructible objects, and applies conservativity to
the canonical condensed evaluation transpose.  It does not assume a finite-
stage biduality theorem as a hypothesis.
(blueprint: lem-pd-constructible-sheaf-biduality-devissage) -/
theorem isIso_biduality_constructible_sheaf_of_stage_transport
    (hIntegral : ∀ (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ)
      [Fact l.Prime] (hl : l ≠ D.p) (E : Type u) [Field E]
      [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (Y : Scheme.{u})
      [Y.Over (Spec (.of D.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
      [QuasiCompact (Y ↘ Spec (.of D.k))]
      [IsSeparated (Y ↘ Spec (.of D.k))]
      (ω : WeilConjectures.sfIntegralConstructibleCategory l E Y)
      (r : ∀ n : ℕ,
        (WeilConjectures.scalarReductionDerivedExtension l E Y n).obj ω.obj ≅
          WeilConjectures.integralDualizingFiniteTerm l E D Y n),
      WeilConjectures.IntegralVerdier.Conclusion l E Y D hl ω r)
    (hRational : ∀ (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ)
      [Fact l.Prime] (hl : l ≠ D.p) (Y : Scheme.{u})
      [Y.Over (Spec (.of D.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
      [QuasiCompact (Y ↘ Spec (.of D.k))]
      [IsSeparated (Y ↘ Spec (.of D.k))],
      WeilConjectures.RationalVerdier.Conclusion D l hl Y)
    (hQbar : ∀ (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ)
      [Fact l.Prime] (hl : l ≠ D.p) (Ω : Type u) [Field Ω]
      [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (Y : Scheme.{u})
      [Y.Over (Spec (.of D.k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
      [QuasiCompact (Y ↘ Spec (.of D.k))]
      [IsSeparated (Y ↘ Spec (.of D.k))],
      WeilConjectures.CurrentCoefQbarVerdierConclusion D l hl Ω Y)
    (hBase : ∀ {C : Type u} {D : Type u} [Category.{u} C] [Category.{u} D]
      (F : C ⥤ D) (hF : F.FullyFaithful) {A B : C} (f : A ⟶ B)
      [IsIso (F.map f)], IsIso f)
    [IsIso S.hom] (a : X ⟶ S)
    (M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left))
    (hM : IsConstructibleModuleObject _ M) :
    IsIso (toIhomIhom
      ((boundedConstructibleUpperShriek ℓ a).obj (𝟙_ _)).obj
      ((DerivedCategory.singleFunctor _ 0).obj M)) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
