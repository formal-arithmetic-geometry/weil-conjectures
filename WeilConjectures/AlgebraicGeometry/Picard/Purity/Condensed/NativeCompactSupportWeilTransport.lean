/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportCompatibility
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarCompatibility
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportAffineGeometry
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
public import WeilConjectures.AlgebraicGeometry.Picard.Purity.Condensed.CondensedPurityTateDatum
public import WeilConjectures.AlgebraicGeometry.SepFinType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs

/-! # Native compact-support Weil transport

Source: latest blueprint, `part-duality-trace-formula/sec-poincare-duality/`
`sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-def-ops/`
`sk-thm-sf-package/def-pur-compact-support-transport.md`, both displayed formulas.
The compact-support map is the native exchange, the fixed Cartesian pullback
identification, and the refinement-characterized compactification comparison.
(blueprint: def-pur-compact-support-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

namespace WeilConjectures.Purity.Condensed

/-- The fixed identification of the literal pullback leg with the leg of `sq`.
This is the native derived pullback compositor for `sq.isoPullback`, rewritten
by its first projection equation.
Source: compactification base change and the inverse-image identification in
`def-exchange-projection` (blueprint: def-pur-compact-support-transport). -/
def pullbackNativeIdentification
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback a f' f v) :
    CompactificationReindexing.P Λ (pullback.fst f v) ⋙
        CompactificationReindexing.P Λ sq.isoPullback.hom ≅
      CompactificationReindexing.P Λ a :=
  (leftDerivedUpperStarComp Λ sq.isoPullback.hom (pullback.fst f v)).symm ≪≫
    eqToIso (by rw [sq.isoPullback_hom_fst])

/-- The literal and supplied pullback compactifications have the same proper
middle scheme; their open factors are related by `sq.isoPullback`.
Source: compactification base change in `def-exchange-projection`
(blueprint: def-pur-compact-support-transport). -/
def pullbackCompactificationSquare
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback a f' f v)
    (c : Compactification f) :
    CompactificationReindexing.Square (c.baseChange v) (c.ofIsPullback sq)
      sq.isoPullback.hom (𝟙 Y') where
  middle := eqToHom (by rfl)
  openSquare := by
    letI : IsIso (eqToHom (by rfl : (c.ofIsPullback sq).Z = (c.baseChange v).Z)) := inferInstance
    apply IsPullback.of_horiz_isIso
    constructor
    apply pullback.hom_ext
    · simp [Compactification.baseChange, Compactification.ofIsPullback, Category.assoc]
    · simp [Compactification.baseChange, Compactification.ofIsPullback,
        Category.assoc, sq.isoPullback_hom_snd]
  properSquare := ⟨by simp [Compactification.baseChange, Compactification.ofIsPullback]⟩

/-- The actual native identification between the two pullback compactification
models. Insert the inverse-image identity comparison, use the proper/open
exchange for `sq.isoPullback` and the identity on the middle scheme, then use
`pullbackNativeIdentification`. Every factor is a specified native map.
Source: `def-exchange-projection`, Cartesian inverse-image identification
(blueprint: def-pur-compact-support-transport). -/
def pullbackCompactificationIdentification
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {a : X' ⟶ X} {v : Y' ⟶ Y} (sq : IsPullback a f' f v)
    (c : Compactification f) :
    CompactificationReindexing.P Λ (pullback.fst f v) ⋙
        CompactificationReindexing.F Λ (c.baseChange v) ≅
      CompactificationReindexing.P Λ a ⋙
        CompactificationReindexing.F Λ (c.ofIsPullback sq) := by
  let s := pullbackCompactificationSquare sq c
  letI : IsIso s.middle := by
    dsimp [s, pullbackCompactificationSquare]
    infer_instance
  letI : IsIso (𝟙 Y') := IsIso.id _
  letI := (CompactificationReindexing.square_isIso Λ s
    (show CommSq sq.isoPullback.hom f' (pullback.snd f v) (𝟙 Y') from
      ⟨by rw [sq.isoPullback_hom_snd, Category.comp_id]⟩)).2
  let e : CompactificationReindexing.F Λ (c.baseChange v) ≅
      CompactificationReindexing.P Λ sq.isoPullback.hom ⋙
        CompactificationReindexing.F Λ (c.ofIsPullback sq) :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ (leftDerivedUpperStarId Λ Y').symm ≪≫
        asIso (CompactificationReindexing.squareExchange Λ s)
  exact Functor.isoWhiskerLeft (CompactificationReindexing.P Λ (pullback.fst f v)) e ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pullbackNativeIdentification Λ sq) _

/-- The canonical `B_M` of compact-support base change for an isomorphism square.
It is the native exchange to the literal base change, the fixed
`sq.isoPullback` identification, and the current canonical compactification
comparison `detSfCanonicalCompactificationComparison`, in that order. The last
comparison is characterized against every common dense refinement by
`detSfCanonicalCompactificationComparison_refinement`, not by a free isomorphism.
It is the all-admissible-coefficient localizing comparison corresponding to the
refinement-normalized τ in `condensed_compactification_reindexing`.

Source: `def-exchange-projection` and `det-sf-comp-coherence-cocycle`, common
refinement normalization (blueprint: def-pur-compact-support-transport). -/
def compactSupportComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ell : ℕ) [Fact ell.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y X' Y' : Scheme.{u}} [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    {f : X ⟶ Y} {f' : X' ⟶ Y'}
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    {a : X' ⟶ X} {v : Y' ⟶ Y}
    (sq : IsPullback a f' f v) (c : Compactification f) (c' : Compactification f')
    (M : (localizingClosureProEtale Λ X).FullSubcategory)
    (hM : localizingClosureProEtale Λ X' ((CompactificationReindexing.P Λ a).obj M.obj)) :
    (CompactificationReindexing.P Λ v).obj ((CompactificationReindexing.F Λ c).obj M.obj) ⟶
      (CompactificationReindexing.F Λ c').obj ((CompactificationReindexing.P Λ a).obj M.obj) :=
  (compactSupportWeilTransport Λ c v).app M.obj ≫
    (pullbackCompactificationIdentification Λ sq c).hom.app M.obj ≫
      (detSfCanonicalCompactificationComparison Λ ell hΛ k f'
        (c.ofIsPullback sq) c').hom.app ⟨_, hM⟩

/-- Compact-support transport of the supplied strict Weil datum. Its input is
`φM : Lg_X^*M ≅ M`; its output ends in the selected `Rf_!M`. The first factor
is the concrete native `B_M` above, and the second is exactly `Rf_!(φM)`.
Membership of the pulled object follows from this isomorphism, so there is no
additional preservation hypothesis or independently supplied exchange map.

Source: latest blueprint `def-pur-compact-support-transport`, first displayed
composite (blueprint: def-pur-compact-support-transport). -/
def compactSupportWeilTransportOfDatum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (ell : ℕ) [Fact ell.Prime]
    (hΛ : IsLocalizingAdmissibleCoefficient ell Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    {X Y : Scheme.{u}} [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    {a : X ⟶ X} {v : Y ⟶ Y}
    (c : Compactification f) (sq : IsPullback a f f v)
    (M : ConstantModelConstructibleFiniteTor Λ X)
    (φM : (CompactificationReindexing.P Λ a).obj M.obj ≅ M.obj) :
    (CompactificationReindexing.P Λ v).obj ((CompactificationReindexing.F Λ c).obj M.obj) ⟶
      (CompactificationReindexing.F Λ c).obj M.obj := by
  let hM : localizingClosureProEtale Λ X M.obj := fun _ _ hgen ↦ hgen _ M.property
  let hPull : localizingClosureProEtale Λ X ((CompactificationReindexing.P Λ a).obj M.obj) := by
    intro Q hQ hgen
    let := hQ.2.1
    exact Q.prop_of_iso φM.symm (hgen _ M.property)
  exact compactSupportComparison Λ ell hΛ k sq c c ⟨M.obj, hM⟩ hPull ≫
    (CompactificationReindexing.F Λ c).map φM.hom

/-- Scheme-Frobenius form of any datum produced by compact-support transport.
This reuses the recorded canonical κ and its composition `uDatum`, for every
object on either geometric fibre, including the transported `Rf_!M`.
Source: `def-pur-compact-support-transport`, second displayed formula
(blueprint: def-pur-compact-support-transport). -/
def compactSupportSchemeFrobeniusDatum
    (D : WeilConjectures.FiniteFieldDatum.{u}) (Λ : ScalarSixRing.{u})
    (T₀ : Over (Spec (.of D.k₀)))
    (N : DerivedCategory (ModuleRingedComparison.internalModules Λ.X
      (D.purityFrobeniusFiber T₀).left))
    (φN : (actualPull Λ.X (D.purityGaloisMap T₀)).obj N ⟶ N) :=
  uDatum D Λ T₀ N φN

end WeilConjectures.Purity.Condensed
