/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import WeilConjectures.AlgebraicGeometry.ConstructibleNoetherianEtaleModules
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingedComparisonInjectiveAcyclicity
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionEquivalence
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.ConstantCoefficientScalarExtension
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsSupplement
public import WeilConjectures.AlgebraicGeometry.StrictPerfectCoefficientPackageSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.ConstructibleSheaf.RestrictScalars
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Principal-quotient scalar restriction

Source: `WeilConjectures/SixFunctors/Etale/Derived/RestrictScalarsTorAmplitude.lean`,
`torAmplitudeIn_derivedRestrictScalars` and `boundedConstructible_derivedRestrictScalars_iff`;
Stacks Project, Tag 03RW(3), for the affine-local constructibility convention
(blueprint: lem-route-restriction-scalar-tor-shift).

The Tor estimate needs no Noetherian or finite-ring hypothesis. The constructibility clause
uses the recorded affine-local module predicate and one global cohomological interval.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

open Scheme

-- Cache sheafification on the concrete sites before elaborating the local models.
-- This avoids reconstructing the same large instance terms at every constant sheaf.
private instance etaleModuleWeakSheafify (Y : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} R) := inferInstance

private instance etaleModuleOverWeakSheafify (Y : Scheme.{u}) (R : Type (u + 1))
    [CommRing R] (U : Y.Etale) :
    HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} R) := inferInstance

private instance etaleRingWeakSheafify (Y : Scheme.{u}) :
    HasWeakSheafify Y.smallEtaleTopology RingCat.{u + 1} := inferInstance

private instance etaleModuleLocallyBijective (Y : Scheme.{u}) (R : Type (u + 1))
    [CommRing R] : Y.smallEtaleTopology.WEqualsLocallyBijective (ModuleCat.{u + 1} R) :=
  inferInstance

private noncomputable instance etaleModuleAbelian (Y : Scheme.{u}) (R : Type (u + 1))
    [CommRing R] : Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  inferInstance

private instance : JointlySurjective etalePrecoverage.{u} :=
  inferInstanceAs (JointlySurjective (precoverage @Etale))

private def etaleFiniteModels {Y : Scheme.{u}} {R : Type (u + 1)} [CommRing R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) : Prop :=
  ∃ V : Cover.{u} etalePrecoverage Y, ∀ b : V.I₀,
    ∃ M : ModuleCat.{u + 1} R, Module.Finite R M ∧
      Nonempty (F.over (V.etalePrecoverageToEtale b) ≅
        (constantSheaf (Y.smallEtaleTopology.over (V.etalePrecoverageToEtale b))
          (ModuleCat.{u + 1} R)).obj M)

private noncomputable def finiteModelPullbackIso
    {Y : Scheme.{u}} {R : Type (u + 1)} [CommRing R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : Y.Etale) (M : ModuleCat.{u + 1} R)
    (e : F.over U ≅
      (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)).obj M) :
    (Etale.upperStar (ModuleCat.{u + 1} R) U.hom).obj F ≅
      (constantSheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M :=
  (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} R) U F).symm ≪≫
    (Etale.overSheafEquiv U (ModuleCat.{u + 1} R)).functor.mapIso e ≪≫
    ((Etale.overEquiv U).constantSheafSheafCongrIso
      (Y.smallEtaleTopology.over U) U.left.smallEtaleTopology
      (ModuleCat.{u + 1} R) CategoryTheory.Over.mkIdTerminal).app M

private noncomputable def finiteModelStalkIso
    {Y : Scheme.{u}} {R : Type (u + 1)} [CommRing R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (U : Y.Etale) (M : ModuleCat.{u + 1} R)
    (e : F.over U ≅
      (constantSheaf (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} R)).obj M)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ U.left) :
    ((pointSmallEtale (s ≫ U.hom)).sheafFiber
      (A := ModuleCat.{u + 1} R)).obj F ≅ M := by
  have : PreservesFilteredColimitsOfSize.{u, u}
      (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  exact ((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} R) U.hom s).app F).symm ≪≫
    (pointSmallEtale s).sheafFiber.mapIso (finiteModelPullbackIso F U M e) ≪≫
    (pointSmallEtale s).sheafFiberConstantSheafIso M

private theorem etaleFiniteModels_iff
    {Y : Scheme.{u}} {R : Type (u + 1)} [CommRing R]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    etaleFiniteModels F ↔ IsFiniteLocallyConstantSheaf F := by
  classical
  constructor
  · rintro ⟨V, hV⟩
    refine { toIsLocallyConstantSheaf := ⟨⟨⟨V, fun b ↦ ?_⟩⟩⟩
             toIsFiniteSheaf := ⟨fun Ω _ _ s ↦ ?_⟩ }
    · obtain ⟨M, _, ⟨e⟩⟩ := hV b
      exact Sheaf.isConstant_of_iso _ e
    · obtain ⟨b, x, hx⟩ := V.exists_eq (s default)
      have : Etale (V.f b) := V.map_prop b
      obtain ⟨t, ht, _⟩ := exists_fac_of_etale_of_isSepClosed (V.f b) s x hx
      obtain ⟨M, hM, ⟨e⟩⟩ := hV b
      have hgen := (ModuleCat.isFinitelyGenerated_iff M).mpr hM
      have he := finiteModelStalkIso F (V.etalePrecoverageToEtale b) M e t
      change ((pointSmallEtale (t ≫ V.f b)).sheafFiber
        (A := ModuleCat.{u + 1} R)).obj F ≅ M at he
      rw [ht] at he
      exact hgen.of_iso he.symm
  · intro hF
    have := hF
    obtain ⟨d⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := F)
    let V := d.cover.nonemptyMembers
    refine ⟨V, fun b ↦ ?_⟩
    have := d.isConstant b.1
    obtain ⟨M, ⟨e⟩⟩ :=
      (F.over (d.cover.etalePrecoverageToEtale b.1)).mem_essImage_of_isConstant
    let U := V.etalePrecoverageToEtale b
    have : Nonempty U.left := b.2
    let x : U.left := Classical.arbitrary _
    let Ω := SeparableClosure (U.left.residueField x)
    let t : Spec (.of Ω) ⟶ U.left := (SpecToEquivOfField Ω _).symm
      ⟨x, CommRingCat.ofHom (algebraMap (U.left.residueField x) Ω)⟩
    have hgen := (IsFiniteSheaf.isFinitelyGenerated_sheafFiber
      (F := F) Ω (t ≫ U.hom)).of_iso (finiteModelStalkIso F U M e.symm t)
    exact ⟨M, (ModuleCat.isFinitelyGenerated_iff M).mp hgen, ⟨e.symm⟩⟩

private theorem affineLocal_iff {X : Scheme.{u}} {R : Type (u + 1)}
    [CommRing R] [IsNoetherianRing R]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    IsAffineLocallyConstructibleEtaleModuleSheaf F ↔
      ∀ U : X.Opens, IsAffineOpen U →
        ∃ S : Stratification U.toScheme, ∀ a : Fin S.n,
          IsFiniteLocallyConstantSheaf
            ((Etale.upperStar (ModuleCat.{u + 1} R) (S.immersion a ≫ U.ι)).obj F) := by
  constructor
  · intro h U hU
    obtain ⟨S, _, hS⟩ := h U hU
    exact ⟨S, fun a ↦ (etaleFiniteModels_iff _).mp (hS a)⟩
  · intro h U hU
    obtain ⟨S, hS⟩ := h U hU
    exact ⟨S, S.isConstructible_stratum,
      fun a ↦ (etaleFiniteModels_iff _).mpr (hS a)⟩

private theorem affineLocal_of_iso {X : Scheme.{u}} {R : Type (u + 1)}
    [CommRing R] [IsNoetherianRing R]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)} (e : F ≅ G)
    (hF : Scheme.IsAffineLocallyConstructibleEtaleModuleSheaf F) :
    Scheme.IsAffineLocallyConstructibleEtaleModuleSheaf G := by
  apply (affineLocal_iff G).mpr
  intro U hU
  obtain ⟨S, hS⟩ := (affineLocal_iff F).mp hF U hU
  refine ⟨S, fun a ↦ ?_⟩
  have := hS a
  exact Scheme.IsFiniteLocallyConstantSheaf.of_iso
    ((upperStar (ModuleCat.{u + 1} R) (S.immersion a ≫ U.ι)).mapIso e)

private theorem affineLocal_restrictScalars_iff {X : Scheme.{u}} {R : Type (u + 1)}
    [CommRing R] [IsNoetherianRing R] (J : Ideal R) [Finite (R ⧸ J)]
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (R ⧸ J))) :
    Scheme.IsAffineLocallyConstructibleEtaleModuleSheaf
        ((Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj G) ↔
      Scheme.IsAffineLocallyConstructibleEtaleModuleSheaf G := by
  rw [affineLocal_iff, affineLocal_iff]
  constructor
  · intro h U hU
    obtain ⟨S, hS⟩ := h U hU
    refine ⟨S, fun a ↦ ?_⟩
    have : IsFiniteLocallyConstantSheaf
        ((Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J) ⋙
          upperStar (ModuleCat.{u + 1} R) (S.immersion a ≫ U.ι)).obj G) := hS a
    have : IsFiniteLocallyConstantSheaf
        ((Sheaf.restrictScalars _ (Ideal.Quotient.mk J)).obj
          ((upperStar (ModuleCat.{u + 1} (R ⧸ J)) (S.immersion a ≫ U.ι)).obj G)) :=
      IsFiniteLocallyConstantSheaf.of_iso
        ((upperStarRestrictScalarsIso (Ideal.Quotient.mk J) (S.immersion a ≫ U.ι)).app G)
    exact IsFiniteLocallyConstantSheaf.of_restrictScalars J _
  · intro h U hU
    obtain ⟨S, hS⟩ := h U hU
    refine ⟨S, fun a ↦ ?_⟩
    have : IsFiniteLocallyConstantSheaf
        ((upperStar (ModuleCat.{u + 1} (R ⧸ J)) (S.immersion a ≫ U.ι)).obj G) := hS a
    have : IsFiniteLocallyConstantSheaf
        ((upperStar (ModuleCat.{u + 1} (R ⧸ J)) (S.immersion a ≫ U.ι) ⋙
          Sheaf.restrictScalars _ (Ideal.Quotient.mk J)).obj G) :=
      inferInstanceAs (IsFiniteLocallyConstantSheaf
        ((Sheaf.restrictScalars _ (Ideal.Quotient.mk J)).obj
          ((upperStar (ModuleCat.{u + 1} (R ⧸ J)) (S.immersion a ≫ U.ι)).obj G)))
    exact IsFiniteLocallyConstantSheaf.of_iso
      ((upperStarRestrictScalarsIso (Ideal.Quotient.mk J) (S.immersion a ≫ U.ι)).app G).symm

/-- Scalar restriction along `Λ → Λ/(ϖ^m)` lowers the lower Tor bound by one. For Noetherian
`Λ` and finite quotient it also preserves and reflects bounded affine-local constructibility.
Source: `RestrictScalarsTorAmplitude.lean`, the two theorems named in the module docstring,
and Stacks Project, Tag 03RW(3)
(blueprint: lem-route-restriction-scalar-tor-shift).

Proof plan:
1. `Ideal.Quotient.mk (span {ϖ^m})` is surjective with kernel `span {ϖ^m}`, and `ϖ^m` is a
nonzerodivisor (`pow_mem hϖ m`). Specialize `torAmplitudeIn_derivedRestrictScalars` to this
map, converting both Tor predicates by `DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn`.
The source theorem allows all integer endpoints, so `a > b` and `m = 0` need no case split.
2. The private helpers identify the explicit finite constant local models of the affine-local
constructibility predicate with `IsFiniteLocallyConstantSheaf` on each stratum: a constant
model identifies the geometric stalks at points lifted through the cover with the finitely
generated model; conversely, on each nonempty member of a constant trivialization, the stalk
at a separably closed residue-field point identifies the model with a finitely generated stalk.
3. Over the finite quotient, `upperStarRestrictScalarsIso` commutes restriction with pullback
to a stratum, and `IsFiniteLocallyConstantSheaf.restrictScalars` and `.of_restrictScalars`
preserve and reflect finite local constancy; so the same strata serve on both sides.
4. Restriction of scalars `R` is exact and faithful: `mapDerivedCategoryHomologyFunctorIso`
gives `H^q(RN) ≅ R(H^q N)`, transporting constructibility in each degree, and the two
`isZero_homologyFunctor` lemmas preserve and reflect vanishing with the same `c ≤ d`. -/
theorem restrictionScalarTorShift
    (Λ : Type (u + 1)) [CommRing Λ] (ϖ : Λ) (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (m : ℕ) (hm : 1 ≤ m) (X : Scheme.{u})
    (N : DerivedCategoryModule (Λ ⧸ Ideal.span {ϖ ^ m}) X) (a b : ℤ) :
    (DerivedCategory.hasTorAmplitudeIn (Λ ⧸ Ideal.span {ϖ ^ m}) X a b N →
      DerivedCategory.hasTorAmplitudeIn Λ X (a - 1) b
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
          (Ideal.Quotient.mk (Ideal.span {ϖ ^ m}))).obj N)) ∧
    (∀ [IsNoetherianRing Λ] [Finite (Λ ⧸ Ideal.span {ϖ ^ m})],
      ((∀ q : ℤ, Scheme.IsAffineLocallyConstructibleEtaleModuleSheaf
          ((_root_.DerivedCategory.homologyFunctor _ q).obj
            ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
              (Ideal.Quotient.mk (Ideal.span {ϖ ^ m}))).obj N))) ∧
        ∃ c d : ℤ, c ≤ d ∧ ∀ q : ℤ, q < c ∨ d < q →
          IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
            ((Sheaf.derivedRestrictScalars X.smallEtaleTopology
              (Ideal.Quotient.mk (Ideal.span {ϖ ^ m}))).obj N))) ↔
      ((∀ q : ℤ, Scheme.IsAffineLocallyConstructibleEtaleModuleSheaf
          ((_root_.DerivedCategory.homologyFunctor _ q).obj N)) ∧
        ∃ c d : ℤ, c ≤ d ∧ ∀ q : ℤ, q < c ∨ d < q →
          IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj N))) := by
  have _ := hm
  constructor
  · intro hN
    apply DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
    exact torAmplitudeIn_derivedRestrictScalars
      (φ := Ideal.Quotient.mk (Ideal.span {ϖ ^ m})) (X := X)
      Ideal.Quotient.mk_surjective Ideal.mk_ker (pow_mem hϖ m)
      (DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mp hN)
  · intro _ _
    let R := Sheaf.restrictScalars X.smallEtaleTopology
      (Ideal.Quotient.mk (Ideal.span {ϖ ^ m}))
    constructor
    · rintro ⟨hc, c, d, hcd, hb⟩
      refine ⟨fun q ↦ ?_, c, d, hcd, fun q hq ↦ ?_⟩
      · apply (affineLocal_restrictScalars_iff _ _).mp
        exact affineLocal_of_iso
          ((R.mapDerivedCategoryHomologyFunctorIso q).app N).symm (hc q)
      · exact R.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
          (hb q hq)
    · rintro ⟨hc, c, d, hcd, hb⟩
      refine ⟨fun q ↦ ?_, c, d, hcd, fun q hq ↦ ?_⟩
      · exact affineLocal_of_iso ((R.mapDerivedCategoryHomologyFunctorIso q).app N)
          ((affineLocal_restrictScalars_iff _ _).mpr (hc q))
      · exact R.isZero_homologyFunctor_mapDerivedCategory_obj (hb q hq)

end AlgebraicGeometry.Etale
