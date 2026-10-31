/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleModuleStalkFunctor
public import WeilConjectures.AlgebraicGeometry.ProEtalePullbackStalkCoherence
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import WeilConjectures.SixFunctors.FlatModel
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Nilpotent.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.FiniteEtalePushforwardLocallyConstant
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleFixedModuleLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyConstantSheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModels
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Over
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import WeilConjectures.AlgebraicGeometry.ProEtaleOriginFromFiniteModels
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonLocalization
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.AlgebraicGeometry.ProEtaleEtaleFiniteModels
import WeilConjectures.AlgebraicGeometry.ProEtaleModelTypePartition
import WeilConjectures.AlgebraicGeometry.FpqcOpenSubschemeDescent
import WeilConjectures.AlgebraicGeometry.ProEtaleUniformModelEtaleCover
import Mathlib.CategoryTheory.Sites.SheafHom
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Data.Finite.Prod
import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.SiteConstantModuleIsomSheaf
import WeilConjectures.AlgebraicGeometry.ProEtaleConstantSheafStalk
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonStalk
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.ComparisonDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleExtensionZeroComparison

/-!
# Finite etale two-cycle monodromy

Source: the Weil blueprint, `lem-trf-devissage-generation`, proof Step 3
(blueprint: lem-trf-finite-etale-point-monodromy).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- The germ-normalized stalk reparametrization, transported back by the specified equality
of geometric points, minus the identity. Source: the Weil blueprint,
`lem-trf-devissage-generation`, proof Step 3
(blueprint: lem-trf-finite-etale-point-monodromy). -/
def genericStalkMonodromy (A : Type u) [CommRing A]
    {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (σ : Ω ≃+* Ω)
    (hs : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x = x) :
    finiteCoefficientModuleStalkFunctor x A ⟶ finiteCoefficientModuleStalkFunctor x A :=
  (proEtaleStalkReparam A x σ).hom ≫
    eqToHom (congrArg (fun z ↦ finiteCoefficientModuleStalkFunctor z A) hs) -
      𝟙 (finiteCoefficientModuleStalkFunctor x A)

/-- The three separation conditions on the same module stalk and its endomorphism.
The last condition uses every finite locally closed stratification, without a
constructibility or Noetherian hypothesis, and the actual scheme-theoretic closure.
The constant regular module is sheafified before open extension and closed direct image;
then the canonical fixed-module/intrinsic-module equivalence is applied.
Source: the Weil blueprint, `lem-trf-devissage-generation`, proof Step 3
(blueprint: lem-trf-finite-etale-point-monodromy). -/
structure SeparatingPointMonodromy (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules X (proEtaleConstantRing X A) ⥤
      ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (t : F ⟶ F)
    (L : proEtaleRingModules X (proEtaleConstantRing X A)) : Prop where
  /-- The degree-zero complex is a lisse flat stratum-extension generator. -/
  generator : sfProEtaleClosureGenerators X A ((_root_.DerivedCategory.singleFunctor _ 0).obj L)
  /-- No power of the stalk endomorphism on this sheaf vanishes. -/
  not_nilpotent : ¬ IsNilpotent (R := CategoryTheory.End (F.obj L)) (t.app L)
  /-- Monodromy minus identity vanishes on every constant stratum extension. -/
  constant_strata : ∀ (str : FiniteLocallyClosedStratification X) (i : Fin str.n)
    (j : str.domain i ⟶ (str.immersion i).image) [IsOpenImmersion j],
    j ≫ (str.immersion i).imageι = str.immersion i →
      t.app ((sfIntrinsicModuleEquivalence X A).functor.obj
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (str.immersion i).imageι).obj
          ((ProEtale.openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).obj
            ((constantSheaf (ProEt.topology (str.domain i))
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).obj
                (ModuleCat.of (ULift.{u + 1, u} A) (ULift.{u + 1, u} A)))))) = 0

/-- A two-cycle in the geometric fibre of a finite etale morphism separates lisse flat
stratum extensions from constant stratum extensions, using the canonical stalk and action.
Source: the Weil blueprint, `lem-trf-devissage-generation`, proof Step 3
(blueprint: lem-trf-finite-etale-point-monodromy).

Proof:
1. Take the etale sheaf pi_* A_V, pull it to the pro-etale site, and apply intrinsic
   realization. Finite etale local splitting identifies it locally with a finite direct
   sum of regular modules. It is finite locally constant and flat, and etale origin
   gives lisseness. The one-stratum identity stratification makes its degree-zero
   complex a member of sfProEtaleClosureGenerators.
2. The finite stalk formula identifies its stalk with A-valued functions on geometric
   lifts. The comparison is normalized on unit germs, and reparametrization precomposes
   each pointed lift by Spec(sigma), so its action permutes the coordinates. For
   v = delta_y - delta_(sigma y), the two-cycle hypotheses give sigma(v) = -v and
   v(y) = 1. Thus v is nonzero. In characteristic three, (sigma - 1)v = -2v = v,
   so no positive power vanishes; the zeroth power is the identity on a nonzero module.
3. A closed immersion is finite and a monomorphism. Its stalk is zero when there is
   no lift and is the stalk at the unique lift otherwise. Open extension by zero
   likewise has zero stalk outside the open and the original stalk inside. Each
   unique lift is fixed by sigma, and constant germs of the regular module are fixed.
   Hence monodromy minus identity is zero on every constant stratum extension.
   Direct-image and open-extension comparison, normalized on germs, identify this
   with the action on intrinsic modules. No genericity or reducedness is used. -/
theorem finite_etale_point_monodromy
    {X V : Scheme.{u}} (π : V ⟶ X) [IsFinite π] [Etale π]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ X) (σ : Ω ≃+* Ω)
    (hs : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x = x)
    (y : Spec (.of Ω) ⟶ V) (hy : y ≫ π = x)
    (hmove : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ y ≠ y)
    (htwo : Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ y = y)
    (A : Type u) [CommRing A] [Finite A] [CharP A 3] [Nontrivial A] :
    ∃ L : proEtaleRingModules X (proEtaleConstantRing X A),
      SeparatingPointMonodromy X A (finiteCoefficientModuleStalkFunctor x A)
        (genericStalkMonodromy A x σ hs) L := by
  sorry

end AlgebraicGeometry
