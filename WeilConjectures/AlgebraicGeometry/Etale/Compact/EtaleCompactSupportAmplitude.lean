/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Mathlib.Topology.KrullDimension
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CohomologicalDimension
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependence

/-!
# Compact-support amplitude bounded by the original geometric fibres

## Main definitions

- `compactSupportAmplitudeCompactification`: the existing Nagata compactification with
  its base conditions supplied by the finite-type field hypotheses.

## Main statements

- `isZero_homology_rightDerivedLowerShriek_of_geometricFiberDimensionLE`: vanishing above
  twice the dimension bound on the original geometric fibres.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The existing Nagata compactification for a morphism over a finite-type field scheme.
This supplies its quasi-compact quasi-separated base instances from the finite-type hypotheses;
it introduces no additional choice beyond `NagataCompactification`. -/
noncomputable def compactSupportAmplitudeCompactification
    (k : Type u) [Field k] (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    {X : Scheme.{u}} (f : X ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] : Compactification f :=
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of k))
  NagataCompactification f

/-- For a separated finite-type morphism of finite-type schemes over a field, the higher
compact-support direct image of any etale module sheaf over a finite coefficient ring of
invertible exponent vanishes above twice the dimension bound on the original geometric fibres.
All derived functors are on the ordinary unbounded derived categories. -/
theorem isZero_homology_rightDerivedLowerShriek_of_geometricFiberDimensionLE
    (k : Type u) [Field k] (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasInvertibleExponent Λ Y] (d : ℕ)
    (hd : ∀ y : Y, topologicalKrullDim
      (↑(pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
          Y.fromSpecResidueField y))) ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (hq : 2 * (d : ℤ) < q) :
    IsZero ((_root_.DerivedCategory.homologyFunctor
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ)
          (compactSupportAmplitudeCompactification k Y f)).obj
          ((_root_.DerivedCategory.singleFunctor
            (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F))) := by
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian
    (Y ↘ Spec (.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace
    (Y ↘ Spec (.of k))
  have hdim (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y) :
      topologicalKrullDim (pullback f s : Scheme.{u}) ≤ (d : WithBot ℕ∞) := by
    obtain ⟨⟨y, t⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω Y).symm.surjective s
    let a : Spec (.of (AlgebraicClosure (Y.residueField y))) ⟶
        Spec (Y.residueField y) :=
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) _))
    have he (K : Type u) [Field K] (b : Spec (.of K) ⟶ Spec (Y.residueField y)) :
        topologicalKrullDim (pullback f (b ≫ Y.fromSpecResidueField y) : Scheme.{u}) =
          topologicalKrullDim (f.fiber y) := by
      let e := pullbackLeftPullbackSndIso f (Y.fromSpecResidueField y) b
      calc
        _ = topologicalKrullDim
            (pullback (pullback.snd f (Y.fromSpecResidueField y)) b : Scheme.{u}) :=
          (IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph).symm
        _ = _ := topologicalKrullDim_pullback_eq_of_field
          (k := Y.residueField y) (pullback.snd f (Y.fromSpecResidueField y)) b
    change topologicalKrullDim
      (pullback f (Spec.map t ≫ Y.fromSpecResidueField y) : Scheme.{u}) ≤ _
    rw [he Ω (Spec.map t), ← he (AlgebraicClosure (Y.residueField y)) a]
    exact hd y
  have hz := isZero_homology_rightDerivedLowerShriek_singleFunctor_of_two_mul_lt Λ f
    (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) (comp_over f _) d hdim F q hq
  let K := (_root_.DerivedCategory.Plus.singleFunctor
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj F
  exact hz.of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
    ((rightDerivedLowerShriekOfCompactificationPlusιIso Λ
      (compactSupportAmplitudeCompactification k Y f)
      (HasCompactification.compactification f)).app K))

end AlgebraicGeometry.Etale
