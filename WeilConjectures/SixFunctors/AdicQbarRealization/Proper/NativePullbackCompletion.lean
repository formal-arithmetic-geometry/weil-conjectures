/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperCoefficientOperations
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # The specified completion isomorphism on native integral inputs

Source: Bhatt--Scholze, Lemma 6.5.9 and Proposition 6.6.11.
(blueprint: lem-sf-native-pullback-completion)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper

private theorem primeUnit (l : ℕ) (W : Scheme.{u})
    [∀ x : W, Invertible (l : W.residueField x)] : IsUnit (l : Γ(W, ⊤)) := by
  apply RingedSpace.isUnit_of_isUnit_germ W.toSheafedSpace ⊤
  intro x hx
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  simpa only [map_natCast] using (isUnit_of_invertible (l : W.residueField x)).ne_zero

/-- The quotient-tower completion map is a natural isomorphism on integral constructible
inputs over the geometric spaces. Its components are the published map, not arbitrary
isomorphisms between the objects.
Source: Bhatt--Scholze, Lemma 6.5.9, Proposition 6.6.11 and Remark 6.8.15.
(blueprint: lem-sf-native-pullback-completion).

Proof: finite type over the field gives local noetherianity and a finite dimension bound;
quasi-compactness gives a noetherian scheme. Invertibility in the residue fields implies
invertibility in every local stalk and then in global sections. Apply
ordinaryCompletedIntegralPullback to every object of the full integral constructible
subcategory. It proves that the specified completion-map component is invertible.
These components form a natural isomorphism because the original comparison is natural.
The component equation also proves uniqueness. Empty schemes and zero complexes need no
separate choice, since the same completion map is used throughout. -/
theorem nativePullbackCompletion (l : ℕ) [Fact l.Prime]
    (D : FiniteFieldDatum.{u}) (Z T : GeometricSpace D) (p : Z.base ⟶ T.base)
    [∀ x : Z.base.left, Invertible (l : Z.base.left.residueField x)]
    [∀ x : T.base.left, Invertible (l : T.base.left.residueField x)]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃! e : (sfIntegralConstructible l E T.base.left).ι ⋙
          ordinaryIntegralDerivedPull l E p.left ≅
        (sfIntegralConstructible l E T.base.left).ι ⋙ integralDerivedPullback l E p.left,
      ∀ K : sfIntegralConstructibleCategory l E T.base.left,
        e.hom.app K = (ordinaryIntegralCompletionComparison l E p.left).app K.obj := by
  let := Z.finiteType
  let := Z.quasiCompact
  let := T.finiteType
  let := T.quasiCompact
  let : CompactSpace Z.base.left := QuasiCompact.compactSpace_of_compactSpace Z.base.hom
  let : CompactSpace T.base.left := QuasiCompact.compactSpace_of_compactSpace T.base.hom
  let : IsLocallyNoetherian Z.base.left :=
    LocallyOfFiniteType.isLocallyNoetherian Z.base.hom
  let : IsLocallyNoetherian T.base.left :=
    LocallyOfFiniteType.isLocallyNoetherian T.base.hom
  let : IsNoetherian Z.base.left := ⟨⟩
  let : IsNoetherian T.base.left := ⟨⟩
  have hi (K : sfIntegralConstructibleCategory l E T.base.left) :
      IsIso ((ordinaryIntegralCompletionComparison l E p.left).app K.obj) :=
    (ordinaryCompletedIntegralPullback l E p.left
      (exists_topologicalKrullDim_le Z.base.hom)
      (exists_topologicalKrullDim_le T.base.hom)
      (primeUnit l Z.base.left) (primeUnit l T.base.left) K.obj K.property).2
  let e : (sfIntegralConstructible l E T.base.left).ι ⋙
          ordinaryIntegralDerivedPull l E p.left ≅
        (sfIntegralConstructible l E T.base.left).ι ⋙ integralDerivedPullback l E p.left :=
    NatIso.ofComponents (fun K ↦ @asIso _ _ _ _ _ (hi K))
      (fun f ↦ (ordinaryIntegralCompletionComparison l E p.left).naturality f.hom)
  refine ⟨e, fun K ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  ext K
  exact he' K

end WeilConjectures.AdicQbarRealization.Proper
