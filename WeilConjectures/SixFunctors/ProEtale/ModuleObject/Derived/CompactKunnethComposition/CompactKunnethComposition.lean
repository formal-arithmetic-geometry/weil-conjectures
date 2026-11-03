/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProductComparisons.NativeSixFunctorKunnethMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SkThmSfCompComposition

/-!
# Composition of the compact-support external Künneth comparison

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-lefschetz-verdier/sec-kunneth-formulas-and-external-duality/
sk-prop-tf-exceptional-external-kunneth.proof.md, “Constant and lisse coefficients”:
alpha is compatible with composition of morphisms (compact-support compositor
equation before taking mates).
The explicit compact-support calculation is recorded in the seven steps of
(blueprint: lem-sf-compact-kunneth-composition).

The comparisons are `ProductComparisons.ku`, using the normalized relative six-arrow
word, and `RelativeKunneth.CanonicalCompositionData.comp`, using proper/open interchange.
All arrows are evaluated in the existing ordinary module-derived categories.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.CompactKunnethComposition

open CompactificationReindexing RelativeKunneth ProductComparisons

variable {k : Type u} [Field k]

/-- The existing continuous-function coefficient ring, bundled as a commutative
condensed ring. This is the discrete condensed ring when R has the discrete topology.
Source: the finite coefficient convention and the existing universe-polymorphic
continuous coefficient construction (blueprint: lem-sf-compact-kunneth-composition). -/
def coefficient (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    ScalarSixRing.{u} := by
  letI : IsCommMonObj (Profinite.continuousCoefficientRingObj R) :=
    Sheaf.isCommMonObj_sheafCompose_obj (coherentTopology Profinite.{u})
      (Profinite.continuousCoefficientRingSheaf R) (by
        intro S a b
        apply ULift.ext
        exact mul_comm a.down b.down)
  exact ⟨Profinite.continuousCoefficientRingObj R⟩

/-- Auxiliary Cartesian squares presenting the relative product used by `ku`.
The endpoint schemes and projections are parameters, so successive comparisons share
literally the same absolute products. This only packages fields of the existing `Geometry`.
Source: sk-def-sf-kv-maps (i), applied to f, g and gf
(blueprint: lem-sf-compact-kunneth-composition). -/
structure Factorization {X₁ X₂ Y₁ Y₂ W T : SepFinType k}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (r₁ : W ⟶ X₁) (r₂ : W ⟶ X₂) (t₁ : T ⟶ Y₁) (t₂ : T ⟶ Y₂) where
  U : SepFinType k
  V : SepFinType k
  a₁ : U ⟶ X₁
  a₂ : V ⟶ X₂
  u : U ⟶ T
  v : V ⟶ T
  p : W ⟶ U
  q : W ⟶ V
  exchange₁ : IsPullback a₁.hom.left u.hom.left f₁.hom.left t₁.hom.left
  exchange₂ : IsPullback a₂.hom.left v.hom.left f₂.hom.left t₂.hom.left
  relativeProduct : IsPullback p.hom.left q.hom.left u.hom.left v.hom.left
  path₁ : p.hom.left ≫ a₁.hom.left = r₁.hom.left
  path₂ : q.hom.left ≫ a₂.hom.left = r₂.hom.left

/-- Reassemble the existing geometry, without introducing a new product or comparison.
Source: the three product diagrams in the node's displayed equation
(blueprint: lem-sf-compact-kunneth-composition). -/
def Factorization.geometry {X₁ X₂ Y₁ Y₂ W T : SepFinType k}
    {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    {r₁ : W ⟶ X₁} {r₂ : W ⟶ X₂} {t₁ : T ⟶ Y₁} {t₂ : T ⟶ Y₂}
    (s : Factorization f₁ f₂ r₁ r₂ t₁ t₂)
    (hW : IsPullback r₁.hom.left r₂.hom.left X₁.obj.hom X₂.obj.hom)
    (hT : IsPullback t₁.hom.left t₂.hom.left Y₁.obj.hom Y₂.obj.hom) : Geometry k where
  X₁ := X₁
  X₂ := X₂
  Y₁ := Y₁
  Y₂ := Y₂
  W := W
  T := T
  f₁ := f₁
  f₂ := f₂
  r₁ := r₁
  r₂ := r₂
  t₁ := t₁
  t₂ := t₂
  U := s.U
  V := s.V
  a₁ := s.a₁
  a₂ := s.a₂
  u := s.u
  v := s.v
  p := s.p
  q := s.q
  sourceProduct := hW
  targetProduct := hT
  exchange₁ := s.exchange₁
  exchange₂ := s.exchange₂
  relativeProduct := s.relativeProduct
  path₁ := s.path₁
  path₂ := s.path₂

end AlgebraicGeometry.ProEtale.CondensedRing.CompactKunnethComposition
