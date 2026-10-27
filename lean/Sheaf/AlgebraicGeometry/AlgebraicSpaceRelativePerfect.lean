module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules

/-! # Relative perfectness on an algebraic space over a scheme

Source: Stacks Project, More on Morphisms of Spaces, Tag 0DKN and
lemma-affine-locally-rel-perfect (blueprint: def-sfb-space-relative-perfect).

The chart criterion uses the existing scheme pseudo-coherence and the existing
K-flat definition of Tor dimension over the inverse-image structure sheaf.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Relative perfectness tested on affine étale scheme charts. On each affine chart,
pseudo-coherence is the bounded-above finite-free local condition, and the relative
Tor bound is tested against ALL inverse-image-structure-sheaf module sheaves.
An affine chart is quasi-compact, so locally finite Tor dimension gives one finite
interval there; different charts may have different intervals. The target is a scheme.
Source: Stacks, Tag 0DKN and lemma-affine-locally-rel-perfect
(blueprint: def-sfb-space-relative-perfect). -/
def IsPerfectRelativeToScheme {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : Over S) (f : X ⟶ schemeSpace Y)
    [HasDerivedCategory.{w} X.SmallModules] (K : X.DerivedModules) : Prop :=
  letI : ∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) :=
    fun _Z ↦ HasDerivedCategory.standard _
  letI : ∀ (Z : Scheme.{u}) (U : Z.Opens), HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U)) :=
    fun _Z _U ↦ HasDerivedCategory.standard _
  X.derivedQCohProperty K ∧
  ∀ T : X.EtaleSite, IsAffine (X.etaleForget.obj T) →
    Scheme.IsPseudoCoherent (X.etaleForget.obj T) (derivedSchemeRestriction X T K) ∧
      Scheme.HasFiniteTorDimensionOver (chartToScheme Y f T)
        (derivedSchemeRestriction X T K)

end AlgebraicGeometry.AlgebraicSpace
