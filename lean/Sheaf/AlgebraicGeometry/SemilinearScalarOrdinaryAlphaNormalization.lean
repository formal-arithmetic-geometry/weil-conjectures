module

public import Sheaf.AlgebraicGeometry.SemilinearScalarOrdinaryComparison
public import Sheaf.AlgebraicGeometry.StrictTowerOrdinaryProperOpenArrows

/-! # Canonical normalization of the ordinary scalar alpha

Source: Stacks, Tags 03D7, 03DI and 0F7B; the intrinsic proper/open word.
(blueprint: lem-sf-semilinear-scalar-ordinary-alpha-normalization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable {R : ℕ → CommRingCat.{u + 1}} {φ : ∀ n : ℕ, R (n + 1) ⟶ R n}
  {B : Type (u + 1)} [CommRing B] {ψ : ∀ n : ℕ, CommRingCat.of B ⟶ R n}

/-- The alpha of a normalized ordinary scalar package is canonical.
Source: Stacks, Tags 03D7, 03DI and 0F7B, and the intrinsic proper/open word.
(blueprint: lem-sf-semilinear-scalar-ordinary-alpha-normalization).
Proof: beta_unit identifies the inverse cartesian beta by injectivity of the open
adjunction Hom equivalence. clopen_unit identifies the open-to-direct map with the
transpose of the inverse open unit; pi_eq then identifies its projector with the
canonical clopen projector. The unit-normalized open compositor is the whiskering
of the single-level compositor. Transport along equality is checked by substitution
of the equality, where both maps are identities. Substitute these identifications
in alpha_eq. The ordinary alpha word is the termwise image of singleAlpha: whiskering
preserves composition and its compositor components are identities. This is exactly
towerAlpha, for arbitrary commutative proper/open squares. No derived evaluation or
faithfulness assertion is involved. -/
theorem scalarOrdinaryAlphaNormalization (D : OrdinaryScalarComparison R φ B ψ)
    {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S) (p : W ⟶ T) (i : S ⟶ T)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    D.alpha k r p i h = StrictTower.towerAlpha B k r p i h := by sorry

end AlgebraicGeometry.ProEtale.VaryingRing
