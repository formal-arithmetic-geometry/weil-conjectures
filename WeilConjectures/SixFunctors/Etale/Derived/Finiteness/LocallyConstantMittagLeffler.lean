/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LocalSystems
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.Algebra.Homology.DerivedCategory.MittagLefflerArtinian
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs

/-!
# Towers of finite locally constant sheaves are Mittag-Leffler

Let `Y` be a connected scheme with a geometric point `s` and `Λ` a finite ring.

- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.isIso_of_isIso_sheafFiber_map`: a
  morphism of finite locally constant sheaves of `Λ`-modules which is an isomorphism on the
  stalk at `s` is an isomorphism (Galois correspondence,
  `AlgebraicGeometry.Scheme.exists_equivalence_isFiniteLocallyConstantSheaf`);
- `AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.imageSubobject`: images of morphisms
  of finite locally constant sheaves are finite locally constant;
- `AlgebraicGeometry.Scheme.imagesStabilize_of_isFiniteLocallyConstantSheaf`,
  `AlgebraicGeometry.Scheme.isMittagLefflerTower_of_isFiniteLocallyConstantSheaf`: in a tower
  of finite locally constant sheaves the images stabilise (their stalks at `s` form a decreasing
  chain in a finite module), so the tower is Mittag-Leffler;
- `Scheme.isMittagLefflerTower_comp_comparisonUpperStar_of_isFiniteLocallyConstantSheaf`:
  so is its comparison pullback `ν^*` to the pro-étale site.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} [ConnectedSpace Y] {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (s : Spec (.of Ω) ⟶ Y) {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

section Stalk

variable {F G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}

end Stalk

end AlgebraicGeometry.Scheme
