/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian

/-!
# Vector bundles with chosen total spaces in the purity setting

Source: blueprint, `sec-smooth-purity/sk-def-purity-conv`, definition at order 1895;
Stacks Project, Constructions, Tags 01M2, 01LW and 01LX
(blueprint: def-pur-vector-bundle-zero-section).

The canonical relative spectrum, symmetric-algebra augmentation, and its zero section
are reused from `VectorBundleZeroSection`. The additional data here are an arbitrary
chosen total space and an isomorphism over the base to that relative spectrum.
The Noetherian instance required by that existing construction follows from finite type
over the fixed field; it is supplied by the existing theorem, never an extra hypothesis.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- A rank-`c` vector bundle over a separated finite-type scheme over the fixed purity
field, including its chosen isomorphism `phi` to `Spec_Z Sym(𝓔)` over `Z`.
Source: blueprint, `sk-def-purity-conv`, order 1895; Stacks Tag 01M2
(blueprint: def-pur-vector-bundle-zero-section). -/
structure PurityVectorBundle
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (Z : Scheme.{u}) (hZ : Z ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated hZ] [LocallyOfFiniteType hZ] [QuasiCompact hZ] (c : ℕ) where
  E : Scheme.{u}
  p : E ⟶ Z
  𝓔 : Z.Modules
  [locallyFree : 𝓔.IsFiniteLocallyFreeOfRank c]
  phi : E ≅ @VectorBundleZeroSection.scheme Z
    (isNoetherian_of_locallyOfFiniteType hZ) c 𝓔 locallyFree
  over_commutes : phi.hom ≫ @VectorBundleZeroSection.π Z
    (isNoetherian_of_locallyOfFiniteType hZ) c 𝓔 locallyFree = p

namespace PurityVectorBundle

variable {P : WeilConjectures.PurityFiniteSetting.{u}}
  {Z : Scheme.{u}} {hZ : Z ⟶ Spec (CommRingCat.of P.field.k)}
  [IsSeparated hZ] [LocallyOfFiniteType hZ] [QuasiCompact hZ] {c : ℕ}

/-- The zero section is the augmentation section of the canonical relative spectrum,
followed by the inverse of the chosen `phi`. The augmentation is the existing unique
algebra morphism killing `SymmetricAlgebraSheaf.inclusion`; its sectionwise composite
with `sectionMap` is `SymmetricAlgebra.algebraMapInv`.
Source: blueprint, `sk-def-purity-conv`, order 1895; Stacks Tag 01M2
(blueprint: def-pur-vector-bundle-zero-section). -/
def zeroSection (V : PurityVectorBundle P Z hZ c) : Z ⟶ V.E :=
  @VectorBundleZeroSection.zero Z (isNoetherian_of_locallyOfFiniteType hZ)
    c V.𝓔 V.locallyFree ≫ V.phi.inv

/-- An étale trivialization comprises an étale base change and a scheme isomorphism over
its source from the pullback bundle to relative affine `c`-space. Surjectivity of the
étale map and preservation of the zero section are not part of this definition.
Source: blueprint, `sk-def-purity-conv`, order 1895
(blueprint: def-pur-vector-bundle-zero-section). -/
structure Trivialization (V : PurityVectorBundle P Z hZ c) where
  Z' : Scheme.{u}
  u : Z' ⟶ Z
  [etale : Etale u]
  tau : pullback V.p u ≅ AffineSpace (ULift.{u} (Fin c)) Z'
  over_commutes : tau.hom ≫ (AffineSpace (ULift.{u} (Fin c)) Z' ↘ Z') =
    pullback.snd V.p u

end PurityVectorBundle
end AlgebraicGeometry
