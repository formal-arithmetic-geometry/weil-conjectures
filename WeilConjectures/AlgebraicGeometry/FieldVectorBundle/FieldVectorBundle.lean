/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.PurityVectorBundle.PurityVectorBundleZeroSection

/-!
# Vector bundles over a general base field

Source: blueprint sk-def-purity-conv, def-pur-vector-bundle-zero-section (restated over a
purity base field K, node def-pur-base-field; Houyi #1396); Stacks Tags 01M2, 01LX
(blueprint: def-pur-vector-bundle-zero-section).

`FieldVectorBundle` is `PurityVectorBundle` with `Spec P.field.k` replaced by `Spec K`. The
fields are literally the same, so `PurityVectorBundle.equivField` is the identity on fields:
the fixed-setting declarations are the case `K = P.field.k`.

## Main definitions

* `AlgebraicGeometry.FieldVectorBundle`, its zero section, `canonical` (phi = Iso.refl),
  `Trivialization`, `PurityVectorBundle.equivField`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- A rank-`c` vector bundle over a separated finite-type scheme over a base field `K`. It
includes the chosen isomorphism `phi` to `Spec_Z Sym(𝓔)` over `Z`. The fields are literally
those of `PurityVectorBundle`, which is the case `K = P.field.k` (`PurityVectorBundle.equivField`).
Source: blueprint, `sk-def-purity-conv`, order 1895; Stacks Tag 01M2
(blueprint: def-pur-vector-bundle-zero-section). -/
structure FieldVectorBundle
    (K : Type u) [Field K]
    (Z : Scheme.{u}) (hZ : Z ⟶ Spec (CommRingCat.of K))
    [IsSeparated hZ] [LocallyOfFiniteType hZ] [QuasiCompact hZ] (c : ℕ) where
  E : Scheme.{u}
  p : E ⟶ Z
  𝓔 : Z.Modules
  [locallyFree : 𝓔.IsFiniteLocallyFreeOfRank c]
  phi : E ≅ @VectorBundleZeroSection.scheme Z
    (isNoetherian_of_locallyOfFiniteType hZ) c 𝓔 locallyFree
  over_commutes : phi.hom ≫ @VectorBundleZeroSection.π Z
    (isNoetherian_of_locallyOfFiniteType hZ) c 𝓔 locallyFree = p

namespace FieldVectorBundle

variable {K : Type u} [Field K]
  {Z : Scheme.{u}} {hZ : Z ⟶ Spec (CommRingCat.of K)}
  [IsSeparated hZ] [LocallyOfFiniteType hZ] [QuasiCompact hZ] {c : ℕ}

/-- The zero section: the augmentation section of the canonical relative spectrum,
followed by the inverse of the chosen `phi`. This is `PurityVectorBundle.zeroSection` with
the field generalised.
Source: blueprint, `sk-def-purity-conv`, order 1895; Stacks Tag 01M2
(blueprint: def-pur-vector-bundle-zero-section). -/
def zeroSection (V : FieldVectorBundle K Z hZ c) : Z ⟶ V.E :=
  @VectorBundleZeroSection.zero Z (isNoetherian_of_locallyOfFiniteType hZ)
    c V.𝓔 V.locallyFree ≫ V.phi.inv

/-- The canonical bundle of a finite locally free module: total space literally
`Spec_Z Sym(𝓔)` and `phi = Iso.refl`. This is A's `canonicalBundle` and iface
`regularSectionBundle`, over a general base field.
Source: Stacks Tag 01M2 (blueprint: def-pur-vector-bundle-zero-section). -/
def canonical (K : Type u) [Field K] (Z : Scheme.{u}) (hZ : Z ⟶ Spec (CommRingCat.of K))
    [IsSeparated hZ] [LocallyOfFiniteType hZ] [QuasiCompact hZ] (c : ℕ)
    (𝓔 : Z.Modules) [h𝓔 : 𝓔.IsFiniteLocallyFreeOfRank c] : FieldVectorBundle K Z hZ c where
  E := @VectorBundleZeroSection.scheme Z (isNoetherian_of_locallyOfFiniteType hZ) c 𝓔 h𝓔
  p := @VectorBundleZeroSection.π Z (isNoetherian_of_locallyOfFiniteType hZ) c 𝓔 h𝓔
  𝓔 := 𝓔
  locallyFree := h𝓔
  phi := Iso.refl _
  over_commutes := Category.id_comp _

end FieldVectorBundle

namespace PurityVectorBundle

variable {P : WeilConjectures.PurityFiniteSetting.{u}}
  {Z : Scheme.{u}} {hZ : Z ⟶ Spec (CommRingCat.of P.field.k)}
  [IsSeparated hZ] [LocallyOfFiniteType hZ] [QuasiCompact hZ] {c : ℕ}

/-- The iface purity bundles are exactly the field-general bundles over `P.field.k`. The
fields are identical, so both round trips are the identity by structure eta.
Source: def-pur-vector-bundle-zero-section (blueprint: def-pur-vector-bundle-zero-section). -/
def equivField :
    PurityVectorBundle P Z hZ c ≃ FieldVectorBundle P.field.k Z hZ c where
  toFun V :=
    { E := V.E, p := V.p, 𝓔 := V.𝓔, locallyFree := V.locallyFree, phi := V.phi,
      over_commutes := V.over_commutes }
  invFun V :=
    { E := V.E, p := V.p, 𝓔 := V.𝓔, locallyFree := V.locallyFree, phi := V.phi,
      over_commutes := V.over_commutes }
  left_inv _ := rfl
  right_inv _ := rfl

end PurityVectorBundle

end AlgebraicGeometry
