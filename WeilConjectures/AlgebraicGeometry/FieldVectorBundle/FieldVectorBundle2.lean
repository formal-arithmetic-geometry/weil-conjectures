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

namespace FieldVectorBundle

variable {K : Type u} [Field K]
  {Z : Scheme.{u}} {hZ : Z ⟶ Spec (CommRingCat.of K)}
  [IsSeparated hZ] [LocallyOfFiniteType hZ] [QuasiCompact hZ] {c : ℕ}

/-- The zero section is a section of the projection and a closed immersion. On every affine
open `U` its restriction, transported through `phi`, is the spectrum of the augmentation
`Sym(𝓔(U)) → 𝒪(U)` fixing constants and killing all degree-one generators.
Source: blueprint, `sk-def-purity-conv`, order 1895; Stacks Tags 01M2 and 01LX
(blueprint: def-pur-vector-bundle-zero-section).

Proof (the node's proof steps; as for `PurityVectorBundle.zeroSection_spec`):
1. Install the Noetherian instance `isNoetherian_of_locallyOfFiniteType hZ` (finite type over
   the field `K`) and the locally-free instance `V.locallyFree`.
2. `VectorBundleZeroSection.zero_spec Z c V.𝓔` gives `hsection : zero ≫ π = 𝟙 Z` and
   `hclosed : IsClosedImmersion zero`: the augmentation is the unique algebra map killing the
   generators (`lem-weil-pbc-quasi-coherent-symmetric-algebra-core`), on affine charts it is
   `SymmetricAlgebra.algebraMapInv`, surjective since it fixes scalars, and the affine-cover
   criterion (`lem-weil-pbc-closed-immersion-affine-cover-criterion`) gives closedness.
3. Section identity: `rw [zeroSection, ← V.over_commutes]`; `Category.assoc` and
   `Iso.inv_hom_id_assoc` cancel `phi.inv ≫ phi.hom`, and `hsection` concludes.
4. Closedness: keep `hclosed` as a local instance; the composite of a closed immersion with
   the isomorphism `phi.inv` is a closed immersion (`infer_instance`).
5. Affine opens: take `zU := VectorBundleZeroSection.zeroRestricted Z c V.𝓔 U.1`; after
   unfolding `zeroSection` and cancelling `phi.inv ≫ phi.hom`, the first equation is
   `Scheme.Hom.resLE_comp_ι`, and the second is the chart equation of
   `VectorBundleZeroSection.affineChart_spec Z c V.𝓔 U`. -/
theorem zeroSection_spec (V : FieldVectorBundle K Z hZ c) :
    V.zeroSection ≫ V.p = 𝟙 Z ∧ IsClosedImmersion V.zeroSection ∧
    ∀ U : Z.affineOpens,
      ∃ zU : U.1.toScheme ⟶
          ((@VectorBundleZeroSection.π Z (isNoetherian_of_locallyOfFiniteType hZ)
            c V.𝓔 V.locallyFree) ⁻¹ᵁ U.1).toScheme,
        zU ≫ ((@VectorBundleZeroSection.π Z (isNoetherian_of_locallyOfFiniteType hZ)
          c V.𝓔 V.locallyFree) ⁻¹ᵁ U.1).ι = U.1.ι ≫ V.zeroSection ≫ V.phi.hom ∧
        zU ≫ @VectorBundleZeroSection.affineChart Z
          (isNoetherian_of_locallyOfFiniteType hZ) c V.𝓔 V.locallyFree U =
          U.2.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
            (SymmetricAlgebra.algebraMapInv (R := Z.presheaf.obj (op U.1))
              (M := V.𝓔.val.obj (op U.1))).toRingHom) := by
  let : IsNoetherian Z := isNoetherian_of_locallyOfFiniteType hZ
  let := V.locallyFree
  obtain ⟨hsection, hclosed⟩ := VectorBundleZeroSection.zero_spec Z c V.𝓔
  refine ⟨?_, ?_, ?_⟩
  · rw [zeroSection, ← V.over_commutes]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hsection
  · let := hclosed
    dsimp only [zeroSection]
    infer_instance
  · intro U
    refine ⟨VectorBundleZeroSection.zeroRestricted Z c V.𝓔 U.1, ?_,
      (VectorBundleZeroSection.affineChart_spec Z c V.𝓔 U).2.2⟩
    simp only [zeroSection, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact Scheme.Hom.resLE_comp_ι _ _

end FieldVectorBundle

namespace PurityVectorBundle

variable {P : WeilConjectures.PurityFiniteSetting.{u}}
  {Z : Scheme.{u}} {hZ : Z ⟶ Spec (CommRingCat.of P.field.k)}
  [IsSeparated hZ] [LocallyOfFiniteType hZ] [QuasiCompact hZ] {c : ℕ}

/-- The zero sections agree under `equivField`.
Source: def-pur-vector-bundle-zero-section (blueprint: def-pur-vector-bundle-zero-section).
Proof: both sides unfold to `VectorBundleZeroSection.zero Z c V.𝓔 ≫ V.phi.inv`, since
`equivField` copies every field; `rfl`. -/
theorem equivField_zeroSection (V : PurityVectorBundle P Z hZ c) :
    (equivField V).zeroSection = V.zeroSection := by
  rfl

end PurityVectorBundle

end AlgebraicGeometry
