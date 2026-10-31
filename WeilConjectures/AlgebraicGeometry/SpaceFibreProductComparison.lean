/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import WeilConjectures.AlgebraicGeometry.MonomorphismFiniteTypeComposite

/-! # Comparison of fibre products over different algebraic-space bases

Source: Stacks Project, Morphisms of Spaces, Tag 03KN
(lemma-fibre-product-after-map), clauses (1) and (4)
(blueprint: lem-sfb-space-fibre-product-comparison).

`pullback.mapDesc` is the canonical comparison, with the two original projections
as components. The pullbacks are formed in fppf sheaves, and the existing fibre-product
closure theorem makes them algebraic spaces. Representable properties are expressed
using the existing scheme-test predicate `IsRepresentableWith`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The comparison of fibre products is representable, injective on every scheme's
sections, locally of finite type, separated and locally quasi-finite. If the diagonal
of the map between the bases is quasi-compact on scheme tests, so is the comparison.
Source: Stacks Project, Morphisms of Spaces, Tag 03KN, clauses (1) and (4)
(blueprint: lem-sfb-space-fibre-product-comparison).

Proof:
1. Put `P = A ×_Z B`, `Q = A ×_T B`, and `W = Z ×_T Z`. Fibre products are
   algebraic spaces by lem-trf-space-fibre-products-etale-covers. The comparison keeps
   the pair of sections, hence is injective. The map `Q → W` sends `(a,b)` to
   `(f(a),g(b))`. The formulas `(a,b) ↦ ((a,b),f(a))` and `((a,b),z) ↦ (a,b)`
   identify `P` with `Q ×_W Z`, compatibly with restriction and projection to `Q`.
2. Given a scheme `C → Q`, compose with `Q → W`. Apply
   lem-sfb-space-diagonal-scheme-tests to `h : Z → T` and this test. Its representing
   scheme `D_C → C` is locally of finite type and monic. Step 1 identifies it with
   the scheme test of the comparison, proving representability and local finite type.
3. Apply lem-trf-monomorphism-finite-type-composite-lqf to `D_C → C → C`, with
   second arrow the identity. The locally finite type monomorphism is locally
   quasi-finite in the affine-neighbourhood sense of pqf-def-quasifinite.
4. Sectionwise injectivity makes the two projections `P ×_Q P → P` equal. The
   diagonal and the first projection are inverse by the fibre-product universal
   property. Every scheme test of this diagonal is therefore an identity, a closed
   immersion by def-weil-closed-immersion. This is the asserted separatedness.
5. If the diagonal of `h` is quasi-compact, the affine scheme test `C → Q → W`
   has quasi-compact source `Z ×_W C`. Step 1 identifies this with `P ×_Q C`.
   This is exactly quasi-compactness of the comparison. Scheme quasi-compactness
   is tested over affine opens, so the assertion is equivalently expressed by
   `IsRepresentableWith` and the scheme predicate `QuasiCompact`. -/
theorem fibreProduct_comparison_properties {S : Scheme.{u}}
    (A B Z T : AlgebraicSpace S) (f : A ⟶ Z) (g : B ⟶ Z) (h : Z ⟶ T) :
    IsRepresentable (pullback.mapDesc f.hom g.hom h.hom).hom ∧
    (∀ C : Over S,
      Function.Injective ((pullback.mapDesc f.hom g.hom h.hom).hom.app (op C))) ∧
    IsRepresentableWith (fun _ _ p ↦ LocallyOfFiniteType p.left)
      (pullback.mapDesc f.hom g.hom h.hom).hom ∧
    IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (pullback.diagonal (pullback.mapDesc f.hom g.hom h.hom).hom) ∧
    IsRepresentableWith (fun _ _ p ↦ Scheme.Hom.IsLocallyQuasiFinite p.left)
      (pullback.mapDesc f.hom g.hom h.hom).hom ∧
    (IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)
      (pullback.diagonal h.hom.hom) →
      IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)
        (pullback.mapDesc f.hom g.hom h.hom).hom) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
