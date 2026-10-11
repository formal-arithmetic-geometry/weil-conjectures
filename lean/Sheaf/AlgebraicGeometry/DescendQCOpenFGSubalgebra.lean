/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.PicardFunctor

/-!
# Descent of quasi-compact opens to finitely generated subalgebras

Source: Stacks Project, Varieties, Tag 0388 (`lemma-descend-open`)
(blueprint: lem-weil-pbc-descend-qc-open-fg-subalgebra).
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A quasi-compact open in a base change to an algebra descends to a finitely generated
subalgebra. Source: Stacks Project, Tag 0388.
(blueprint: lem-weil-pbc-descend-qc-open-fg-subalgebra).

Proof:
1. Cover `V` by the base changes of finitely many affine opens `U_i = Spec R_i` of `X`,
   using the affine-open basis and quasi-compactness. These are open subschemes of the
   base change by `lem-weil-pbc-open-fibre-product`.
2. Identify these affine base changes with `Spec (R_i ⊗[k] A)` by
   `lem-weil-pbc-fibre-product-affine-spectra`. Their principal opens form a basis;
   quasi-compactness of `V` gives finitely many `D(f_ij)` whose union is `V`.
   This does not require the intersections of `V` with the affine charts to be compact.
3. Generate `A'` by the finitely many coefficients in all the tensors `f_ij`.
   Lift each tensor to `f'_ij` over `A'`. Their principal opens have finite union `V'`,
   which is open and quasi-compact.
4. The canonical map `π` restricts on each chart to the spectrum of the tensor map
   induced by the inclusion, using `lem-weil-pbc-open-fibre-product` and
   `lem-weil-pbc-fibre-product-affine-spectra`. The inverse image of each `D(f'_ij)`
   is `D(f_ij)`. Thus `π(V) ⊆ V'`; conversely a point whose image belongs to `V'`
   lies in some `D(f_ij)`, and hence in `V`. This gives `V = π ⁻¹ᵁ V'`. -/
theorem descend_qc_open_fg_subalgebra (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) (A : Type u) [CommRing A] [Algebra k A] :
    ∀ (V : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))).Opens),
      IsCompact V.1 →
      ∃ (A' : Subalgebra k A), A'.FG ∧
        ∃ (V' : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A')))).Opens),
          IsCompact V'.1 ∧
          ∃ (π : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A)))) ⟶
              (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k A')))) ),
            π = baseChangeMap f
              (Over.homMk (Spec.map (CommRingCat.ofHom (Subalgebra.val A')))
                (by
                  change Spec.map (CommRingCat.ofHom (Subalgebra.val A')) ≫
                      Spec.map (CommRingCat.ofHom (algebraMap k A')) =
                    Spec.map (CommRingCat.ofHom (algebraMap k A))
                  rw [← Spec.map_comp]
                  congr 1
                  ) :
                  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A))) ⟶
                    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k A')))) ∧
            V = (π ⁻¹ᵁ V')  := by sorry

end AlgebraicGeometry
