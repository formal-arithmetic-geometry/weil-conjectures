module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.NumberTheory.Padics.PadicIntegers
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Isogeny
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Torsion
import WeilConjectures.GroupTheory.TateModule
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Faithfulness and prime-power saturation of the Tate action

Source: Milne, Abelian Varieties, Chapter I, Remark 7.3, Proposition 10.5,
Lemmas 10.6 and 10.16, printed pp.34, 45, 49.
(blueprint: lem-sfb-abelian-tate-action-saturation)
-/

@[expose] public section

universe u

open CategoryTheory MonObj

namespace AlgebraicGeometry.IsAbelianVariety

/-- The geometric Tate action is faithful and detects divisibility by powers of the prime.
Source: Milne, Abelian Varieties, Chapter I, Remark 7.3, Proposition 10.5,
Lemmas 10.6 and 10.16, printed pp.34, 45, 49.
(blueprint: lem-sfb-abelian-tate-action-saturation)

The group `Additive (Grp.mk A ⟶ Grp.mk B)` consists exactly of group-scheme
homomorphisms, with pointwise addition. The displayed equation fixes the additive map
`iota` to the existing componentwise `tateModuleMap`, rather than an arbitrary injection.

Proof plan:
1. By lem-sc-av-commutative the target is commutative, so pointwise operations make
   Hom an abelian group. The compatible-sequence description sk-def-av-tate and
   def-tate-module-abelian-group gives the componentwise linear action and its additivity.
2. Extend to an algebraic closure (def-weil-algebraic-closure,
   lem-sfb-abelian-field-extension, def-pc-base-change). Geometric points, Tate modules
   and the action are unchanged. Apply prop-av-tate-rank and write linear maps as matrices
   to get the three finite-free identifications, including empty matrices.
3. Every finite-level torsion point lifts to a Tate sequence: recursively lift by
   multiplication using lem-sc-isogeny-surjective, and fill earlier coordinates by powers.
4. If the Tate action vanishes, every prime-power torsion point is killed. Use
   lem-sfb-simple-isogeny-decomposition over the algebraic closure. A nonzero map from a
   positive-dimensional simple factor has finite kernel: use
   lem-sfb-abelian-closed-subgroup-reduced-component and
   lem-sc-abelian-variety-characterization to rule out a full-dimensional kernel. A finite
   algebra has at most its vector-space dimension many geometric points, by interpolation.
   This contradicts the unbounded torsion counts of lem-sc-ntorsion-etale. Thus the map
   vanishes on every factor, and hence after the product isogeny, also for an empty product.
5. By lem-sc-isogeny-degree and def-sc-isogeny the product isogeny is finite flat
   surjective, hence fpqc (def-weil-finite-integral-morphism,
   def-weil-pbc-fpqc-covering). Cancel it by lem-weil-pbc-fpqc-representable-descent.
   Cancel the field-extension cover as well, using lem-pc-field-extension-fpqc-cover and
   lem-galois-fpqc-covering-base-change. Applying this to a difference gives injectivity.
6. If the Tate map is divisible by `ℓ ^ n`, lifting an `ℓ ^ n`-torsion point to a Tate
   sequence shows its image is zero. Over the algebraic closure apply
   lem-sfb-abelian-torsion-kernel-divisibility to factor through multiplication
   (def-sc-mult-n), obtaining a unique homomorphism there.
7. Multiplication over the original field is finite flat and surjective by
   lem-sc-mult-n-finite-flat and lem-sc-mult-n-isogeny, hence fpqc. Its base change is
   still a cover, even over the possibly nonreduced field-extension overlap. Cancelling
   multiplication there by representable descent makes the two pullbacks of the factor equal.
8. Descend the factor by lem-weil-pbc-fpqc-representable-descent. Its base-map, group-law,
   unit and inverse equations hold after fpqc covers and therefore hold over the original
   field; use def-sc-group-scheme and lem-galois-fpqc-covering-base-change.
9. Cancel the field cover once more to obtain `g ∘ [ℓ ^ n] = f`. On every test scheme,
   the homomorphism law identifies this with `f = ℓ ^ n • g`. If either variety is zero,
   take `g = 0`; all the preceding empty-product and rank-zero cases apply. -/
theorem tate_action_saturation
    (K : Type u) [Field K] (A B : Over (Spec (.of K)))
    [GrpObj A] [IsAbelianVariety A] [GrpObj B] [IsAbelianVariety B]
    (ℓ : ℕ) [Fact ℓ.Prime] (p : ℕ) [CharP K p] (hℓ : ℓ ≠ p) :
    Nonempty (tateModule ℓ A ≃ₗ[ℤ_[ℓ]] (Fin (2 * dim A) → ℤ_[ℓ])) ∧
      Nonempty (tateModule ℓ B ≃ₗ[ℤ_[ℓ]] (Fin (2 * dim B) → ℤ_[ℓ])) ∧
      Nonempty ((tateModule ℓ A →ₗ[ℤ_[ℓ]] tateModule ℓ B) ≃ₗ[ℤ_[ℓ]]
        (Fin (4 * dim A * dim B) → ℤ_[ℓ])) ∧
      ∃ iota : Additive (Grp.mk A ⟶ Grp.mk B) →+
          (tateModule ℓ A →ₗ[ℤ_[ℓ]] tateModule ℓ B),
        (∀ f : Additive (Grp.mk A ⟶ Grp.mk B), iota f = tateModuleMap (ℓ := ℓ) f.toMul.hom.hom) ∧
        Function.Injective iota ∧
        ∀ (f : Additive (Grp.mk A ⟶ Grp.mk B)) (n : ℕ), 1 ≤ n →
          (∃ v : tateModule ℓ A →ₗ[ℤ_[ℓ]] tateModule ℓ B,
            iota f = (ℓ : ℤ_[ℓ]) ^ n • v) →
          ∃ g : Additive (Grp.mk A ⟶ Grp.mk B), f = (ℓ ^ n) • g := sorry

end AlgebraicGeometry.IsAbelianVariety
