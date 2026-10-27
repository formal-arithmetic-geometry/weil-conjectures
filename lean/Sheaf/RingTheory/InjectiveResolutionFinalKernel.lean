module

public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs

import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.Algebra.Category.ModuleCat.Injective

/-!
# The final kernel of an injective resolution

Source: Stacks Project, More on Algebra, Tag 0A5T, proof of (3) implies (1),
with the ideal-extension test of Tag 0AVF and the Ext computation of Tag 06XR
(blueprint: lem-trf-injective-resolution-final-kernel).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

/-- The degree `d` kernel in the given injective resolution is injective when
`Ext^{d+1}(R/T,N)` vanishes for every ideal `T`.

Source: Stacks Project, More on Algebra, Tag 0A5T, proof of (3) implies (1)
(blueprint: lem-trf-injective-resolution-final-kernel).

Proof: Fix an ideal `T` and a linear map `f : T → J`, where `J` is this kernel.
By degreewise injectivity, extend the composite `T → J → I^d` to `a : R → I^d`
(`def-sp-injective-resolutions`, `lem-weil-pbc-ring-modules-enough-injectives`).
The differential of `a` vanishes on `T`, hence descends to a cocycle
`α : R/T → I^{d+1}`. The complex identity makes its next differential zero.
The Ext computation `lem-weil-pbc-ext-via-injective-resolution` (Tag 06XR),
applied to this augmented exact resolution, and the assumed Ext vanishing give
`b : R/T → I^d` whose differential is `α`. If `q : R → R/T` is the quotient map,
then `a - bq` has zero differential and restricts to `f` on `T`. It therefore
corestricts to an extension `R → J`. Baer's criterion `lem-sf-baer-criterion`
(Tag 0AVF) now gives injectivity of `J`. All modules use the common universe `u`.
-/
theorem injective_kernel_of_ext_ideal_quotient_eq_zero
    (R : Type u) [CommRing R] (N : ModuleCat.{u} R)
    (I : CochainComplex (ModuleCat.{u} R) ℤ) (ε : N ⟶ I.X 0)
    (hneg : ∀ j : ℤ, j < 0 → IsZero (I.X j))
    (hinj : ∀ j : ℤ, Injective (I.X j))
    (hε : Function.Injective ε.hom)
    (hexact₀ : Function.Exact ε.hom (I.d 0 1).hom)
    (hexact : ∀ j : ℤ, 0 < j →
      Function.Exact (I.d (j - 1) j).hom (I.d j (j + 1)).hom)
    (d : ℤ) (hd : 0 ≤ d)
    (hExt : ∀ T : Ideal R,
      Subsingleton (Abelian.Ext (ModuleCat.of R (R ⧸ T)) N (d.toNat + 1))) :
    Injective (kernel (I.d d (d + 1))) := by
  sorry

end ModuleCat
