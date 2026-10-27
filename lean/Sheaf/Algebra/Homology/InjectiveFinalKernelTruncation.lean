module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-! # Truncating an injective resolution at an injective final kernel

Source: Stacks Project, Tag 0A5T, proof of (3) implies (1), the complex ending in `J`.
(blueprint: lem-trf-injective-final-kernel-truncation)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace CochainComplex

/-- An augmented injective resolution can be cut off at an injective final kernel.
Source: Stacks Project, Tag 0A5T, proof of (3) implies (1).
(blueprint: lem-trf-injective-final-kernel-truncation)

The given chain map `ε` encodes the augmentation: its degree-zero component, after
the canonical identification of the single complex with `N`, is the given map into `I.X 0`.
Its being a quasi-isomorphism, together with vanishing of negative terms of `I`, is
equivalent to exactness of the augmented sequence in the node. The isomorphisms `a` and `b`
identify the retained terms and the final kernel; all component equations use these
identifications, so they express the prescribed identities and kernel inclusion.

Proof: (1) Retain the differentials below the last degree and corestrict the last one
to the kernel. This is well defined by `d_comp_d`; the same identity proves that the
new differentials square to zero. For `d = 0` they are all zero.
(2) The identities, the kernel inclusion, and zero maps form a chain map `ι`: at the
last two degrees its equations are the corestriction identity and the kernel identity.
(3) Factor the augmentation through this complex. For `d > 0` its zero component is
unchanged; for `d = 0`, exactness identifies `N` isomorphically with the kernel.
The equation `e ≫ ι = ε` holds componentwise.
(4) Exactness of the original resolution gives zero cohomology in degrees strictly
between zero and `d`; corestriction preserves kernels. At degree `d > 0`, the image
of the preceding differential is the entire final kernel, so cohomology also vanishes.
(5) At degree zero the kernel is the image of the injective augmentation. Outside
`[0,d]` the terms vanish. Thus `e` is a quasi-isomorphism, including when `d = 0`.
(6) Retained terms are injective by assumption, the last term is injective by the
final-kernel hypothesis, and the zero terms are injective by the extension definition.
(7) The localization functor `DerivedCategory.Q` inverts `e`, yielding the displayed
derived isomorphism whose forward morphism is precisely `Q.map e`.
These steps use def-sp-injective-resolutions and def-weil-abstract-derived-category.
-/
theorem exists_injective_final_kernel_truncation
    {R : Type u} [CommRing R] (N : ModuleCat.{u} R)
    (I : CochainComplex (ModuleCat.{u} R) ℤ)
    (hneg : ∀ j : ℤ, j < 0 → IsZero (I.X j))
    (hinj : ∀ j : ℤ, Injective (I.X j))
    (ε : (single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj N ⟶ I)
    [QuasiIso ε] (d : ℤ) (hd : 0 ≤ d)
    (hJ : Injective (kernel (I.d d (d + 1))))
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    ∃ (L : CochainComplex (ModuleCat.{u} R) ℤ) (ι : L ⟶ I)
      (e : (single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj N ⟶ L)
      (a : ∀ (j : ℤ), 0 ≤ j → j < d → (L.X j ≅ I.X j))
      (b : L.X d ≅ kernel (I.d d (d + 1))),
      (∀ (j : ℤ) (hj : 0 ≤ j) (hjd : j < d), ι.f j = (a j hj hjd).hom) ∧
      ι.f d = b.hom ≫ kernel.ι (I.d d (d + 1)) ∧
      (∀ j : ℤ, j < 0 ∨ d < j → IsZero (L.X j) ∧ ι.f j = 0) ∧
      (∀ (i j : ℤ) (hi : 0 ≤ i) (hid : i < d) (hj : 0 ≤ j) (hjd : j < d),
        j = i + 1 → L.d i j ≫ (a j hj hjd).hom = (a i hi hid).hom ≫ I.d i j) ∧
      (∀ (i : ℤ) (hi : 0 ≤ i) (hid : i < d), i + 1 = d →
        L.d i d ≫ b.hom ≫ kernel.ι (I.d d (d + 1)) = (a i hi hid).hom ≫ I.d i d) ∧
      (∀ j : ℤ, ¬ (0 ≤ j ∧ j < d) → L.d j (j + 1) = 0) ∧
      e ≫ ι = ε ∧
      (∀ hpos : 0 < d, e.f 0 ≫ (a 0 (le_refl 0) hpos).hom = ε.f 0) ∧
      (d = 0 → IsIso (e.f 0)) ∧
      QuasiIso e ∧ (∀ j : ℤ, Injective (L.X j)) ∧
      ∃ η : DerivedCategory.Q.obj
          ((single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj N) ≅
          DerivedCategory.Q.obj L,
        η.hom = DerivedCategory.Q.map e := by
  sorry

end CochainComplex
