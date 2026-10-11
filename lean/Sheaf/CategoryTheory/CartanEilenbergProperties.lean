/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Sheaf.CategoryTheory.DoubleComplexTotal
import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Cartan--Eilenberg resolution properties

Source: Stacks Project, Definition 13.21.1 (015H) and Lemma 13.21.2 (015I)
(blueprint: lem-sp-cartan-eilenberg-properties).

The first index is the resolution degree. Negative resolution degrees vanish;
restriction to natural degrees lets us use Mathlib's `InjectiveResolution` directly.
Kernel and image complexes are taken in the abelian category of cochain complexes.
-/

universe v u v' u'

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HomologicalComplex₂

/-- Cartan--Eilenberg resolutions commute with left exact additive functors on vertical
cohomology, and their vertical cohomology rows resolve the cohomology of the augmentation.
Source: Stacks 015H and the construction in 015I
(blueprint: lem-sp-cartan-eilenberg-properties).

Proof: (1) Exchange the indices in Definition 015H. Rows resolve the terms of `K`;
the kernel, image and homology rows resolve its cycles, boundaries and homology
[def-sp-double-complex-total, def-sp-injective-resolutions].
(2) At every fixed first degree the cycles and boundaries are injective, by the kernel
and image resolution hypotheses. The split short exact sequences defining cohomology
are therefore preserved by `G`. Apply [lem-sp-cart-eilenberg-left-exact-cohomology]
to each bounded-below column, using [def-sp-left-exact-additive], to identify its
cohomology after applying `G` with `G` of its cohomology.
(3) Condition (6) of 015H is exactly the asserted injective resolution of `K.homology q`,
with the differential induced by the first differential [def-sp-injective-resolutions]. -/
theorem cartanEilenberg_properties
    {B : Type u} [Category.{v} B] [Abelian B] [EnoughInjectives B]
    {A : Type u'} [Category.{v'} A] [Abelian A]
    (K : CochainComplex B ℤ)
    (C : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    (a : K ⟶ C.X 0)
    (hK : ∃ i : ℤ, ∀ q : ℤ, q < i → IsZero (K.X q))
    (hbelow : ∃ i : ℤ, ∀ p q : ℤ, q < i → IsZero ((C.X p).X q))
    (hnegative : ∀ p q : ℤ, p < 0 → IsZero ((C.X p).X q))
    (G : B ⥤ A) [G.Additive] [PreservesFiniteLimits G] :
    let P := C.restriction ComplexShape.embeddingUpNat
    let R := HomologicalComplex₂.flip P
    ∀ (hrows : ∀ q : ℤ, ∃ (I : InjectiveResolution (K.X q))
      (e : I.cocomplex ≅ R.X q),
      (singleObjXSelf (ComplexShape.up ℕ) 0 (K.X q)).inv ≫
        I.ι.f 0 ≫ e.hom.f 0 = a.f q)
    (hcycles : ∀ q : ℤ, ∃ (I : InjectiveResolution (K.cycles q))
      (e : I.cocomplex ≅ kernel (R.d q (q + 1))),
      (singleObjXSelf (ComplexShape.up ℕ) 0 (K.cycles q)).inv ≫
        I.ι.f 0 ≫ e.hom.f 0 ≫ (kernel.ι (R.d q (q + 1))).f 0 =
        K.iCycles q ≫ a.f q)
    (hboundaries : ∀ q : ℤ, ∃ (I : InjectiveResolution (image (K.d q (q + 1))))
      (e : I.cocomplex ≅ image (R.d q (q + 1))),
      (singleObjXSelf (ComplexShape.up ℕ) 0 (image (K.d q (q + 1)))).inv ≫
        I.ι.f 0 ≫ e.hom.f 0 ≫ (image.ι (R.d q (q + 1))).f 0 =
        image.ι (K.d q (q + 1)) ≫ a.f (q + 1))
    (hhomology : ∀ q : ℤ, ∃ (I : InjectiveResolution (K.homology q))
      (e : I.cocomplex ≅
        ((homologyFunctor B (ComplexShape.up ℤ) q).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj P),
      (singleObjXSelf (ComplexShape.up ℕ) 0 (K.homology q)).inv ≫
        I.ι.f 0 ≫ e.hom.f 0 = homologyMap a q),
    (∀ p q : ℤ, Nonempty
      ((((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (C.X p)).homology q) ≅
        G.obj ((C.X p).homology q))) ∧
    (∀ q : ℤ, ∃ (I : InjectiveResolution (K.homology q))
      (e : I.cocomplex ≅
        ((homologyFunctor B (ComplexShape.up ℤ) q).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj P),
      (singleObjXSelf (ComplexShape.up ℕ) 0 (K.homology q)).inv ≫
        I.ι.f 0 ≫ e.hom.f 0 = homologyMap a q) := by
  sorry

end HomologicalComplex₂
