/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.CochainComplexMinus
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-!
# Functorial bounded-above resolutions from a zero-preserving left resolution

Source: `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
 sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`, first three sentences
(blueprint: lem-sfb-left-resolution-bounded-minus).
The construction is implemented by the FromJoel `LeftResolution.CochainComplexMinus`
module, using `minusResolutionFunctor` and `minusResolutionNatTrans`
(blueprint: lem-sfb-left-resolution-bounded-minus).

## Main statements

* `CochainComplex.exists_functorial_boundedAbove_left_resolution`: a functor `S` on
  `CochainComplex.Minus A` with a natural quasi-isomorphic augmentation `S ⟶ Minus.ι A`,
  termwise in the essential image of `ι`, preserving every upper bound.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

/-- A zero-preserving epimorphic left resolution gives a functorial resolution of
all bounded-above cochain complexes, preserving upper bounds termwise.

Source: `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/
sk-def-sfb-derived-tensor-hom/lem-sfb-derived-monoidal.proof.md`, first three sentences;
`WeilConjectures/FromJoel/Algebra/Homology/LeftResolution/CochainComplexMinus.lean:32-273`
(blueprint: lem-sfb-left-resolution-bounded-minus).

Proof (the node's steps):
1. Package `Q` and `π` (with `hπ`) as the left-resolution datum
   `Λ : CategoryTheory.Abelian.LeftResolution ι`; `[Q.PreservesZeroMorphisms]` is the
   zero-preservation hypothesis of `CochainComplexMinus.lean:32-36`.
2. Apply `lem-sfb-left-resolution-objectwise-cochain`: the cochain-complex resolution
   functor and its objectwise quasi-isomorphic augmentation; its complexes and their images
   under `ι` vanish in every resolution degree `q > 0` (FromJoel `LeftResolution/Basic`).
3. For bounded-above `K` choose an upper bound `b`.
   `lem-sfb-left-resolution-bicomplex-total-exists` gives the resolution bicomplex `B_K`,
   its vanishing for `p > b` and `q > 0`, and the existence of both diagonal totals.
4. Put `T(K) = Tot(B_K)` in `C` and `S(K) = ι(T(K))` termwise, `S(f) = ι(Tot(B_f))`;
   the functor laws come from those of the objectwise resolution and `total.map`. The totals
   do not depend on a bound witness, so `S` acts on every map of `CochainComplex.Minus A`.
   For `n > b` every diagonal summand of `T(K)^n` is zero (`p ≤ b`, `q ≤ 0` force
   `n ≤ b`), so `T(K)^n` and `S(K)^n` are zero; every `S(K)^n = ι(T(K)^n)` is in the
   essential image of `ι`.
5. The map `τ_K` of `lem-sfb-left-resolution-totalized-augmentation` is natural and a
   quasi-isomorphism, by the bounded-column comparison
   `lem-pc-bounded-above-double-complex-total-comparison`
   (`HomologicalComplex₂.total.quasiIso_map_of_isStrictlyGE_of_isStrictlyLE`) applied to the
   objectwise quasi-isomorphisms of step 2.
6. `lem-sfb-left-resolution-additive-total-transport` with `F = ι` (zero object and finite
   coproducts in `C`, `A` preadditive, `ι` additive, the bounds of step 3) gives the natural
   isomorphism `e_K = mapTotalIso : Tot(ι B_K) ≅ S(K)`.
7. `lem-sfb-left-resolution-single-row-total` gives the natural isomorphism
   `r_K : Tot(singleRow₀ K) ≅ K`.
8. Put `a_K = r_K ∘ τ_K ∘ e_K⁻¹ : S(K) ⟶ K`, a quasi-isomorphism as a composite of
   isomorphisms and a quasi-isomorphism; the naturality of steps 5–7 gives
   `f ∘ a_K = a_L ∘ S(f)`. Step 4 gives the essential-image and upper-bound clauses
   (FromJoel `totalπ`, `minusResolutionNatTrans`, `CochainComplexMinus.lean:216-256`). -/
theorem exists_functorial_boundedAbove_left_resolution
    {A : Type u₁} [Category.{v₁} A] [Abelian A]
    {C : Type u₂} [Category.{v₂} C] [Preadditive C]
    [HasZeroObject C] [HasFiniteCoproducts C]
    (ι : C ⥤ A) [ι.Full] [ι.Faithful] [ι.Additive]
    (Q : A ⥤ C) [Q.PreservesZeroMorphisms]
    (π : Q ⋙ ι ⟶ 𝟭 A) (hπ : ∀ (X : A), Epi (π.app X)) :
    ∃ (S : CochainComplex.Minus A ⥤ CochainComplex A ℤ)
      (a : S ⟶ CochainComplex.Minus.ι A),
      (∀ (L : CochainComplex.Minus A), QuasiIso (a.app L)) ∧
      (∀ (L : CochainComplex.Minus A) (i : ℤ),
        ∃ (X : C), Nonempty ((S.obj L).X i ≅ ι.obj X)) ∧
      (∀ (L : CochainComplex.Minus A) (b : ℤ),
        L.obj.IsStrictlyLE b → (S.obj L).IsStrictlyLE b) := by
  sorry

end CochainComplex
