module

public import Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Sheaf.AlgebraicGeometry.FinitePresentationFamilyDescent
import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import WeilConjectures.AlgebraicGeometry.DescendFiniteLocallyFree
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-! # Relative object descent for finite Hilbert groupoids

Source: Stacks Project, criteria.tex, Tag 06CH (lemma-limit-preserving), with the
relative object-descent convention of Tag 06CX
(blueprint: lem-sfb-relative-finite-hilbert-limit-descent).

We use the total-category convention of `RelativeFiniteHilbert.Hom`. In a category
fibred in groupoids, an arrow over `q` is exactly an isomorphism to the pullback
along `q`. Thus `γ` encodes the prescribed isomorphism to the restriction of `yᵢ`.
The Hilbert arrow `a` encodes the inverse of the requested isomorphism from the
restriction of `ξⱼ` to `ξ`, while `b` encodes the requested target isomorphism.
The equation `a.b ≫ b = γ` is precisely the prescribed compatibility square.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RelativeFiniteHilbert

/-- Relative object descent, retaining the prescribed target comparison.
Source: Stacks Project, criteria.tex, Tags 06CH and 06CX
(blueprint: lem-sfb-relative-finite-hilbert-limit-descent).

Proof:
1. Restrict to the cofinal directed tail above i; a cone on this tail extends by
choosing common upper bounds, so its limit is unchanged.
2. Write ξ=(Z→T,y,x,α). Replace y by yᵢ|T and α by αγ⁻¹|Z. The resulting Hilbert
object is isomorphic to ξ with target component γ⁻¹. The representative R identifies
(x,αγ⁻¹|Z) with the map Z→X_yᵢ, by the represented-fibre equivalence and Yoneda
(def-sfb-relative-finite-hilbert-groupoids, lem-pc-yoneda, def-trf-algebraic-space).
3. The affine limit T is qcqs; the finite cover Z is affine and its locally finitely
presented map to T is of finite presentation. Descend this one-member family to a
finite-presentation model Z_k→T_k (lem-weil-pbc-limit-affine-transition,
lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-finite-morphism-permanence,
lem-weil-pbc-qcqs-morphism-permanence, lem-weil-pbc-finite-presentation-family-descent).
4. Enlarge k until the cover is finite locally free of degree d. All later base
changes retain this property and are affine; their inverse limit is Z
(lem-weil-pbc-descend-finite-locally-free, lem-weil-pbc-finite-morphism-permanence,
lem-weil-pbc-flat-morphism-base-change, lem-weil-pbc-qcqs-morphism-permanence,
lem-weil-pbc-finite-flat-rank-iso, lem-weil-pbc-scheme-over-limit).
5. The locally finitely presented representing space over T_i admits descent of
the map Z→X_yᵢ to some Z_j, without any qcqs assumption on that space
(lem-sfb-lfp-space-scheme-limit-test).
6. Evaluate the representing equivalence at Z_j to reconstruct x_j and α_j. Full
faithfulness lifts equality of the represented maps to the compatible isomorphism
of Hilbert objects. Compose with the normalization from step 2. Its target component
is γ⁻¹, while the comparison to y_i is the identity. In total-category notation
this gives a.b ≫ b = γ (def-sfb-relative-finite-hilbert-groupoids). -/
theorem relativeFiniteHilbert_limit_descent
    {S : Scheme.{u}} {X : BasedCategory.{v₁, w₁} (Over S)}
    {Y : BasedCategory.{v₂, w₂} (Over S)} (F : BasedFunctor X Y)
    (_hX : IsFppfModuliStack X) (_hY : IsFppfModuliStack Y)
    (R : ∀ (T : Over S) (y : Functor.Fiber Y.p T), Representative (F := F) T y)
    (_hlfp : ∀ (T : Over S) (y : Functor.Fiber Y.p T),
      SpaceProperty (fun _ _ f ↦ LocallyOfFinitePresentation f) (R T y).projection)
    (d : ℕ+) (I : Type u) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Over S) (c : Cone D) (_hc : IsLimit c)
    [∀ i : I, IsAffine (D.obj (op i)).left]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f).left]
    (i : I) (yᵢ : Functor.Fiber Y.p (D.obj (op i)))
    (ξ : Fiber (F := F) (d := d) c.pt) (γ : ξ.val.y.val ⟶ yᵢ.val)
    (_hγ : Y.p.IsHomLift (c.π.app (op i)) γ) :
    ∃ (j : I) (hij : i ≤ j) (ξⱼ : Fiber (F := F) (d := d) (D.obj (op j)))
      (a : ξ.val ⟶ ξⱼ.val) (b : ξⱼ.val.y.val ⟶ yᵢ.val),
      (base (F := F) (d := d)).IsHomLift (c.π.app (op j)) a ∧
      Y.p.IsHomLift (D.map (homOfLE hij).op) b ∧ a.b ≫ b = γ := by
  sorry

end AlgebraicGeometry.RelativeFiniteHilbert
