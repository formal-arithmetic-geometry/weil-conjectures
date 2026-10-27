/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.RelativeFiniteHilbertGroupoids
public import WeilConjectures.AlgebraicGeometry.Thickening
import Sheaf.AlgebraicGeometry.AffineLciConormalSplitting
import Sheaf.AlgebraicGeometry.SpaceUniversalConormal
import Sheaf.AlgebraicGeometry.SpaceChangeBase

/-! # Compatible affine lifts in the unramified lci Hilbert locus

Source: Stacks Project, criteria.tex, Tags 06D8 and 06D9
(blueprint: lem-sfb-relative-finite-hilbert-lci-lift).

We use total categories. An arrow `γ : y₀ → y'` over `i` is precisely an
isomorphism `y₀ ≅ i* y'` since the target is fibred in groupoids. Likewise a
Hilbert arrow from `ξ₀` to `ξ'` over `i` specifies the inverse of the requested
isomorphism `i* ξ' ≅ ξ₀`, including its cartesian square of finite schemes.
The equation `a.b ≫ b.hom = γ` is the compatibility of these isomorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.RelativeFiniteHilbert

/-- Compatible square-zero lifts in the unramified lci locus, without surjectivity.
Source: Stacks Project, criteria.tex, Tag 06D9, using Tag 06D8
(blueprint: lem-sfb-relative-finite-hilbert-lci-lift).

Proof:
1. Write the given object as (Z₀, p₀, y₀, x₀, α₀). Use γ to regard its
   comparison as lying over the restriction of y'. In the representing space
   X' = X_{y'}, this gives the specified unramified lci map Z₀ → X₀. The finite
   locally free morphism p₀ has affine source because its base is affine.
2. Put J = ker(O_{T'} → O_{T₀}). By
   lem-sfb-space-square-zero-flatness-criterion, the conormal of X₀ in X' is
   the pullback of J. Apply lem-sfb-affine-lci-conormal-splitting and
   lem-sfb-space-universal-conormal to split C_{Z₀/X'} as p₀*J ⊕ C_{Z₀/X₀}.
   Identify the iterated tensor pullback with p₀*J by multiplying tensors.
3. Take the universal first-order thickening W of Z₀ over X'. Quotient its
   square-zero ideal by the second summand. The quotient ring sheaf is an
   extension of O_{Z₀} by p₀*J. Apply
   lem-sfb-scheme-etale-square-zero-chart-construction to realize it as a
   scheme Z' with its entire etale ring sheaf and the prescribed reduction.
4. The quotient map O_W → O_{Z'} is local: a section is invertible exactly
   when its residue modulo a square-zero ideal is invertible. Apply
   lem-sfb-space-locally-ringed-etale-topos-reconstruction, after
   lem-sfb-space-change-base-to-integers, to obtain Z' → W → X'. Faithfulness
   identifies its reduction with the original map Z₀ → X₀.
5. The canonical ideal map p₀*J → C_{Z₀/Z'} is the first summand followed by
   the quotient, hence an isomorphism. Apply the square-zero flatness criterion
   again to obtain flatness of Z' → T' and the cartesian reduction square.
6. Lem-sfb-finite-locally-free-deformation gives degree d for Z' → T'.
7. The map Z' → X_{y'} determines (x', α') and hence a Hilbert object. By
   lem-sfb-relative-finite-hilbert-lci-open its lci locus is an open containing
   T₀. A square-zero thickening has the same points, so this open is all of T'.
8. The cartesian reduction and the comparison supply the arrow a. Choose the
   target of the lift to be y', and b to be the identity. Its reduced target
   comparison is γ, so a.b followed by b is γ. Translating cartesian arrows
   into pullback isomorphisms gives b|_{T₀} = γ ∘ p_d(a) in the node's
   orientation. No step uses surjectivity of F.
-/
theorem exists_compatible_lci_lift
    {S : Scheme.{u}}
    {X : BasedCategory.{v₁, w₁} (Over S)} {Y : BasedCategory.{v₂, w₂} (Over S)}
    (F : BasedFunctor X Y) (hX : IsFppfModuliStack X) (hY : IsFppfModuliStack Y)
    (hF : IsRepresentableByAlgebraicSpaces F)
    (R : ∀ (T : Over S) (y : Functor.Fiber Y.p T), Representative (F := F) T y)
    (hflat : FlatLfp R) (d : ℕ+)
    (ξ₀ : Lci (d := d) hX hY hF R hflat)
    (T' : Over S) (i : ξ₀.obj.T ⟶ T')
    [IsAffine ξ₀.obj.T.left] [IsAffine T'.left]
    (hi : IsFirstOrderThickening i.left)
    (y' : Functor.Fiber Y.p T') (γ : ξ₀.obj.y.val ⟶ y'.val)
    (hγ : Y.p.IsHomLift i γ) :
    ∃ (ξ' : Lci (d := d) hX hY hF R hflat)
      (a : ξ₀.obj ⟶ ξ'.obj) (b : ξ'.obj.y.val ≅ y'.val),
      (base (F := F) (d := d)).IsHomLift i a ∧
      Y.p.IsHomLift (𝟙 T') b.hom ∧ a.b ≫ b.hom = γ := by
  sorry

end AlgebraicGeometry.RelativeFiniteHilbert
