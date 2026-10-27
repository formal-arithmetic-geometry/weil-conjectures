/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.DensePoints
import Sheaf.AlgebraicGeometry.AffineSpaceInvertibleTrivial
import Sheaf.AlgebraicGeometry.RegularSpaceDivisorLineDictionary

/-! # Picard groups of products with a proper variety containing an affine cell

Source: Stacks Project, Chow Homology, Tags 02TT and 02RX, and Divisors,
Tag 0BE9; the product boundary-divisor argument extending Milne, Algebraic Groups,
Lemma 18.21, printed p.392 (blueprint: lem-sfb-affine-cell-picard-product).

The existing Picard groups use multiplicative notation for tensor product.
For two abelian groups their product is also their direct sum.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

/-- Tensor pullback along the product projections splits the Picard group when the
proper factor contains a dense affine cell, including the prescribed rational-fibre clause.
Source: Stacks Project, Chow Homology, Tags 02TT, 02RX, and Divisors, Tag 0BE9;
Milne, Algebraic Groups, Lemma 18.21, printed p.392, with the product boundary argument
(blueprint: lem-sfb-affine-cell-picard-product).

Proof:
1. Smoothness makes X and T regular and locally Noetherian
   (lem-weil-pbc-smooth-scheme-over-field-regular). Properness of X and finite type
   and separatedness of T make both Noetherian and absolutely separated
   (lem-weil-pbc-qcqs-over-affine, lem-sc-separated-over-affine-scheme-separated).
   Smoothness gives local finite presentation (lem-pc-smooth-flat). The cell origin
   gives x₀ in X(F), and lem-pc-rational-points-dense gives t* in T(F).
2. The product W has smooth, flat, finitely presented, universally open projections
   (lem-pc-proper-base-change, lem-pc-smooth-flat, lem-weil-pbc-flat-lfp-open,
   lem-weil-pbc-qcqs-morphism-permanence). Separatedness and finite type follow by
   base change and composition (lem-pod-separated-finite-type-base-change,
   lem-sfb-finite-type-composition-base-change). Apply
   lem-sfb-smooth-integral-fibre-vertical-divisors to W → X and U to get regularity,
   local Noetherianity and density of A = U × T. Apply
   lem-sfb-integral-pullback-geometric-flat-open to get integrality of W.
3. Identify A with affine d-space over T. Its polynomial charts give separatedness
   and finite presentation, and sbc-lem-affine-space-smooth gives smoothness. Fibres
   are nonempty integral affine spaces. The same vertical-divisor and integral
   pullback lemmas make A regular, locally Noetherian and integral; the finite
   affine cover inherited from T makes A quasi-compact.
4. Product diagonals show W and A separated over F, hence absolutely separated by
   lem-sc-separated-over-affine-scheme-separated. Their finite type and local
   Noetherianity give Noetherianity. Thus A and W have the divisor dictionary.
5. For any invertible H on W, lem-sfb-affine-space-invertible-trivial trivializes
   its restriction to the generic fibre of A → T. Apply
   lem-sfb-smooth-generic-trivial-line-descent to obtain N on T with H|A ≅ q* N.
   The twist H' = H tensor (p_T* N) inverse is trivial on A. Local rank-one bases
   verify invertibility of tensor products, duals and pullbacks.
6. Its trivialization gives a rational section of H'. By
   lem-sfb-regular-space-divisor-line-dictionary its divisor D_W is supported
   outside A and H' ≅ O(D_W). The supported-divisor isomorphism of
   lem-sfb-smooth-integral-fibre-vertical-divisors gives D_W = p_X* D_X.
   The dictionary's flat-pullback compatibility gives H' ≅ p_X* O(D_X).
   Therefore every H is p_X* M tensor p_T* N.
7. Pullback respects tensor product by the balanced tensor identities of
   def-pc-module-pullback. Hence the displayed class map is a homomorphism, and
   step 6 makes it surjective.
8. Restrict a trivial external tensor product along (id_X,t*) and (x₀,id_T).
   Composition of pullbacks and triviality of any one-dimensional F-vector space
   show first M and then N trivial. This proves injectivity and the group isomorphism.
9. For the final clause restrict the decomposition from step 6 along (id_X,t₀).
   Trivialize the fibre of N at t₀, obtaining M ≅ L, and substitute this into
   the external tensor decomposition. -/
theorem affineCellPicardProduct
    (F : Type u) [Field F] [IsAlgClosed F]
    (X T : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of F))
    (g : T ⟶ Spec (CommRingCat.of F))
    [Smooth f] [IsProper f] [GeometricallyIntegral f]
    [Smooth g] [GeometricallyIntegral g] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g]
    (d : ℕ) (U : X.Opens) (hU : Dense (U : Set X))
    (cell : U.toScheme ≅ AffineSpace (ULift.{u} (Fin d)) (Spec (CommRingCat.of F)))
    (hcell : cell.hom ≫ (AffineSpace (ULift.{u} (Fin d))
      (Spec (CommRingCat.of F)) ↘ Spec (CommRingCat.of F)) = U.ι ≫ f) :
    ∃ e : (X.Pic × T.Pic) ≃* (pullback f g).Pic,
      (∀ (M : X.Pic) (N : T.Pic),
        e (M, N) = Scheme.Pic.map (pullback.fst f g) M *
          Scheme.Pic.map (pullback.snd f g) N) ∧
      (∀ (t₀ : Spec (CommRingCat.of F) ⟶ T) (ht₀ : t₀ ≫ g = 𝟙 _)
        (H : (pullback f g).Modules) (L : X.Modules),
        H.IsInvertible → L.IsInvertible →
        Nonempty ((Scheme.Modules.tensorPullback
          (pullback.lift (𝟙 X) (f ≫ t₀)
            ((Category.id_comp f).trans (((Category.assoc f t₀ g).trans
              ((congrArg (f ≫ ·) ht₀).trans (Category.comp_id f))).symm)))).obj H ≅ L) →
        ∃ N : T.Modules, N.IsInvertible ∧
          Nonempty (H ≅ (Scheme.Modules.tensorPullback (pullback.fst f g)).obj L ⊗
            (Scheme.Modules.tensorPullback (pullback.snd f g)).obj N)) := by
  sorry

end AlgebraicGeometry
