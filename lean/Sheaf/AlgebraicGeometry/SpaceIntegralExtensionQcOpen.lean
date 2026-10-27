/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.SpaceOpenChartTests

/-!
# Extension of an integral algebraic space across a quasi-compact open

Source: Stacks Project, Decent Algebraic Spaces, Tag 0G2D,
`lemma-extend-integral-morphism`
(blueprint: lem-sfb-space-integral-extension-qc-open).

The open immersion and integrality are tested on schemes using `IsRepresentableWith`.
The isomorphism is between fppf sheaves and commutes with the projections to `V`.
The open immersion of `Z` into the extension is its inverse followed by the first
pullback projection, so it is the specified pullback open immersion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- An integral morphism over a quasi-compact open subspace extends to an integral
morphism over the ambient algebraic space. The inverse of the displayed isomorphism
followed by the first projection identifies `Z` with the pullback open subspace of `E`.

Source: Stacks Project, Decent Algebraic Spaces, Tag 0G2D,
`lemma-extend-integral-morphism`
(blueprint: lem-sfb-space-integral-extension-qc-open).

Proof:
1. Write `f = π ≫ j`. The integral map `π` is quasi-compact and separated by
   lem-sfb-space-integral-qcqs-permanence. The open immersion `j` is a monomorphism
   on scheme tests, so its diagonal is an isomorphism and hence a closed immersion.
   Thus `f` is separated by lem-sfb-space-separated-fp-composition.
2. For a quasi-compact scheme `T → B`, the scheme `V ×_B T` is quasi-compact by
   the quasi-compact open hypothesis. Its inverse image under the integral map is
   integral, hence affine, over it. A finite affine cover pulls back to a finite
   affine cover, proving that `Z ×_B T` is quasi-compact. Its identity gives the
   required quasi-compact scheme atlas. Thus `f` is quasi-compact.
3. Apply lem-sfb-space-relative-integral-factorization to `f`, obtaining `Z → E → B`
   with integral second map and the universal property against integral `B`-spaces.
   This is the relative normalization of Tags 0822 and 0823.
4. The open map `j` is representable étale by lem-a1-space-open-chart-tests.
   Apply lem-sfb-space-integral-factorization-etale-base-change along `j`.
   Since `j` is monic, `Z ×_B V` is canonically `Z`. The resulting factorization
   `Z → E ×_B V → V` has the same universal property over `V`.
5. Apply that property to the integral map `π` and the identity of `Z`, obtaining
   `h : E ×_B V → Z` inverse on one side to the factor map `a : Z → E ×_B V`.
   Uniqueness applied to the integral target `E ×_B V` gives `a h = id` as well.
   This yields the displayed isomorphism over `V`. The first pullback projection
   is the base change of `j`; on a scheme test it is the corresponding open
   subscheme. Transport by the isomorphism proves the final open-immersion clause.
   These arguments also apply to the empty open subspace and empty `Z`. -/
theorem exists_integral_extension_qcOpen {S : Scheme.{u}} {V B Z : AlgebraicSpace S}
    (j : V ⟶ B) (π : Z ⟶ V)
    (hj : IsRepresentableWith
      (fun _ _ p ↦ IsOpenImmersion p.left ∧ QuasiCompact p.left) j.hom.hom)
    (hπ : IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) π.hom.hom) :
    ∃ (E : AlgebraicSpace S) (ν : E ⟶ B),
      IsRepresentableWith (fun _ _ p ↦ IsIntegralHom p.left) ν.hom.hom ∧
      ∃ e : Limits.pullback ν.hom j.hom ≅ Z.obj,
        e.hom ≫ π.hom = Limits.pullback.snd ν.hom j.hom ∧
        IsRepresentableWith (fun _ _ p ↦ IsOpenImmersion p.left)
          (e.inv ≫ Limits.pullback.fst ν.hom j.hom).hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
