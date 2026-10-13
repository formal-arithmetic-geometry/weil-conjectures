/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.AlgebraicGeometry.Coherent
public import Sheaf.Paper.PQFCohomology
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Direct images of an external tensor product with an acyclic first factor

Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, acyclic base case.
(blueprint: lem-sc-picard-external-coefficients-direct-images).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

/-- The positive direct images of the external coefficients vanish, and the zeroth
is a coproduct of copies of the second coefficient. No acyclicity of G is assumed.
Source: Stacks Project, Varieties, Tag 0BED, lemma-kunneth, the paragraph beginning
"Let V be an affine open" and the displayed derived-direct-image formula.
(blueprint: lem-sc-picard-external-coefficients-direct-images).

Proof: Choose a finite affine cover U of the quasi-compact X. Affine diagonal ensures
that every nonempty finite intersection of its members is affine. On each affine open
V of Y, cover X times V by the products U_i times V. The affine fibre-product formula,
pullback-section comparison and tensor-section comparison identify its Cech complex
with Cech(U,F) tensor_k G(V), naturally under restriction of V. Finite products commute
with field tensor. Affine Cech comparison identifies its cohomology with H^p(X,F)
tensor_k G(V), since tensor over a field is exact. Hence its positive cohomology is
zero, while degree zero is Gamma(X,F) tensor_k G(V). The higher-direct-image presheaf
comparison sheafifies these compatible calculations to identify R^q pr2_* E with zero
for q>0, and R^0 pr2_* E with Gamma(X,F) tensor_k G. Choose a vector-space basis of
Gamma(X,F), indexed by a type I in universe w. The vector-space direct-sum decomposition,
tensored with G and sheafified, gives maps from G into R^0 pr2_* E which exhibit it as
the coproduct indexed by I. This is a universal property, not equality of presheaf
sections with an infinite direct sum: sheafification is needed. If Gamma(X,F) is zero,
I is empty and the coproduct is the zero sheaf. Empty schemes and G=0 are included.
The existential witnesses are used only in propositions, never to define an object. -/
theorem picardExternalCupCoefficients_directImages
    (k : Type w) [Field k] (X Y : Scheme.{w})
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [IsAffineHom (pullback.diagonal f)]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (hF : ∀ p : ℕ, 0 < p →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace p).obj F)) :
    (∀ q : ℕ, 0 < q →
      IsZero (((RingedSpace.moduleDirectImage
        (pullback.snd f g).toLRSHom.toShHom).rightDerived q).obj
          (externalCupCoefficients f g F G))) ∧
    ∃ (I : Type w)
      (ι : ∀ _ : I, G ⟶ ((RingedSpace.moduleDirectImage
        (pullback.snd f g).toLRSHom.toShHom).rightDerived 0).obj
          (externalCupCoefficients f g F G)),
      Nonempty (IsColimit (Cofan.mk _ ι)) := by sorry

end AlgebraicGeometry.Scheme.Modules
