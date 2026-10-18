/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Sheaf.AlgebraicGeometry.PullbackConstantModule
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.Paper.ProjectionMateExact
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.Algebra.Homology.ComplexColimitHomotopyColimit
import Sheaf.AlgebraicGeometry.EtaleDerivedTensorDirectSums

/-!
# Constant coefficient tensor comparison for an open immersion

Source: Weil conjectures blueprint, sec-smooth-purity/sk-prop-a1-kummer,
lemma lem-exc-constant-tensor (blueprint: lem-exc-constant-tensor).

The comparison is the existing unbounded projection-formula morphism at the constant
module sheaf in degree zero. Its target is identified with the tensor by the constant
module on the source through the canonical constant inverse-image isomorphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- If the unbounded derived direct image of an open immersion preserves countable
coproducts, its canonical projection-formula map is invertible at every finite constant
module over a finite commutative coefficient ring. Here the second argument is `N_T[0]`;
the canonical constant inverse-image isomorphism identifies its derived inverse image
with `N_U[0]`, so this is precisely `(Rj_*K) tensor^L N_T → Rj_*(K tensor^L N_U)`.

Source: blueprint sec-smooth-purity/sk-prop-a1-kummer/lem-exc-constant-tensor.md
(blueprint: lem-exc-constant-tensor).

Proof plan:
1. Put M₀ = N. For each finite Mᵣ take the finite free module A^(Mᵣ) mapping its basis
   vector eₓ to x, and let Mᵣ₊₁ be its kernel. Finiteness of A makes every kernel finite.
   The surjections and kernel inclusions form a finite-free resolution P → N[0] in
   nonpositive degrees, with no finite-projective-dimension assumption.
2. Exact constant sheafification gives resolutions P_T → N_T[0] and P_U → N_U[0].
   The canonical constant inverse-image isomorphisms commute with every differential
   and augmentation: both adjuncts send a constant section x to its image under the
   corresponding module homomorphism. Thus they agree by sheafification's universal
   property (lem-kun-pullback-constant and def-weil-pbc-sheafification).
3. For fixed K write F(L) = Rj_*K tensor^L L and G(L) = Rj_*(K tensor^L j⁻¹L).
   The canonical projection mate is natural, exact, shift-compatible, and the identity
   at A_T under unit identifications (lem-weil-pbc-ringed-projection-mate-exact).
   It is therefore invertible on finite sums and shifts of A_T.
4. Induct on the brutal truncations Eₘ = P_T in degrees -m through 0. The degreewise
   split short exact sequence adjoining the bottom term gives a distinguished triangle
   (lem-weil-pbc-complex-ses-triangle). The mate is a morphism of these triangles, so
   invertibility of its first and third components proves invertibility on Eₘ
   (lem-sf-triangle-morphism-iso).
5. The degreewise colimit of the Eₘ is P_T, since every degree eventually stabilizes.
   The complex-colimit telescope theorem (lem-kun-complex-colimit-hocolim) gives the
   distinguished triangle B → B → P_T → B[1], with B = ⨁ₘ Eₘ and first map 1-shift.
6. F preserves countable coproducts by lem-kun-derived-tensor-direct-sums. G does too:
   inverse image is a left adjoint (lem-weil-pbc-left-adjoint-preserves-colimits), tensor
   preserves coproducts, and Rj_* preserves them by hypothesis.
7. Naturality identifies the mate on B with the coproduct of its invertible components
   on Eₘ. Exactness and shift compatibility make the canonical mate a morphism of the
   telescope triangles, including the connecting square. The first two components
   are invertible, hence so is the component on P_T (lem-sf-triangle-morphism-iso).
8. Naturality at the augmentation isomorphism P_T ≅ N_T[0] transfers invertibility to
   N_T[0]. Under the canonical constant inverse-image isomorphism of step 2 this is
   the displayed comparison. Nothing bounds K or the length of P. -/
theorem isIso_projectionMap_finiteConstant_of_preservesCountableCoproducts
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    [PreservesColimitsOfShape (Discrete ℕ)
      (lowerStar (ModuleCat.{u + 1} A) j).rightDerivedFunctor]
    (K : DerivedCategoryModule A U) (N : ModuleCat.{u + 1} A) [Finite N] :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) j).app K).app
      ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj N))) := by
  sorry

end AlgebraicGeometry.Etale
