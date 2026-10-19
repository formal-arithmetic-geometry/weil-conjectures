/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.AlgebraicGeometry.ConstructibleSurjectivePullback
import Sheaf.AlgebraicGeometry.FiniteDenseNormalOpen
import Sheaf.AlgebraicGeometry.NormalOpenLisseImage
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.ConstructibleSubsheafNoetherian
import WeilConjectures.SixFunctors.Finite.Stalk
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Sheaf.AlgebraicGeometry.OpenImmersionRestriction
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.SecSmoothPurity.FinReductionOpenDirectImage
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Constructibility of degree-zero open direct images over a field

Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/thm-fin-open-degree-zero.md`,
statement and proof paragraphs 1–4 (blueprint: thm-fin-open-degree-zero).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The direct image of a constructible etale module sheaf under an open immersion into
 a scheme of finite type over a field is constructible, for every finite commutative
 coefficient ring.

Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/thm-fin-open-degree-zero.md`,
statement and proof paragraphs 1–4 (blueprint: thm-fin-open-degree-zero).

Proof plan:
1. Finite type over a field makes `X` Noetherian
   (`lem-weil-pbc-finite-type-over-noetherian`). Induct on closed subsets, including every
   open and every constructible sheaf in the inductive assertion. Reduction is a universal
   homeomorphism (`lem-weil-pbc-reduction-universal-homeomorphism`), so its inverse image
   is an equivalence (`thm-weil-pbc-universal-homeomorphism-invariance`). The direct-image
   formula (`def-weil-pbc-direct-image`) identifies the two composites through reduction,
   and `lem-weil-pbc-etale-constructible-surjective-pullback` preserves and reflects
   constructibility. Thus assume `X` reduced. If `U` is not dense, factor through its
   reduced closure, apply induction and then `lem-fin-closed-immersion`.
2. For nonempty reduced `X` and dense `U`, there are finitely many integral components
   (`lem-weil-pbc-noetherian-finite-components`). The constructible partition
   (`def-weil-pbc-constructible-complexes`) yields a lisse open at each generic point.
   Remove all other components and apply `lem-fin-dense-normal-open`, obtaining disjoint
   nonempty normal opens `V_a`. Put `V = coproduct V_a`, `h : V → U`, `k = jh` and
   `L = h⁻¹F` (`def-weil-pbc-inverse-image`). Each component image is constructible by
   `lem-fin-normal-open-lisse-image`; push to `X` by `lem-fin-closed-immersion`. The sheaf
   axiom and `def-weil-pbc-direct-image` identify `k_*L` with their finite product.
   The zero sheaf is lisse, and `thm-constructible-serre` gives closure under finite sums.
3. Let `K` be the kernel of the adjunction unit `F → h_*L`. It is constructible by
   `lem-weil-pbc-constructible-subobjects-noetherian`. Exact inverse image
   (`prop-weil-pbc-inverse-image-modules-exact`) and the open counit isomorphism
   (`lem-kun-open-immersion-restriction`) imply `K|V = 0`. For the reduced complement
   `W = X ∖ V`, put `W_U = W ∩ U`, with closed immersions `i : W → X`, `i' : W_U → U`
   and open immersion `j_W : W_U → W`. The sheaf `K' = i'⁻¹K` is constructible by
   `prop-constructible-pullback`. The closed immersion is finite
   (`lem-weil-pbc-closed-immersion-finite`), and its unit `K → i'_*K'` is an isomorphism:
   the finite stalk formula (`lemma-weil-pbc-finite-stalk-formula`) and unit-compatible
   inverse-image stalk identification (`lem-weil-pbc-inverse-image-stalk-germ`) give an
   isomorphism on `W_U`, while both stalks vanish off it. Apply
   `lemma-weil-pbc-geometric-stalk-conservative`; the isomorphism is coefficient-linear.
   The direct-image formula identifies `j_*K` with `i_*j_{W,*}K'`, by canonical iterated
   fibre-product isomorphisms compatible with restriction maps. The complement is proper,
   so induction and `lem-fin-closed-immersion` give constructibility of `j_*K`.
4. Left exactness (`def-weil-pbc-direct-image`) identifies `j_*K` with the kernel of
   `j_*F → j_*h_*L`. The fibre-product formula identifies `j_*h_*L` with `k_*L`.
   Its image `I` is constructible by `lem-weil-pbc-constructible-subobjects-noetherian`.
   Apply the extension clause of `thm-constructible-serre` to
   `0 → j_*K → j_*F → I → 0`. This uses only left exactness of the open direct image. -/
theorem isConstructibleEtaleModuleSheaf_lowerStar_of_openImmersion_over_field
    {k : Type u} [Field k] {X U : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModuleSheaf F) :
    IsConstructibleEtaleModuleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj F) := by
  sorry

end AlgebraicGeometry.Scheme
