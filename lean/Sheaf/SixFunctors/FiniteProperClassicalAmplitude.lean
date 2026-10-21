/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.SixFunctors.ClassicalDefinition
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Limits.Shapes.Countable

import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Sheaf.Paper.FiniteDiscreteSchemeRing
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import Sheaf.AlgebraicGeometry.ProperTorsionDirectImageBound
import WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison
import Sheaf.CategoryTheory.KInjectiveComputes
import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Sheaf.SixFunctors.FiniteProperClassicalTruncation
import Sheaf.AlgebraicGeometry.FiniteCohomologicalDimensionDirectImageCoproducts

/-!
# Uniform amplitude of finite-coefficient proper direct image

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-ctf-finite-proper-localizing.proof.md, "Etale statements" and "Transfer";
Stacks Project, Tags 095U, 0D6J, 07KC, 0H72 and 0F0D
(blueprint: lem-sfb-finite-proper-classical-amplitude).

Both coefficient presentations use the canonical lift `ULift.{u + 1, u} A`.
The pro-etale category is the ordinary constant-ring module derived category;
its classicality predicate concerns all cohomology sheaves. Preservation of
products and coproducts means preservation of the canonical limiting cones and
colimiting cocones, hence of their projections and coprojections.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Total proper direct image has lower amplitude zero on every complex and upper
amplitude `2e` on complexes with classical cohomology, including those unbounded below.
It is triangulated, commutes with integer shifts and preserves countable products.
The etale higher images vanish above `2e`, and the total etale direct image preserves
all existing small ambient coproducts by their canonical comparison.

Source: blueprint main-20261015, sk-prop-ctf-finite-proper-localizing.proof.md,
"Etale statements" and "Transfer"; Stacks Tags 095U, 0D6J, 07KC, 0H72 and 0F0D
(blueprint: lem-sfb-finite-proper-classical-amplitude).

Proof plan:
1. Apply prop-pur-kinjective-resolutions-exist to the constant ring sheaves.
   The module inverse image is exact, and its right adjoint is the sectionwise
   direct image of def-weil-pbc-proetale-operations. Apply
   lem-pc-right-derived-functor-triangulated for triangulatedness and integer shifts.
   The two finite-discrete-constant lemmas identify these coefficients with the
   continuous-function coefficients of def-weil-pbc-proetale-modules and with
   comparison pullback of the etale constant coefficients.
2. Products of module sheaves are sectionwise products. By
   lem-pc-ringed-space-product-kinjective, products of K-injective representatives
   represent derived products. The derived adjunction identifies maps into the
   image of such a product with families of maps into the images. These bijections
   are induced by the images of the projections, proving canonical preservation.
3. For `L` bounded below by `a`, apply
   lem-weil-pbc-derived-functor-negative-vanishing to the left exact direct image.
   src-right-derived-functor-plus-compatibility identifies this bounded-below
   derived image with the total image, proving the same lower bound.
4. Finiteness gives a positive additive exponent annihilating `A` and every
   `A`-module. The identity base change gives the fibre bound for `f` itself.
   Apply lem-kun-proper-torsion-cd-bound and then
   lem-sbc-higher-direct-image-forget-comparison. Forgetting reflects zero objects,
   giving the etale module higher-image vanishing above `2e`.
5. Properness implies qcqs. det-pe-classical-sheaves-modules writes a classical
   sheaf as comparison pullback of an etale sheaf. Apply
   sk-thm-pe-direct-image-comparison and bounded-below compatibility to that sheaf
   in degree zero. lem-sp-kinjective-computes and step 4 bound its total image
   above by `2e`; comparison pullback is exact and commutes with cohomology.
6. The class of classical sheaves is replete and contains zero. Apply
   lem-sfb-bounded-heart-amplitude-devissage with this class and the heart bound
   from step 5 to obtain upper bound `b + 2e` for bounded classical complexes.
7. For arbitrary classical `L` bounded above by `b`, fix `m > b + 2e` and put
   `N = min(b, m - 2e - 2)`. The good truncation `K = truncGE N L` is bounded
   and classical, so step 6 kills degree `m` of its image. Apply
   lem-sfb-finite-proper-classical-truncation to the identity base change;
   `N < m - 2e - 1` identifies this cohomology with that of the image of `L`.
   All degrees above `b + 2e` therefore vanish without a lower bound on `L`.
8. Apply lem-exc-direct-image-coproducts with `c = 2e`, properness supplying
   qcqs and step 4 supplying its higher-image hypothesis. Its canonical
   comparison is induced by the images of every coprojection and includes
   empty families. No quasi-compactness of the base or ground-field bound enters. -/
theorem finiteProper_classical_amplitude
    (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (e : ℕ)
    (_hbound : ∀ (T : Scheme.{u}) (g : T ⟶ Y) (t : T),
      topologicalKrullDim ((pullback.snd f g).fiber t) ≤ (e : WithBot ℕ∞)) :
    Nonempty ((Scheme.proEtaleConstantDerivedDirectImage f A).CommShift ℤ) ∧
    (Scheme.proEtaleConstantDerivedDirectImage f A).IsTriangulated ∧
    Nonempty (HasCountableProducts (Scheme.proEtaleDerivedCategory X A)) ∧
    Nonempty (HasCountableProducts (Scheme.proEtaleDerivedCategory Y A)) ∧
    (∀ (I : Type w) [Countable I], PreservesLimitsOfShape (Discrete I)
      (Scheme.proEtaleConstantDerivedDirectImage f A)) ∧
    (∀ (a : ℤ) (L : Scheme.proEtaleDerivedCategory X A), L.IsGE a →
      ((Scheme.proEtaleConstantDerivedDirectImage f A).obj L).IsGE a) ∧
    (∀ (b : ℤ) (L : Scheme.proEtaleDerivedCategory X A),
      IsClassicalModuleComplex L → L.IsLE b →
      ((Scheme.proEtaleConstantDerivedDirectImage f A).obj L).IsLE (b + 2 * (e : ℤ))) ∧
    (∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
      (q : ℤ), 2 * (e : ℤ) < q →
      IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) ∧
    (∀ I : Type w, PreservesColimitsOfShape (Discrete I)
      (Etale.rightDerivedLowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)) := by
  sorry

end AlgebraicGeometry.ProEtale
