/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.IntegralScalarExtensionConstructibleIntrinsic
public import Sheaf.Paper.ScalarExtensionComposition

import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Paper.FiniteFreeCompletedScalarComparison
import Sheaf.Paper.PbcActualScalarPullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses

/-! # Composition of intrinsic rational scalar extensions

Source: Weil conjectures blueprint, sec-smooth-purity/sk-def-sf-operations,
order 1469; current main snapshot sec-proper-base-change/sk-thm-properbasechange,
order 1828 (blueprint: lem-weil-scalar-extension-composition).

The ordinary balanced tensor associator and unit are reused from the legacy module.
Their quotient-completion normalization is transported to the current intrinsic integral
subcategory and then to its raw Hom scalar localization. No identification with the legacy
integral constructibility predicate is assumed.

## Main statements

- `sfRationalScalarComp`: canonical composition on the currently recorded rational stages.
- `sfRationalScalarUnit`: the normalized identity-extension comparison.
- `sfRationalScalar_coherence`: both unit equations and the pentagon.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- The normalized ordinary-to-completed comparison on intrinsic integral objects.
Source: blueprint order 1828, proof, first paragraph
(blueprint: lem-weil-scalar-extension-composition).
Proof: the finite-free completed-scalar comparison in the DAG identifies ordinary derived
extension and completed extension on every derived-complete input. On a K-flat complex
with flat terms, its map is the quotient-completion chain map: its unshifted cone
coordinates are the finite quotient tensor maps, and its shifted coordinate is zero.
Finite freeness commutes with the products in the Roos complex; completeness and cofinality
of the two uniformizer filtrations show this very map is invertible. The intrinsic predicate
includes derived completeness, so this applies without a finite-field structure on Y.
Naturality for good complexes descends through roofs. Every object has a good resolution,
so the displayed representative characterization determines the comparison uniquely. -/
theorem sfIntegralOrdinaryComparison_existsUnique :
    ∃! c : (sfIntegralConstructible l E Y).ι ⋙ integralOrdinaryDerivedScalar l E L ι Y ≅
        (sfIntegralConstructible l E Y).ι ⋙ integralScalarExtension l E L ι Y,
      ∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (hP : sfIntegralConstructible l E Y (DerivedCategory.Q.obj P.obj)),
        c.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
            (integralScalarExtensionComparison l E L ι Y).hom.app P =
          (integralOrdinaryScalar l E L ι Y).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map ((integralScalarCompletionChain l E L ι Y).app P.obj) := by
  sorry

/-- The uniquely normalized comparison; its data is fixed by quotient maps on good complexes.
Source: blueprint order 1828 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def sfIntegralOrdinaryComparison :=
  (sfIntegralOrdinaryComparison_existsUnique l E L ι Y).exists.choose

variable (p : ℕ) (hl : l ≠ p)
  (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
  (j : L →ₐ[Padic l] M)

/-- Completed integral associativity, uniquely fixed by ordinary balanced tensor and the
normalized quotient-completion comparisons.
Source: blueprint order 1828, proof, first paragraph
(blueprint: lem-weil-scalar-extension-composition).
Proof: on a K-flat resolution, ordinary associativity sends c tensor (b tensor x) to
c*j(b) tensor x, with inverse c tensor x to c tensor (1 tensor x). These maps commute
with restrictions, differentials and chain maps, hence descend through roofs. Conjugate
this fixed ordinary associator by the three normalized ordinary-to-completed comparisons.
Completed extension preserves the intrinsic subcategories, so full faithfulness of their
inclusions lifts this isomorphism and its inverse uniquely. The displayed equation specifies
that lift, rather than choosing an unnormalized natural isomorphism. -/
theorem sfIntegralScalarComp_existsUnique :
    ∃! a : sfConstructibleIntegralScalarExtension p l hl E L ι Y ⋙
        sfConstructibleIntegralScalarExtension p l hl L M j Y ≅
        sfConstructibleIntegralScalarExtension p l hl E M (j.comp ι) Y,
      ∀ K : sfIntegralConstructibleCategory l E Y,
        (a.hom.app K).hom =
          (sfIntegralOrdinaryComparison l L M j Y).inv.app
              ((sfConstructibleIntegralScalarExtension p l hl E L ι Y).obj K) ≫
            (integralOrdinaryDerivedScalar l L M j Y).map
              ((sfIntegralOrdinaryComparison l E L ι Y).inv.app K) ≫
            (integralOrdinaryDerivedScalarComp l E L ι Y M j).hom.app K.obj ≫
            (sfIntegralOrdinaryComparison l E M (j.comp ι) Y).hom.app K := by
  sorry

/-- The intrinsic completed integral associator with its fixed tensor normalization.
Source: blueprint order 1828 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def sfIntegralScalarComp :=
  (sfIntegralScalarComp_existsUnique l E L ι Y p hl M j).exists.choose

/-- The completed integral identity comparison, uniquely normalized by multiplication.
Source: blueprint order 1828, proof, identity-extension clause
(blueprint: lem-weil-scalar-extension-composition).
Proof: the ordinary unit sends s tensor x to s*x, with inverse x to 1 tensor x.
Conjugating it by the identity ordinary-to-completed comparison gives the actual
completeness-unit normalization. Full faithfulness lifts it uniquely to the intrinsic
subcategory; the inverse is the lift of the inverse ambient map. -/
theorem sfIntegralScalarUnit_existsUnique :
    ∃! a : sfConstructibleIntegralScalarExtension p l hl E E (AlgHom.id (Padic l) E) Y ≅
        𝟭 (sfIntegralConstructibleCategory l E Y),
      ∀ K : sfIntegralConstructibleCategory l E Y,
        (a.hom.app K).hom =
          (sfIntegralOrdinaryComparison l E E (AlgHom.id (Padic l) E) Y).inv.app K ≫
            (integralOrdinaryDerivedScalarUnit l E Y).hom.app K.obj := by
  sorry

/-- The normalized intrinsic integral unit.
Source: blueprint order 1828 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def sfIntegralScalarUnit :=
  (sfIntegralScalarUnit_existsUnique l E Y p hl).exists.choose

/-- The rational associator is uniquely specified as the image of the normalized
completed integral associator on every unchanged integral object.
Source: blueprint order 1828, proof, second paragraph
(blueprint: lem-weil-scalar-extension-composition).
Proof: rationalization has the same objects, and its morphisms are generated by pure
tensors f tensor a. Tensor each component of the integral associator and its inverse
with one. Integral naturality is linear over the source integers, so multiplying it
by a and adding proves naturality for every rational morphism. The inverse equations
survive localization. The published scalar functor has precisely the prescribed integral
object map; transport along that equality gives the displayed HEq. Every object is an
integral representative, so the component condition uniquely determines the isomorphism. -/
theorem sfRationalScalarComp_existsUnique :
    ∃! a : sfRationalScalarExtension l E Y p hl L ι ⋙
        sfRationalScalarExtension l L Y p hl M j ≅
        sfRationalScalarExtension l E Y p hl M (j.comp ι),
      ∀ K : sfRationalConstructibleCategory l E Y,
        HEq (a.hom.app K)
          ((sfRationalConstructibleLocalization l M Y).map
            ((sfIntegralScalarComp l E L ι Y p hl M j).hom.app K.obj)) := by
  sorry

/-- Canonical composition for the currently recorded rational scalar extensions.
Source: blueprint order 1828 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def sfRationalScalarComp :
    sfRationalScalarExtension l E Y p hl L ι ⋙ sfRationalScalarExtension l L Y p hl M j ≅
      sfRationalScalarExtension l E Y p hl M (j.comp ι) :=
  (sfRationalScalarComp_existsUnique l E L ι Y p hl M j).exists.choose

/-- The rational unit is the localized normalized integral unit on every object.
Source: blueprint order 1828, proof, identity-extension clause
(blueprint: lem-weil-scalar-extension-composition).
Proof: localize the integral unit and inverse. Integral naturality multiplied by each
coefficient proves rational naturality on pure tensors and hence on every morphism.
The scalar functor's specified object equalities identify the endpoints, giving HEq.
All objects are integral representatives, so this condition proves uniqueness. -/
theorem sfRationalScalarUnit_existsUnique :
    ∃! a : sfRationalScalarExtension l E Y p hl E (AlgHom.id (Padic l) E) ≅
        𝟭 (sfRationalConstructibleCategory l E Y),
      ∀ K : sfRationalConstructibleCategory l E Y,
        HEq (a.hom.app K)
          ((sfRationalConstructibleLocalization l E Y).map
            ((sfIntegralScalarUnit l E Y p hl).hom.app K.obj)) := by
  sorry

/-- The rational identity comparison, retaining the completeness-unit normalization.
Source: blueprint order 1828 (blueprint: lem-weil-scalar-extension-composition). -/
noncomputable def sfRationalScalarUnit :
    sfRationalScalarExtension l E Y p hl E (AlgHom.id (Padic l) E) ≅
      𝟭 (sfRationalConstructibleCategory l E Y) :=
  (sfRationalScalarUnit_existsUnique l E Y p hl).exists.choose

/-- Both identity-extension laws and the pentagon for the canonical intrinsic comparisons.
Source: blueprint order 1828, proof, unit and pentagon clauses
(blueprint: lem-weil-scalar-extension-composition).
Proof: check ordinary sheaf tensor generators. For a source identity, the associator
sends c tensor (b tensor x) to cb tensor x, which equals c tensor (b*x). For a target
identity, it is the multiplication unit at the extended object. Both paths for three
extensions send d tensor (c tensor (b tensor x)) to d*k(c)*k(j(b)) tensor x.
Associativity in the final completed coefficient ring proves equality, and local tensor
generation extends it to sheaves. Derived localization preserves these equations.
Expand the completed comparisons as conjugates by the normalized quotient-completion
maps; naturality moves intermediate comparisons past tensor maps and cancels adjacent
inverse factors, leaving the ordinary equations. Full-subcategory faithfulness and
rationalization preserve them. These arguments also cover identity embeddings and
E=L=M, the zero object, and the empty scheme. -/
theorem sfRationalScalar_coherence :
    (∀ K : sfRationalConstructibleCategory l E Y,
      (sfRationalScalarComp l E E (AlgHom.id (Padic l) E) Y p hl L ι).hom.app K =
        (sfRationalScalarExtension l E Y p hl L ι).map
          ((sfRationalScalarUnit l E Y p hl).hom.app K)) ∧
    (∀ K : sfRationalConstructibleCategory l E Y,
      (sfRationalScalarComp l E L ι Y p hl L (AlgHom.id (Padic l) L)).hom.app K =
        (sfRationalScalarUnit l L Y p hl).hom.app
          ((sfRationalScalarExtension l E Y p hl L ι).obj K)) ∧
    (∀ (N : Type u) [Field N] [Algebra (Padic l) N] [FiniteDimensional (Padic l) N]
      (k : M →ₐ[Padic l] N) (K : sfRationalConstructibleCategory l E Y),
      (sfRationalScalarExtension l M Y p hl N k).map
          ((sfRationalScalarComp l E L ι Y p hl M j).hom.app K) ≫
        (sfRationalScalarComp l E M (j.comp ι) Y p hl N k).hom.app K =
      (sfRationalScalarComp l L M j Y p hl N k).hom.app
          ((sfRationalScalarExtension l E Y p hl L ι).obj K) ≫
        (sfRationalScalarComp l E L ι Y p hl N (k.comp j)).hom.app K) := by
  sorry

end WeilConjectures
