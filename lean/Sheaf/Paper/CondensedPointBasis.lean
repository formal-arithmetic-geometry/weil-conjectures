/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NZ
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.FinitePresentation
public import Sheaf.RingTheory.IndEtaleUniverseTransport
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Profinite
import WeilConjectures.Mathlib.RingTheory.Etale.Field

/-!
# Affine ind-etale schemes over a separably closed field

Source: Weil conjectures blueprint, main-20261015, sec-proetale-coefficients,
sk-prop-pe-condensed-point-basis and its proof
(blueprint: det-pe-condensed-point-basis).

## Main definitions

* `AlgebraicGeometry.ProEtale.condensedPointAlgebraFunctor`: locally constant algebras,
  contravariantly by precomposition.
* `AlgebraicGeometry.ProEtale.condensedPointSchemeFunctor`: their spectra over the field.

## Main statement

* `AlgebraicGeometry.ProEtale.condensed_point_basis`: the finite and ind-etale
  classifications, the specified Hom bijection, the equivalence onto affine ind-etale
  schemes, and its natural identification with the existing relative test-object functor.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The algebra part of `S ↦ Ω[S]`: the actual algebra `LocallyConstant S Ω`, with
morphisms given by precomposition. Source: main-20261015 blueprint,
sk-prop-pe-condensed-point-basis, opening paragraph and clause (3)
(blueprint: det-pe-condensed-point-basis). -/
def condensedPointAlgebraFunctor (Ω : Type u) [CommRing Ω] :
    Profinite.{u} ⥤ (CommAlgCat.{u} Ω)ᵒᵖ where
  obj S := op (CommAlgCat.of Ω (LocallyConstant S Ω))
  map f := (CommAlgCat.ofHom (LocallyConstant.comapₐ Ω f.hom.hom)).op

/-- The specified functor `S ↦ Spec LC(S,Ω)` over `Spec Ω`, with spectra of
precomposition on arrows. This uses Mathlib's existing relative spectrum functor.
Source: main-20261015 blueprint, sk-prop-pe-condensed-point-basis, final paragraph
(blueprint: det-pe-condensed-point-basis). -/
noncomputable def condensedPointSchemeFunctor (Ω : Type u) [CommRing Ω] :
    Profinite.{u} ⥤ Over (Spec (.of Ω)) :=
  condensedPointAlgebraFunctor Ω ⋙ algSpec (.of Ω)

/-- Over a separably closed field, finitely presented etale algebras are finite
powers, ind-etale algebras are exactly locally constant algebras on profinite spaces,
and all algebra maps between these algebras are uniquely continuous precompositions.
The specified spectrum functor gives the equivalence onto the full category of affine
ind-etale schemes over the field, and is naturally the relative test-object functor.

Source: main-20261015 blueprint, sk-prop-pe-condensed-point-basis, all three numbered
clauses and the final paragraph (blueprint: det-pe-condensed-point-basis).

Proof plan, following the node's nine steps:
1. `lem-weil-pbc-etale-ring-map-iff-etale-affine` and
   `lem-weil-pbc-etale-algebra-over-field-product` express a finite-stage algebra as a
   finite product of finite separable fields. `lem-pc-sepclosed-finite-sep-trivial`
   identifies each factor with Ω. Number the finite set, retaining the empty product.
   Conversely use `lem-weil-pbc-finite-separable-extension-etale` on Ω and
   `lem-weil-pbc-etale-algebra-finite-product` on its finite powers.
2. An algebra map from Ω^F is determined by its orthogonal characteristic idempotents,
   whose sum is one. In LC(T,Ω) their fibers at one give a clopen partition of T,
   including empty blocks. This is exactly a continuous map T → F; the algebra map
   is precomposition. For empty F it exists precisely when the target is zero.
3. For any small cofiltered diagram of finite spaces, realize the limit as compatible
   tuples in the product. The compatibility conditions are closed. Use
   `lem-weil-pbc-tychonoff-product-quasi-compact` and
   `lem-weil-pbc-closed-in-quasi-compact` for compactness. Coordinates separate points
   and force connected subsets to be singletons. Thus the limit is profinite,
   with the usual universal property, including empty factors and empty limits.
4. Index finite clopen partitions by refinement. Common refinements show cofilteredness.
   The canonical map from a profinite space to the limit of its finite quotients is
   injective by `lem-weil-pbc-profinite-clopen-basis`, and surjective by compactness
   and the finite intersection property of compatible blocks. Apply
   `lem-weil-pbc-compact-hausdorff-bijection`. For an empty space use its empty quotient.
5. If two functions at one finite stage agree on the limit, they agree after some
   transition: otherwise compactness of the product would give a compatible tuple
   where they differ. Explicitly choose a finite incompatible subfamily and a cone
   over its finitely many objects and arrows, equalizing parallel composites using
   `def-weil-pbc-category-colimit`. An empty stage is handled by a common predecessor.
6. `lem-weil-pbc-profinite-limit-function-factorization` factors every locally constant
   function through a finite stage. Step 5 makes evaluation by any compatible algebra
   cocone independent of the representative. Put finitely many representatives at a
   common stage to check ring operations and scalars. This is the colimit universal
   property of `def-weil-pbc-category-colimit`. It is also a ring colimit: all stage
   scalar maps agree by filteredness and the index category is nonempty.
7. Apply this colimit property to finite quotients of S. Step 2 identifies algebra maps
   to LC(T,Ω) with compatible continuous maps to the finite quotients of S. Step 4
   gives a unique continuous T → S. On a representative h = f ∘ q its algebra map is
   h ↦ f ∘ q ∘ s = h ∘ s, compatibly with identities and composition.
8. Use `def-weil-pbc-ind-etale-algebra` to present an ind-etale algebra by finite-stage
   etale algebras. Step 1 gives finite powers, and step 2 gives the opposite finite
   diagram. Steps 3 and 6 identify its colimit with LC(S,Ω). Conversely the finite
   quotients of every S give a filtered etale presentation of LC(S,Ω).
9. `def-weil-affine-spectrum` translates step 7 to full faithfulness and step 8 to
   essential surjectivity onto affine ind-etale schemes. For the final comparison use
   `def-sfb-profinite-test-objects`, `lem-weil-pbc-finite-affine-coproduct-spectrum`
   and `lem-weil-pbc-spec-small-colimit-limit`: both functors are limits of the same
   finite coproduct diagram over Spec Ω. Their unique limit comparison is over Ω
   and natural because transitions and maps are spectra of precomposition. -/
theorem condensed_point_basis (Ω : Type u) [Field Ω] [IsSepClosed Ω] :
    (∀ (A : Type u) [CommRing A] [Algebra Ω A],
      Algebra.Etale Ω A → Algebra.FinitePresentation Ω A →
      ∃ n : ℕ, Nonempty (A ≃ₐ[Ω] (Fin n → Ω))) ∧
    (∀ (A : Type u) [CommRing A] [Algebra Ω A],
      RingHom.IndEtaleAcrossUniverses (algebraMap Ω A) →
      ∃ S : Profinite.{u}, Nonempty (A ≃ₐ[Ω] LocallyConstant S Ω)) ∧
    (∀ S : Profinite.{u},
      RingHom.IndEtaleAcrossUniverses (algebraMap Ω (LocallyConstant S Ω))) ∧
    (∀ S T : Profinite.{u}, Function.Bijective
      (fun s : C(T, S) ↦ (LocallyConstant.comapₐ Ω s :
        LocallyConstant S Ω →ₐ[Ω] LocallyConstant T Ω))) ∧
    (∃ E : Profinite.{u} ≌ ObjectProperty.FullSubcategory
        (fun Y : Over (Spec (.of Ω)) ↦ IsAffine Y.left ∧ proAffineEtale Y.hom),
      Nonempty (E.functor ⋙ ObjectProperty.ι
        (fun Y : Over (Spec (.of Ω)) ↦ IsAffine Y.left ∧ proAffineEtale Y.hom) ≅
          condensedPointSchemeFunctor Ω)) ∧
    Nonempty (condensedPointSchemeFunctor Ω ≅
      profiniteToProEtOf (Spec (.of Ω)) ⋙ Scheme.ProEt.forget (Spec (.of Ω))) := by
  sorry

end AlgebraicGeometry.ProEtale
