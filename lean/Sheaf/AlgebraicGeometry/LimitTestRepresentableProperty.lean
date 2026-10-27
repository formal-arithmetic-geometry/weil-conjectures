/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids
public import Sheaf.AlgebraicGeometry.FibredGroupoidLimitPreserving
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Limits.HasLimits

/-! # Finite-presentation affine tests for a representable morphism property

Source: Stacks Project, Criteria for Representability, Tag 07WI,
lemma-check-property-limit-preserving, proof
(blueprint: lem-sfb-limit-test-representable-property).

The property is arbitrary on algebraic-space maps to schemes. Its three laws are
written explicitly, without assuming locality for the fppf topology or descent of arrows.
-/

@[expose] public section

set_option autoImplicit false

universe u v₁ w₁ v₂ w₂

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace CategoryTheory

/-- Affine scheme tests locally of finite presentation suffice for a representable property.
A based functor from the discrete groupoid `h_T` is an object over `T`, by 2-Yoneda.
`HasSpaceBaseChange` retains both the representing equivalence and its projection to `T`.
In `hLocal`, a set of opens describes an arbitrary open cover; the empty cover is allowed.
The restrictions are specified by actual pullback squares, so no choice of representative
or of a fibre product is built into the property.

Source: Stacks Project, Criteria, Tag 07WI, lemma-check-property-limit-preserving,
proof (blueprint: lem-sfb-limit-test-representable-property).

Proof:
1. For a base map and an isomorphism between the pulled-back object and another object,
identify their represented fibres with the base change of the original represented fibre.
On test objects compose the comparison with the pulled-back isomorphism or its inverse;
these inverse operations also commute with arrows and pullbacks. Use
lem-trf-space-fibre-products-etale-covers for algebraic-space fibre products.
2. If V = Spec A maps into an affine open Spec R of S, present A as a directed colimit
of finitely presented R-algebras, using Stacks 00QN: an index is a pair (E,K) with
E a finite subset of A and K a finite set of polynomials in R[X_e : e in E] vanishing
at their named generators. Order by inclusion of E and of the transported K. The empty
pair is an index; unions give common upper bounds. The stages are R[X_e]/(K), with maps
given by the named generators, and their cocone evaluates X_e at e in A. This index is
small. Given compatible maps to an R-algebra B, define the image of a using X_a at its
singleton-generator stage. Compatibility determines every generator's image at every
stage. Stages containing the addition, multiplication, unit and scalar relations show
that this is an R-algebra map. Agreement on the generators proves factorization;
singleton stages prove uniqueness. This is def-weil-pbc-category-colimit.
3. This is also a colimit of rings: compatible ring maps give one common map from R,
since the index set is nonempty and directed; apply the R-algebra universal property.
4. By lem-weil-pbc-spec-colimit-limit the corresponding affine schemes have limit V,
with the stated projections; nonemptiness also gives the limit over S. Each stage is
locally of finite presentation over S, using its affine R-chart and the definition
in def-sbc-locally-finite-presentation. No quasi-compactness assumption on S is needed.
5. ObjectsDescend gives a stage object whose pullback is the prescribed object over V.
The affine test hypothesis, arbitrary base-change stability and isomorphism invariance
then prove the property over V. Neither fullness nor faithfulness of a limit comparison,
nor limit preservation of the source groupoid, is used.
6. For arbitrary T, choose at each point an affine open whose map to S factors through
an affine open of S, using lem-weil-pbc-affine-opens-basis twice and the open-subscheme
factorization of def-weil-open-immersion. Apply step 5 on this cover and step 1 to identify
these maps with the restrictions of the represented fibre. Zariski locality gives the
claim over T. For empty T the empty cover gives the conclusion directly. -/
theorem limit_test_representable_property
    {S : Scheme.{u}}
    (F : BasedCategory.{v₁, w₁} (Over S)) (G : BasedCategory.{v₂, w₂} (Over S))
    (f : BasedFunctor F G) (hF : IsFibredInGroupoids F) (hG : IsFibredInGroupoids G)
    (hrep : IsRepresentableByAlgebraicSpaces f)
    (hLimits : FibredGroupoidLimit.ObjectsDescend G)
    (P : ∀ (T : Over S) (Z : AlgebraicSpace S), (Z.obj.obj ⟶ yoneda.obj T) → Prop)
    (hIso : ∀ (T T' : Over S) (Z Z' : AlgebraicSpace S)
      (a : Z.obj.obj ⟶ yoneda.obj T) (a' : Z'.obj.obj ⟶ yoneda.obj T')
      (e : Z.obj.obj ≅ Z'.obj.obj) (d : T ≅ T'),
      e.hom ≫ a' = a ≫ yoneda.map d.hom → (P T Z a ↔ P T' Z' a'))
    (hBase : ∀ (T T' : Over S) (Z Z' : AlgebraicSpace S)
      (a : Z.obj.obj ⟶ yoneda.obj T) (a' : Z'.obj.obj ⟶ yoneda.obj T')
      (b : Z'.obj.obj ⟶ Z.obj.obj) (g : T' ⟶ T),
      IsPullback b a' a (yoneda.map g) → P T Z a → P T' Z' a')
    (hLocal : ∀ (T : Over S) (Z : AlgebraicSpace S) (a : Z.obj.obj ⟶ yoneda.obj T)
      (𝒰 : Set T.left.Opens), (∀ x : T.left, ∃ U ∈ 𝒰, x ∈ U) →
      (P T Z a ↔ ∀ (U : T.left.Opens), U ∈ 𝒰 →
        ∀ (Z' : AlgebraicSpace S)
          (a' : Z'.obj.obj ⟶ yoneda.obj (Over.mk (U.ι ≫ T.hom)))
          (b : Z'.obj.obj ⟶ Z.obj.obj),
          IsPullback b a' a (yoneda.map (Over.homMk U.ι)) →
            P (Over.mk (U.ι ≫ T.hom)) Z' a'))
    (hTest : ∀ (T : Over S), IsAffine T.left → LocallyOfFinitePresentation T.hom →
      ∀ (t : BasedFunctor (discreteModuli (yoneda.obj T)) G)
        (Z : AlgebraicSpace S) (a : Z.obj.obj ⟶ yoneda.obj T),
        HasSpaceBaseChange f T t Z a → P T Z a) :
    ∀ (T : Over S) (t : BasedFunctor (discreteModuli (yoneda.obj T)) G)
      (Z : AlgebraicSpace S) (a : Z.obj.obj ⟶ yoneda.obj T),
      HasSpaceBaseChange f T t Z a → P T Z a := by
  sorry

end CategoryTheory
