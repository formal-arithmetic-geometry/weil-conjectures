/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q41
-/
module

public import Sheaf.AlgebraicGeometry.CoherentStackAlgebraicLfp
public import Sheaf.AlgebraicGeometry.OpenModuliSubstack
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.FieldTheory.CommonExtensionFields
import Mathlib.RingTheory.Flat.Stability
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # The invertible open substack of coherent families

Source: Stacks Project, quot.tex, Tag 0D03, lemma-picard-stack-open-in-coh
(blueprint: lem-sfb-invertible-open-in-coherent-stack).

The full subcategory uses the concrete coherent-family objects and their original
pullback-isomorphism arrows. Every invertible module occurs in this subcategory.
The open-substack witness retains the equivalence of the actual two-fibre product
and its projection; the final clause gives the open locus for each coherent family.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Invertible modules form a fully faithful open substack of coherent families for a
proper flat finitely presented morphism. The first clause ensures that restricting the
ambient category to invertible objects includes every line bundle, not just a subset.
The `OpenModuliSubstack.open_pullback` field represents each two-fibre product by an
open immersion, compatibly with the test projection. The last clause specifies the
representing open by its universal property for arbitrary base change.
Source: Stacks Project, quot.tex, Tag 0D03, lemma-picard-stack-open-in-coh
(blueprint: lem-sfb-invertible-open-in-coherent-stack).
Proof:
1. Base change preserves properness and flatness (lem-weil-pbc-proper-fp-permanence,
   lem-weil-pbc-flat-morphism-base-change). A line bundle is quasi-coherent and finitely
   presented. Its rank-one stalks are flat over the test base by flatness of the family
   and lem-pc-module-flat-transitive. Its proper-support witness is the whole X_T with
   the identity closed immersion. Tensor pullback preserves its local rank-one frames.
   The full inclusion keeps exactly the same pullback-isomorphism arrows.
2. For a coherent family F, lem-sfb-relative-finite-free-locus-base-change gives an open
   finite-free locus W in X_T commuting with arbitrary base change. The family is locally
   finitely presented after base change (lem-weil-pbc-qcqs-morphism-permanence). Properness
   makes V = T minus the image of the complement of W open. The pullback of F is finite
   locally free precisely for maps factoring through V.
3. To check this last assertion for arbitrary test maps, lift a pair of points over the
   same base point to the fibre product using lem-weil-common-extension-fields and
   def-pc-fibre-product. Thus missing the closed image is equivalent to having empty
   inverse image. An image contained in an open factors uniquely through its subscheme.
4. On X_V the rank of F is locally constant, by finite local frames and residue-field
   dimensions; its rank-one locus is both open and closed. Pulling back frames preserves
   their ranks (lem-pc-finrank-field-base-change). No bound on all ranks is required.
5. Remove from V the proper image of the complementary ranks. The resulting open U
   has exactly the asserted factorization property, by point lifting and rank-one frames
   (def-sc-invertible-module, def-weil-open-immersion).
6. Over a test map into U, the two-fibre product consists of a line bundle L and an
   isomorphism to the pulled-back F. The pulled-back F with its identity is a terminal
   object, with a unique compatible arrow from every other object; outside U there are
   no objects. These equivalences commute with pullback by uniqueness, and identify the
   projection with the open immersion (def-sfb-open-moduli-substack). Neither geometric
   reducedness nor a condition on the direct image of the structure sheaf is used. -/
theorem invertible_open_in_coherent_stack {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] :
    (∀ (T : Over S) (L : (pullback f T.hom).Modules), L.IsInvertible →
      ∃ A : FlatCoherentModuli f, A.base = T ∧ HEq A.module L) ∧
    ∃ B : OpenModuliSubstack (FlatCoherentModuli.category f),
      B.property = (fun A : FlatCoherentModuli f ↦ A.module.IsInvertible) ∧
      (fullModuliInclusion (FlatCoherentModuli.category f) B.property).toFunctor.Full ∧
      (fullModuliInclusion (FlatCoherentModuli.category f) B.property).toFunctor.Faithful ∧
      ∀ A : FlatCoherentModuli f, ∃ U : A.base.left.Opens,
        ∀ (T₁ : Over S) (v : T₁ ⟶ A.base),
          ((Scheme.Modules.moduleBaseChange f v).obj A.module).IsInvertible ↔
            ∃ w : T₁.left ⟶ U.toScheme, w ≫ U.ι = v.left := by
  sorry

end AlgebraicGeometry
