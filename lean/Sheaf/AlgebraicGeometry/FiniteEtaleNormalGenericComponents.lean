/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Topology.Defs.Filter
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.Separable
import Sheaf.AlgebraicGeometry.EtaleNormalComponents
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.AlgebraicGeometry.NormalSectionsFiniteProduct
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.CategoryTheory.Extensive
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Generic fields and normalizations of finite étale components

Source: Stacks Project, Tag 0BQL, statement and proof; Tag 02GL, part (2).
(blueprint: lem-sfb-finite-etale-normal-generic-components)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite étale cover of a normal integral Noetherian scheme is a finite disjoint
clopen union of normal integral schemes. Their function fields are finite separable
extensions of the base function field. The generic fibre is their spectra, compatibly
with both projections, and each component is the normalization in its own function field.
The normalization isomorphism is uniquely specified over the base and on the generic field.
Normality is expressed by integral closedness of every stalk; integrality supplies domains.

Source: Stacks Project, Tag 0BQL, both proof paragraphs; Tag 02GL(2).
(blueprint: lem-sfb-finite-etale-normal-generic-components)

Proof:
1. Finiteness implies finite type: finite module generators generate the algebra and
an affine inverse image is a finite affine cover. By lem-weil-pbc-finite-type-over-noetherian,
Y is Noetherian.
2. Apply lem-fin-etale-normal-components to obtain finitely many disjoint clopen normal
integral opens U i covering Y. Integrality makes every component nonempty. Empty Y gives n=0.
3. A clopen inclusion is a closed immersion: sections extend by zero across its open
complement. By lem-weil-pbc-closed-immersion-finite and lem-weil-pbc-finite-composition its
composite with p is finite. By lem-weil-pbc-etale-composition-cancellation it is étale.
4. The image of each component is closed by lem-weil-pbc-finite-closed-map-finite-fibres
and open by lem-weil-pbc-etale-morphism-open-map. It is nonempty, so irreducibility of X
makes it all of X; thus each component map is surjective.
5. On nonempty affine V=Spec A, write its inverse image in U i as Spec B. Surjectivity
implies A injects into B, by a prime above (0). Both are domains. By
lem-sc-integral-function-field-affine-fraction their fraction fields are F and F_i.
By lem-weil-pbc-fibre-product-affine-spectra the generic fibre ring is B tensor_A F,
identified by b tensor a/s ↦ ab/s with S^{-1}B for S=A\{0}. This is a nonzero domain.
By lem-weil-pbc-etale-fibre-discrete-separable-points its spectrum is a disjoint union of
finite separable field spectra; irreducibility leaves one summand. Thus S^{-1}B is a
finite separable field and equals Frac B, compatibly with B and F.
6. Apply lem-sbc-normal-sections-finite-product to the affine inverse image in U i.
Its ring B is a domain, so the product has exactly one factor and B is integrally closed.
By lem-weil-pbc-finite-algebra-is-integral B is integral over A. Conversely an element of
F_i integral over A is integral over B by the same monic polynomial, hence belongs to B.
Thus B is exactly the integral closure of A inside F_i.
7. By def-fin-normalization-extension these equalities inside F_i agree on principal
opens and glue to the normalization isomorphism. It is the identity on F_i and lies over X.
The same affine description makes it unique. Its structure map is finite étale by step 3.
8. Apply lem-sc-etale-fibre-product-base-change-coproduct to the clopen decomposition
and Spec F → X. Step 5 gives the displayed generic-fibre isomorphism and its two projection
compatibilities. Primitive nonzero idempotents of a finite product of fields are precisely
the coordinate idempotents, so each field factor belongs to exactly one component, even
when distinct factors are isomorphic fields. Step 7 identifies its normalization.
For empty Y take n=0; conversely nonempty components force n=0 when Y is empty. -/
theorem exists_finite_etale_normal_generic_components {X Y : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (p : Y ⟶ X) [IsFinite p] [Etale p] :
    ∃ (n : ℕ) (U : Fin n → Y.Opens) (hI : ∀ i, IsIntegral (U i).toScheme)
      (A : ∀ i, Algebra X.functionField (U i).toScheme.functionField),
      (∀ i, IsClosed (U i : Set Y)) ∧
      (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
      (⨆ i, U i) = ⊤ ∧
      (n = 0 ↔ IsEmpty Y) ∧
      (∀ i, (∀ y : (U i).toScheme,
          IsIntegrallyClosed ((U i).toScheme.presheaf.stalk y)) ∧
        IsFinite ((U i).ι ≫ p) ∧ Etale ((U i).ι ≫ p) ∧ Surjective ((U i).ι ≫ p) ∧
        FiniteDimensional X.functionField (U i).toScheme.functionField ∧
        Algebra.IsSeparable X.functionField (U i).toScheme.functionField ∧
        ∃! e : (U i).toScheme ≅ X.normalizationIn (U i).toScheme.functionField,
          e.hom ≫ X.fromNormalizationIn (U i).toScheme.functionField = (U i).ι ≫ p ∧
          (U i).toScheme.fromSpecFunctionField ≫ e.hom =
            (X.fromSpecOfAlgebraFunctionField (U i).toScheme.functionField).toNormalization) ∧
      ∃ e : (∐ fun i : Fin n ↦ Spec (U i).toScheme.functionField) ≅
          pullback p X.fromSpecFunctionField,
        ∀ i, Sigma.ι (fun j : Fin n ↦ Spec (U j).toScheme.functionField) i ≫ e.hom ≫
              pullback.fst p X.fromSpecFunctionField =
            (U i).toScheme.fromSpecFunctionField ≫ (U i).ι ∧
          Sigma.ι (fun j : Fin n ↦ Spec (U j).toScheme.functionField) i ≫ e.hom ≫
              pullback.snd p X.fromSpecFunctionField =
            Spec.map (CommRingCat.ofHom
              (algebraMap X.functionField (U i).toScheme.functionField)) := by
  sorry

end AlgebraicGeometry
