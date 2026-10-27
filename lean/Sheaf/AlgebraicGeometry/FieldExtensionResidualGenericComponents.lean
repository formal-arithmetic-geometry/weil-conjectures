/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.Sober
public import WeilConjectures.ZetaSeries
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Ideal.GoingDown

/-!
# Generic components under arbitrary field extension

Source: Stacks Project, More on Morphisms, Tag 0GSI, first two proof paragraphs;
Divisors, Tag 05DC, residual-fibre identification; Algebra, Tag 00HS, flat going-down.
(blueprint: lem-trf-field-extension-residual-generic-components)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Hom

/-- The actual tensor ring `κ(z) ⊗[k] L`, using the canonical residue-field embedding
induced by the structure map. Source: Stacks Project, Divisors, Tag 05DC.
(blueprint: lem-trf-field-extension-residual-generic-components) -/
noncomputable def fieldExtensionResidualRing {k L : Type u} [Field k] [Field L]
    [Algebra k L] {Z : Scheme.{u}} [Z.Over (Spec (.of k))] (z : Z) : CommRingCat.{u} :=
  letI := ((Z ↘ Spec (.of k)).residueFieldAlgebraMap z).toAlgebra
  CommRingCat.of ((Z.residueField z) ⊗[k] L)

/-- The left tensor inclusion `κ(z) → κ(z) ⊗[k] L`.
Source: Stacks Project, Divisors, Tag 05DC, and Schemes, Tag 01I4.
(blueprint: lem-trf-field-extension-residual-generic-components) -/
noncomputable def fieldExtensionResidualLeft {k L : Type u} [Field k] [Field L]
    [Algebra k L] {Z : Scheme.{u}} [Z.Over (Spec (.of k))] (z : Z) :
    Z.residueField z ⟶ fieldExtensionResidualRing (k := k) (L := L) z :=
  letI := ((Z ↘ Spec (.of k)).residueFieldAlgebraMap z).toAlgebra
  CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom (R := k) (A := Z.residueField z) (B := L))

/-- The right tensor inclusion `L → κ(z) ⊗[k] L`.
Source: Stacks Project, Divisors, Tag 05DC, and Schemes, Tag 01I4.
(blueprint: lem-trf-field-extension-residual-generic-components) -/
noncomputable def fieldExtensionResidualRight {k L : Type u} [Field k] [Field L]
    [Algebra k L] {Z : Scheme.{u}} [Z.Over (Spec (.of k))] (z : Z) :
    CommRingCat.of L ⟶ fieldExtensionResidualRing (k := k) (L := L) z :=
  letI := ((Z ↘ Spec (.of k)).residueFieldAlgebraMap z).toAlgebra
  CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := k) (A := Z.residueField z) (B := L)).toRingHom

/-- Under any field extension, the residual fibre is canonically the spectrum of
`κ(z) ⊗[k] L`; the two projection identities uniquely specify the isomorphism.
A point is component generic precisely when its image and residual-fibre point are.
Its closure is then a component, also when lifted through any closed immersion.

Source: Stacks Project, More on Morphisms, Tag 0GSI; Divisors, Tag 05DC; Algebra,
Tag 00HS. (blueprint: lem-trf-field-extension-residual-generic-components)

Proof plan:
1. On an affine neighbourhood, component-generic points are minimal primes
   (lem-weil-pbc-spec-irreducible-components-minimal-primes). Open locality shows
   that this is equivalent to having no proper generalization in the whole scheme.
2. Reassociate the two pullbacks and apply the affine tensor-product identification
   (lem-weil-pbc-fibre-product-affine-spectra). The universal property gives the
   unique isomorphism preserving both projections. The fibre homeomorphism identifies
   residual-fibre generalizations with ambient generalizations over the same point.
3. On an affine neighbourhood of the image, the projection is the spectrum of
   `A → A ⊗[k] L` (lem-weil-pbc-open-fibre-product). It is flat by
   lem-pc-field-extension-flat, lem-weil-pbc-flat-morphism-base-change, and
   lem-weil-pbc-flat-ring-map-iff-flat-affine.
4. Flat going-down (lem-sc-flat-going-down) makes the contraction of a minimal prime
   minimal. Every fibre generalization is ambient, proving the forward implication.
5. Conversely, a generalization has the same image by genericity of that image,
   and hence is a fibre generalization; fibre genericity makes it the original point.
6. A closed immersion identifies its source with a closed subspace. Singleton closure
   is preserved, and an irreducible set strictly containing the lifted closure would
   contradict maximality of the ambient component. No finiteness or reducedness is used.
-/
theorem field_extension_residual_generic_components
    {k L : Type u} [Field k] [Field L] [Algebra k L]
    (Z : Scheme.{u}) [Z.Over (Spec (.of k))]
    (w : pullback (C := Scheme.{u}) (Z ↘ Spec (.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    (∃! e : (pullback.fst (Z ↘ Spec (.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))).fiber
        ((pullback.fst (Z ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))) w) ≅
          Spec (fieldExtensionResidualRing (k := k) (L := L) ((pullback.fst (Z ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))) w)),
      e.hom ≫ Spec.map (fieldExtensionResidualLeft (k := k) (L := L)
        ((pullback.fst (Z ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))) w)) = ((pullback.fst (Z ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k L))))).fiberToSpecResidueField
          ((pullback.fst (Z ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))) w) ∧
      e.hom ≫ Spec.map (fieldExtensionResidualRight (k := k) (L := L)
        ((pullback.fst (Z ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))) w)) =
          ((pullback.fst (Z ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k L))))).fiberι ((pullback.fst (Z ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))) w) ≫ (pullback.snd (Z ↘ Spec (.of k))
            (Spec.map (CommRingCat.ofHom (algebraMap k L))))) ∧
    (w ∈ genericPoints _ ↔
      (pullback.fst (Z ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))) w ∈ genericPoints Z ∧
      ((pullback.fst (Z ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k L))))).asFiber w ∈ genericPoints _) ∧
    (w ∈ genericPoints _ →
      closure {w} ∈ irreducibleComponents _ ∧
      ∀ (T : Scheme.{u}) (j : T ⟶ pullback (C := Scheme.{u}) (Z ↘ Spec (.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))) [IsClosedImmersion j]
          (v : T), j v = w →
        j '' closure {v} = closure {w} ∧ v ∈ genericPoints T) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
