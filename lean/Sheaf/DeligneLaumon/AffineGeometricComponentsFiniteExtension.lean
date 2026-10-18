/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Connected.Clopen

import Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.DescendQCOpenFGSubalgebra
import Sheaf.AlgebraicGeometry.SpecSurjectiveBaseChange
import Sheaf.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Geometric components after a finite constant extension

Source: Stacks Project, varieties.tex, Tags 038E and 0387; morphisms.tex, Tags 01VB and 02NK
(blueprint: lem-zl-affine-geometric-components-finite-extension).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

/-- The data expressing a finite-field decomposition into affine open-and-closed geometric
components.  The maps `baseComponent` are characterized by their two pullback projections, so
that they are the canonical base changes of the inclusions `inclusion`.
Source: Stacks Project, varieties.tex, Tags 038E and 0387
(blueprint: lem-zl-affine-geometric-components-finite-extension). -/
structure AffineGeometricComponentDecomposition
    (D : WeilConjectures.FiniteFieldDatum.{u}) {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (CommRingCat.of D.k₀)) (e : ℕ) (he : 1 ≤ e) where
  I : Type u
  finite_I : Finite I
  component : I → Scheme.{u}
  componentMap : ∀ i, component i ⟶
    Spec (CommRingCat.of (D.extensionSubfield e he))
  inclusion : ∀ i, component i ⟶
    pullback f₀ (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he)))
  inclusion_over : ∀ i, inclusion i ≫
      pullback.snd f₀ (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he))) = componentMap i
  affine : ∀ i, IsAffine (component i)
  nonempty : ∀ i, Nonempty (component i).carrier
  open_closed : ∀ i, IsOpenImmersion (inclusion i) ∧ IsClosedImmersion (inclusion i)
  cover : Set.univ = ⋃ i, Set.range (inclusion i).base
  pairwise_disjoint : ∀ ⦃i j⦄, i ≠ j →
    Disjoint (Set.range (inclusion i).base) (Set.range (inclusion j).base)
  geometrically_connected : ∀ i, GeometricallyConnected (componentMap i)
  baseComponent : ∀ i,
    pullback (componentMap i)
      (Spec.map (CommRingCat.ofHom ((D.extensionSubfield e he).subtype))) ⟶
      pullback f₀ (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
  baseComponent_fst : ∀ i, baseComponent i ≫
      pullback.fst f₀ (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
    pullback.fst (componentMap i)
      (Spec.map (CommRingCat.ofHom ((D.extensionSubfield e he).subtype))) ≫
      inclusion i ≫ pullback.fst f₀
        (Spec.map (CommRingCat.ofHom (D.extensionEmbedding e he)))
  baseComponent_snd : ∀ i, baseComponent i ≫
      pullback.snd f₀ (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) =
    pullback.snd (componentMap i)
      (Spec.map (CommRingCat.ofHom ((D.extensionSubfield e he).subtype)))
  componentPoint : ∀ i,
    (pullback (componentMap i)
      (Spec.map (CommRingCat.ofHom ((D.extensionSubfield e he).subtype)))).carrier
  component_range : ∀ i, Set.range (baseComponent i).base =
    connectedComponent ((baseComponent i).base (componentPoint i))
  components_bijective : Function.Bijective (fun i ↦
    ConnectedComponents.mk ((baseComponent i).base (componentPoint i)))

/-- Geometric connected components of an affine finite-type scheme over a finite field descend to a
finite constant extension.
Source: Stacks Project, varieties.tex, Tag 038E
(lemma-galois-action-connected-components-continuous), and Tag 0387
(lemma-characterize-geometrically-connected); morphisms.tex, Tags 01VB and 02NK.
Proof:
1. Identify every affine field base change with Spec of the tensor product by
   lem-weil-pbc-fibre-product-affine-spectra. Finite type survives base change by
   lem-sfb-finite-type-composition-base-change; lem-pc-affine-finite-type-algebra and
   lem-wf-affine-noetherian-components make the geometric fibre Noetherian.
2. By lem-sfb-noetherian-connected-components-open its nonempty connected components
   form a finite open partition. Each is closed since its complement is the union of
   the other opens, and quasi-compact by lem-sfb-noetherian-space-compact-subsets.
3. Descend each quasi-compact open to a finitely generated base subalgebra using
   lem-weil-pbc-descend-qc-open-fg-subalgebra. This initially asserts only openness.
4. Take the finite union of algebra generating sets. Algebraicity of the closure and
   lem-weil-pbc-algebraic-generators-finite-extension put these coefficients in one
   finite intermediate field L. Its degree e is positive, and a basis shows its
   cardinality is q^e. By lem-weil-unique-subfield-of-closure it is D.extensionSubfield.
5. Pull the descended opens up to L by lem-weil-pbc-open-immersion-base-change.
   Base-change pasting (def-pc-base-change) identifies their base changes to k with
   the original component opens, with their restricted scheme structure.
6. The projection from k to L is surjective by lem-pc-field-extension-surjective and
   lem-weil-pbc-spec-surjective-base-change. Reflect disjointness and coverage along
   this surjection. Nonemptiness upstairs gives nonemptiness downstairs; the
   complement of each descended open is the union of the others, so it is closed.
7. By lem-weil-pbc-spec-clopen-idempotent each descended clopen is a basic open of an
   idempotent; lem-weil-pbc-affine-open-section-vanishing-prime makes it affine.
   The disjoint open inclusions glue to the coproduct isomorphism with the base change.
8. The closure k is also algebraic and algebraically closed over L. Connectedness of
   the base-changed components and lem-weil-geometrically-connected-algebraic-closure
   give geometric connectedness. Their ranges identify exactly the connected components.
   If the original scheme is empty, take e = 1 and the empty component index.
9. Smooth relative dimension d survives base change by
   lem-sbc-smooth-relative-dimension-permanence. The inclusions are etale by
   lem-weil-pbc-open-immersion-etale, thus smooth of dimension zero. Composition in
   the same permanence lemma gives smooth relative dimension 0 + d = d.
(blueprint: lem-zl-affine-geometric-components-finite-extension). -/
theorem exists_affine_geometric_components_finite_extension
    (D : WeilConjectures.FiniteFieldDatum.{u}) {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (CommRingCat.of D.k₀)) [IsAffine X₀]
    [LocallyOfFiniteType f₀] [QuasiCompact f₀] :
    ∃ (e : ℕ) (he : 1 ≤ e),
      ∃ (H : AffineGeometricComponentDecomposition D f₀ e he),
        ∀ (d : ℕ), SmoothOfRelativeDimension d f₀ →
          ∀ (i : H.I), SmoothOfRelativeDimension d (H.componentMap i) := by
  sorry

end AlgebraicGeometry
