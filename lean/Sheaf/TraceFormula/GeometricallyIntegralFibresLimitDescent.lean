/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Topology.Constructible
import Mathlib.Topology.Irreducible
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.SubsetGeometricIrreducibility
import WeilConjectures.AlgebraicGeometry.LimitContainedInConstructible
import Sheaf.TraceFormula.GeometricFibreComponentCountBaseChange
import Sheaf.TraceFormula.GeometricallyIrreducibleFibreLocus
import Sheaf.AlgebraicGeometry.GeometricallyReducedFibreLocus

/-!
# Geometrically integral fibres descend to a directed tail

Source: Stacks Project, More on Morphisms, Tags 05FG and 05FH, simultaneous
constructible-locus argument for a fixed finitely presented algebra; Limits, Tag 05F4
(blueprint: lem-trf-geometrically-integral-fibres-limit-descent).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- If every fibre of a fixed finite-presentation model over a directed ring colimit
is geometrically integral, every fibre at every sufficiently late stage is geometrically
integral. No flatness, Noetherian or injectivity condition is imposed.

The tensors are written with the new base first, so their canonical base algebra structure
is Mathlib's global left algebra structure. Tensor symmetry identifies them with the order
in the node. `p.asIdeal.Fiber B` is the residue-field tensor `κ(p) ⊗ B`.
The two applications of `id` install exactly the algebra structures induced by the cocone
map and the transition map; they do not quantify over extra chosen actions.

Source: Stacks Project, More on Morphisms, Tags 05FG and 05FH, proofs, using Tags 0579,
055B, 0576 and 0556, and Limits, Tag 05F4.
(blueprint: lem-trf-geometrically-integral-fibres-limit-descent)

Proof, following the node:
1. Apply lem-weil-pbc-spec-colimit-limit to the given ring colimit. The spectra form an
   inverse system with affine transitions and the specified limit. Every stage is qcqs by
   lem-weil-pbc-affine-scheme-qcqs. The tensor spectra are the base changes of Spec C by
   lem-weil-pbc-fibre-product-affine-spectra, with their canonical projection maps.
2. The reduced and irreducible fibre loci of C over the fixed stage are constructible by
   lem-trf-geometrically-reduced-fibre-locus and lem-trf-geometrically-irreducible-fibre-locus.
   Their intersection E is constructible by def-weil-constructible-subset and is exactly
   the integral fibre locus by def-pc-geometrically-irreducible and def-pc-integral-scheme.
3. A fibre over a separable closure (def-pd-separable-closure) is irreducible precisely when
   it has one irreducible component: use def-weil-irreducible-components and
   lem-sc-irreducible-components-cover, then lem-sbc-subset-geometric-irreducibility on the
   whole fibre. Irreducibility includes nonemptiness; an empty fibre has zero components.
4. For any base map from the fixed stage, tensor associativity and the pure-tensor formulas
   in lem-weil-pbc-algebra-tensor-pushout-universal-property identify the new fibres with
   scalar extensions of the old fibres. The reduced locus commutes with this base change
   by lem-trf-geometrically-reduced-fibre-locus. The component count is unchanged by
   lem-trf-geometric-fibre-component-count-base-change; step 3 identifies its value one
   with geometric irreducibility. Thus the new integral locus is the inverse image of E.
5. The hypothesis and step 4 put the image of the limit spectrum inside E. Apply
   lem-weil-pbc-limit-contained-in-constructible at a, using the qcqs and affine-transition
   hypotheses from step 1, to obtain a single b above a whose entire tail maps into E.
6. Step 4 at every stage of that tail gives reduced, irreducible and nonempty fibres after
   every residue-field extension, hence integral fibres by def-pc-integral-scheme. -/
theorem exists_eventually_geometricallyIntegral_fibres
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : I ⥤ CommRingCat.{u}) (c : Cocone D) (hc : IsColimit c)
    (a : I) (C : Type u) [CommRing C] [Algebra (D.obj a) C]
    [Algebra.FinitePresentation (D.obj a) C]
    (hgeom : @_root_.id (∀ [Algebra (D.obj a) c.pt], Prop)
      (fun [Algebra (D.obj a) c.pt] ↦
        ∀ p : PrimeSpectrum c.pt,
          GeometricallyIntegral (Spec.map (CommRingCat.ofHom
            (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber (c.pt ⊗[D.obj a] C))))))
      (c.ι.app a).hom.toAlgebra) :
    ∃ b : I, ∃ hab : a ≤ b, ∀ (j : I) (hbj : b ≤ j),
      @_root_.id (∀ [Algebra (D.obj a) (D.obj j)], Prop)
        (fun [Algebra (D.obj a) (D.obj j)] ↦
          ∀ q : PrimeSpectrum (D.obj j),
            GeometricallyIntegral (Spec.map (CommRingCat.ofHom
              (algebraMap q.asIdeal.ResidueField
                (q.asIdeal.Fiber (D.obj j ⊗[D.obj a] C))))))
        (D.map (homOfLE (hab.trans hbj))).hom.toAlgebra := by
  sorry

end AlgebraicGeometry
