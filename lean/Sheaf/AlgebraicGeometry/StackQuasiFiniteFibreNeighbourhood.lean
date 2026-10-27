/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicModuliStack
public import Sheaf.AlgebraicGeometry.DmStackMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleDimension
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
import Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus
import Sheaf.AlgebraicGeometry.RepresentableLocallyQuasiFiniteCalculus
import Sheaf.AlgebraicGeometry.IsLocallyQuasiFiniteEtaleSource
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Sheaf.AlgebraicGeometry.LocallyQuasiFiniteRelativeDimension
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.Mathlib.Topology.KrullDimension

/-! # A locally quasi-finite neighbourhood from a zero-dimensional field fibre

Source: Stacks Project, Morphisms of Stacks, Tag 06ME; Properties of Stacks,
Tags 06M3 and 06M5(2); Morphisms of Spaces, Tags 04NV and 04NW
(blueprint: lem-sfb-stack-quasifinite-fibre-neighbourhood).

The given equivalence identifies the algebraic space `F` with the actual 2-fibre
product, and its projection comparison fixes the map `p` to the source `A`.
No atlas, Noetherian condition, or quasi-compactness condition is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

namespace CategoryTheory

/-- A zero-dimensional point of a field fibre gives an open source neighbourhood
on which a locally finite type map from an algebraic space is locally quasi-finite.
Source: Stacks Project, Tag 06ME
(blueprint: lem-sfb-stack-quasifinite-fibre-neighbourhood).

Proof: (1) The algebraic-stack diagonal makes maps from algebraic spaces representable
[lem-sfb-stack-diagonal-space-source-representability]. Thus the fibre is an algebraic
space; local finite type passes to it by [lem-sfb-stack-chartwise-smooth-etale-calculus].
(2) Apply [lem-sfb-source-local-property-locus-descent] to local quasi-finiteness.
Its base-change and fppf-target descent laws are
[lem-sfb-representable-lqf-calculus-descent]. Etale source locality follows from
[lem-a1-scheme-lqf-etale-source-locality], with overlaps supplied by
[lem-trf-space-fibre-products-etale-covers]. For jointly surjective families use the
scheme coproduct [lem-weil-pbc-scheme-coproduct-family]. The largest open on a scheme
target is [lem-sfb-space-quasifinite-locus-open]; its formation commutes with base change.
Consequently the largest locally quasi-finite open of `A` pulls back to that of `F`.
(3) Every etale chart lift of `z` has local dimension zero. To compare two chart lifts,
extend their residue fields to a common field and use their common point in the scheme
chart fibre product. Its etale projections preserve local dimension by
[lem-sfb-etale-topological-dimension-at-point]. The minimum description in
[def-kun-topological-dimension-at-point] gives a zero-dimensional open neighbourhood
of the lift. Its map to the field is locally of finite type and has relative dimension
zero, so [lem-trf-locally-quasi-finite-relative-dimension-zero] makes it locally
quasi-finite. Its affine neighbourhoods are also affine neighbourhoods in the original
chart [pqf-def-quasifinite]. Hence `z` lies in the largest locally quasi-finite open of `F`.
(4) By the base-change equality, `p(z)` lies in the largest locally quasi-finite open
of `A`. Take that open for the required neighbourhood. -/
theorem exists_open_locallyQuasiFinite_of_field_fibre_dimension_zero
    {S : Scheme.{u}} (X : BasedCategory.{v, w} (Over S))
    (hX : IsAlgebraicModuliStack X) (A : AlgebraicSpace S)
    (h : BasedFunctor (discreteModuli A.obj.obj) X)
    (hft : ModuliSpaceTest @LocallyOfFiniteType h)
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ S)
    (a : BasedFunctor (discreteModuli (yoneda.obj (Over.mk s))) X)
    (F : AlgebraicSpace S) (p : F.obj.obj ⟶ A.obj.obj)
    (e : BasedFunctor (discreteModuli F.obj.obj) (moduliTwoFiberProduct h a))
    (he : e.toFunctor.IsEquivalence)
    (hp : Nonempty (ModuliTwoIso (e.comp (moduliTwoFiberFst h a)) (discreteModuliMap p)))
    (z : Point F.obj.obj) (hz : etaleLocalDimension F.obj.obj z = 0) :
    ∃ V : OpenSubspace A,
      mapPoint p z ∈ pointImage V.val.ι ∧
        ModuliSpaceTest @Scheme.Hom.IsLocallyQuasiFinite
          ((discreteModuliMap V.val.ι).comp h) := by
  sorry

end CategoryTheory
