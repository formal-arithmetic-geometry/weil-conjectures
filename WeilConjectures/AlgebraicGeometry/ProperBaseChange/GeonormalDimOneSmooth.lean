/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricRegularitySmoothFieldCriterion

/-!
# Geometrically normal schemes of dimension at most one

Source: Stacks Project, Tags 0BX2, 038X, 00P3, 033M, and the proof of Tag 0GK5
(blueprint: lem-weil-pbc-geonormal-dim-one-smooth).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A geometrically normal finite type scheme of dimension at most one over a field is
smooth and geometrically reduced; any connected nonempty field base change is irreducible.
Source: Stacks Project, Tags 0BX2, 038X, 00P3, 033M; proof of Tag 0GK5
(blueprint: lem-weil-pbc-geonormal-dim-one-smooth).

Proof:
1. Fix an extension `L/k`. A finite affine cover of `Z` base changes to a cover by
   spectra of finite type `L`-algebras, using
   `lem-weil-pbc-fibre-product-affine-spectra` and the open-immersion pullback property.
   Fields are Noetherian, so `lem-weil-pbc-finite-type-over-noetherian` makes this
   base change Noetherian, and hence all its local rings Noetherian.
2. Each affine chart has dimension at most one, by taking closures of chains.
   `lem-weil-pbc-dimension-preserved-field-extension` preserves this bound after
   scalar extension. By `lem-sc-scheme-stalk-dimension-generalization-chains`, the
   dimension of each stalk is at most the dimension of its chart, hence at most one.
3. The hypothesis makes every such stalk an integrally closed domain. A zero-dimensional
   local domain is a field, thus regular. In dimension one, `lemma-proper-smooth-model--1`
   makes it a discrete valuation ring, whose principal maximal ideal makes it regular
   (`def-sc-discrete-valuation-ring`). Thus every field base change is regular.
4. Apply `lem-weil-pbc-geometric-regularity-smooth-field-criterion` to obtain smoothness:
   the structure map is locally of finite type and every finitely generated field base
   change has regular local rings. No perfectness of the field is needed.
5. Every stalk of every field base change is a domain, hence reduced: a nilpotent
   element in a domain is zero. By `def-pc-reduced-scheme` these base changes are reduced,
   which is geometric reducedness (`def-pc-geometrically-irreducible`).
6. If a field base change is connected and nonempty, its regularity and local
   Noetherianity give integrality by `lem-sc-regular-connected-integral`, and then
   irreducibility by `lem-pc-integral-scheme-irreducible`. The empty scheme satisfies
   the first two conclusions and never meets this final antecedent.
-/
theorem smooth_and_geometricallyReduced_of_geonormal_dim_le_one
    (k : Type u) [Field k] (Z : Scheme.{u}) [Z.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k))]
    [QuasiCompact (Z ↘ Spec (CommRingCat.of k))]
    (hdim : topologicalKrullDim Z ≤ 1)
    (hnormal : ∀ (L : Type u) [Field L] [Algebra k L],
      ∀ x : ↥(pullback (Z ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))),
      IsDomain ((pullback (Z ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.stalk x) ∧
      IsIntegrallyClosed ((pullback (Z ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))).presheaf.stalk x)) :
    Smooth (Z ↘ Spec (CommRingCat.of k)) ∧
      GeometricallyReduced (Z ↘ Spec (CommRingCat.of k)) ∧
      ∀ (L : Type u) [Field L] [Algebra k L],
        ConnectedSpace ↥(pullback (Z ↘ Spec (CommRingCat.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))) →
        IrreducibleSpace ↥(pullback (Z ↘ Spec (CommRingCat.of k))
          (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
  have hregular (L : Type u) [Field L] [Algebra k L] :
      IsRegular (pullback (Z ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
    have := LocallyOfFiniteType.isLocallyNoetherian
      (pullback.snd (Z ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    exact IsRegular.of_isIntegrallyClosed_stalk (hnormal L)
      ((topologicalKrullDim_pullback_eq_of_field (Z ↘ Spec (CommRingCat.of k))
        (Spec.map (CommRingCat.ofHom (algebraMap k L)))).le.trans hdim)
  have hsmooth : Smooth (Z ↘ Spec (CommRingCat.of k)) := by
    apply (smooth_iff_regularLocalRing_finitelyGenerated_field_baseChange k _).mpr
    intro L _ _ _ x
    have := hregular L
    exact IsRegular.isRegularLocalRing_stalk x
  have hreduced : GeometricallyReduced (Z ↘ Spec (CommRingCat.of k)) := by
    refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr ?_⟩
    intro L _ _
    refine @isReduced_of_isReduced_stalk _ (fun x ↦ ?_)
    have := (hnormal L x).1
    infer_instance
  refine ⟨hsmooth, hreduced, ?_⟩
  intro L _ _ hconnected
  have := hconnected
  have := hregular L
  have := LocallyOfFiniteType.isLocallyNoetherian
    (pullback.snd (Z ↘ Spec (CommRingCat.of k))
      (Spec.map (CommRingCat.ofHom (algebraMap k L))))
  have := IsRegular.isIntegral (pullback (Z ↘ Spec (CommRingCat.of k))
    (Spec.map (CommRingCat.ofHom (algebraMap k L))))
  infer_instance

end AlgebraicGeometry
