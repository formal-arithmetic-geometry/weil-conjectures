/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Smooth projective compactification of a normal finite-field curve

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-i-real-compactification,
lemma and proof lem-wf-curve-normal-smooth-compactification, paragraphs 1–3
(blueprint: lem-wf-curve-normal-smooth-compactification).

The boundary carries Mathlib's canonical reduced induced closed subscheme structure, defined
by the vanishing ideal sheaf of the complement of the open image.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A normal geometrically connected finite-field curve has a smooth projective geometrically
connected compactification with reduced boundary finite over the base field.
Source: blueprint main-20261015, sec-purity-real-sheaves/sk-i-real-compactification,
lem-wf-curve-normal-smooth-compactification, paragraphs 1–3; Stacks Tags 00TV and 0B3I
(blueprint: lem-wf-curve-normal-smooth-compactification).

Proof:
1. Finite type gives local Noetherianity and geometric connectedness gives connectedness. The
   stalks are domains, so the connected locally Noetherian `U` is irreducible
   (`irreducibleSpace_of_isDomain_stalk`). Its unique irreducible component is the whole space,
   so the pure-dimension hypothesis (def-weil-pure-dimension) gives `dim U = 1`.
2. Apply `AlgebraicGeometry.exists_smooth_projectiveCompactification` (the blueprint proof:
   normal dimension-one stalks are DVRs, lem-sc-normal-dim1-dvr, so `U` is regular, hence smooth
   over the perfect field, lem-trf-regular-perfect-field-smooth; Nagata compactification,
   sk-thm-nagata-compactification, followed by the normalization of the compactification in `U`,
   def-sc-normalization and lem-sc-normalization-properties; the projective closure
   lem-wf-finite-field-curve-quasi-projective of the proper completion is the completion itself;
   the boundary is finite by lem-sc-dim0-finite). It gives smoothness of `U`, a compactification
   `C` smooth of relative dimension one, geometrically connected, with a closed immersion into a
   projective space, `U` dense, and finite complement.
3. `C` is smooth and connected, hence regular and integral, of dimension one; with the
   projective embedding this is a smooth projective curve.
4. The canonical reduced boundary `D`, the subscheme of the vanishing ideal of the complement
   (def-weil-pbc-scheme-reduction), has image the complement, a finite set, so `D` has finitely
   many points. Its morphism to `Spec K` has finite fibres, hence is locally quasi-finite; it is
   quasi-compact (`C` is proper), so it is finite (`IsFinite.of_locallyQuasiFinite`).
-/
theorem exists_smooth_projectiveCompactification_normal
    {K : Type u} [Field K] [Finite K] {U : Scheme.{u}}
    (p : U ⟶ Spec (.of K)) [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [GeometricallyConnected p]
    (hU : ∀ x : U,
      IsDomain (U.presheaf.stalk x) ∧ IsIntegrallyClosed (U.presheaf.stalk x))
    (hdim : U.IsPureDimension 1) :
    Smooth p ∧ ∃ (C : Scheme.{u}) (pC : C ⟶ Spec (.of K))
      (j : U ⟶ C) (_ : IsOpenImmersion j),
      j ≫ pC = p ∧ IsSmoothProjectiveCurve pC ∧ GeometricallyConnected pC ∧
        DenseRange j.base ∧
          IsFinite ((Scheme.IdealSheafData.vanishingIdeal
            ⟨(j.opensRange : Set C)ᶜ, j.opensRange.isOpen.isClosed_compl⟩).subschemeι ≫ pC) := by
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian p
  have : ConnectedSpace U :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := p)
  have : IrreducibleSpace U := irreducibleSpace_of_isDomain_stalk U fun x ↦ (hU x).1
  have hdim' : topologicalKrullDim U = 1 := by
    have hu : (Set.univ : Set U) ∈ irreducibleComponents U := by
      simp only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff]
    simpa [(Homeomorph.Set.univ U).isHomeomorph.topologicalKrullDim_eq] using
      hdim Set.univ hu
  have : IsCurve p := { krullDim_le_one := hdim'.le }
  obtain ⟨hsmooth, c, hcurve, hreldim, hgeom, hproj, hdense, hfin⟩ :=
    exists_smooth_projectiveCompactification p hU hdim'
  have : SmoothOfRelativeDimension 1 p := hsmooth
  have : IsCurve c.g := hcurve
  have : SmoothOfRelativeDimension 1 c.g := hreldim
  have : Smooth c.g := SmoothOfRelativeDimension.smooth 1 c.g
  have : GeometricallyConnected c.g := hgeom
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : IsRegular c.Z := IsRegular.of_smooth c.g
  have : ConnectedSpace c.Z :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := c.g)
  have : IsIntegral c.Z := IsRegular.isIntegral c.Z
  have : IsProjective c.g :=
    { exists_isClosedImmersion := hproj }
  have : IsIntegralCurve c.g :=
    { isIntegral := inferInstance
      topologicalKrullDim_eq_one :=
        topologicalKrullDim_eq_of_smoothOfRelativeDimension c.g 1 }
  have : IsSmoothProjectiveCurve c.g := {}
  have : IsOpenImmersion c.i := c.isOpenImmersion
  refine ⟨SmoothOfRelativeDimension.smooth 1 p, c.Z, c.g, c.i, inferInstance,
    c.comm.symm, inferInstance, hgeom, hdense, ?_⟩
  let D := Scheme.IdealSheafData.vanishingIdeal
    ⟨(c.i.opensRange : Set c.Z)ᶜ, c.i.opensRange.isOpen.isClosed_compl⟩
  have hrange : Set.range D.subschemeι.base = (Set.range c.i.base)ᶜ := by
    simp only [D, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, TopologicalSpace.Closeds.coe_mk,
      Scheme.Hom.coe_opensRange]
  have hD : (Set.univ : Set D.subscheme).Finite := by
    refine (hfin.preimage D.subschemeι.isClosedEmbedding.injective.injOn).subset ?_
    intro z _
    exact hrange ▸ ⟨z, rfl⟩
  have : Finite D.subscheme := Set.finite_univ_iff.mp hD
  have : LocallyQuasiFinite (D.subschemeι ≫ c.g) :=
    .of_finite_preimage_singleton _ fun _ ↦ Set.toFinite _
  have : IsProper c.g := c.isProper
  exact IsFinite.of_locallyQuasiFinite (D.subschemeι ≫ c.g)

end AlgebraicGeometry
