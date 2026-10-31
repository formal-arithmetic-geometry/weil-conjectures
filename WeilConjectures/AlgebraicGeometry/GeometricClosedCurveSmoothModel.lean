/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import WeilConjectures.ZetaSeries

import WeilConjectures.AlgebraicGeometry.FiniteFieldClosedSubschemeDescent
import WeilConjectures.AlgebraicGeometry.ClosedPointField
import WeilConjectures.AlgebraicGeometry.GeometricallyConnectedAlgebraicClosure
import WeilConjectures.AlgebraicGeometry.FieldExtensionComponentLocalDimension
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import WeilConjectures.PointCount
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-! # Smooth finite-field models of prescribed geometric closed curves

Source: Weil conjectures blueprint, `sec-deligne-laumon-general`,
`sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`, paragraph 2
(blueprint: lem-zl-geometric-closed-curve-smooth-model).

The model and its comparison isomorphism are chosen before quantifying over geometric
points. Thus one model works for every prescribed finite set, including the empty set.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

private theorem component_dimensions_homeomorph
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (d : ℕ)
    (h : ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (d : WithBot ℕ∞)) :
    ∀ Z ∈ irreducibleComponents Y, topologicalKrullDim Z = (d : WithBot ℕ∞) := by
  intro Z hZ
  have hpre : e ⁻¹' Z ∈ irreducibleComponents X :=
    preimage_mem_irreducibleComponents hZ e.isOpenEmbedding (by
      simpa only [e.surjective.range_eq, Set.inter_univ] using hZ.1.nonempty)
  have he := (e.symm.image Z).isHomeomorph.topologicalKrullDim_eq (e.symm.image Z)
  rw [e.symm.image_eq_preimage_symm] at he
  exact he.trans (h _ hpre)

private theorem local_dimension_homeomorph_le
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) : topologicalKrullDimAt x ≤ topologicalKrullDimAt (e x) := by
  refine le_iInf₂ fun U hx ↦ ?_
  let V : TopologicalSpace.Opens X := ⟨e ⁻¹' U, U.isOpen.preimage e.continuous⟩
  let eV : V ≃ₜ U := e.subtype (fun _ ↦ Iff.rfl)
  exact (iInf₂_le V hx).trans_eq (eV.isHomeomorph.topologicalKrullDim_eq eV)

private theorem local_dimension_homeomorph
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) : topologicalKrullDimAt x = topologicalKrullDimAt (e x) := by
  exact le_antisymm (local_dimension_homeomorph_le e x)
    (by simpa using local_dimension_homeomorph_le e.symm (e x))

/-- A prescribed smooth connected affine geometric closed curve has a smooth geometrically
connected affine finite-field model of pure dimension one. Every geometric point has closed
image with finite residue field extension on this same model.
Source: blueprint `thm-zl-real-mixed-by-curves.proof.md`, paragraph 2
(blueprint: lem-zl-geometric-closed-curve-smooth-model).

Proof:
1. Apply lem-zl-bertini-finite-field-descent to the given closed immersion. Obtain m >= 1,
   a closed model immersion, and the base-change isomorphism compatible with the embedding.
   This descends the prescribed closed subscheme itself, without taking its reduction.
2. Affine base change makes the ambient model affine. Its closed subscheme is affine;
   the closed immersion is locally of finite type and quasi-compact. Composition with
   the ambient structure morphism gives finite type of the model by
   lem-sfb-finite-type-composition-base-change.
3. By lem-pc-field-extension-flat the map Spec k -> Spec k_m is flat. Both spectra have
   one point, so it is also surjective and quasi-compact. By
   lem-weil-pbc-surjective-base-change, the projection from C to the model is surjective.
4. Apply lem-trf-smooth-fpqc-base-descent (Stacks 02VL) along that field extension to
   descend smoothness. Apply lem-weil-geometrically-connected-algebraic-closure (0387)
   to the connected base change C to obtain geometric connectedness of the model.
5. Apply lem-sbc-equidimensional-open-local-dimension to the top open of C to obtain
   local dimension one. Lift each model point using step 3 and the comparison isomorphism.
   Homeomorphism invariance and lem-trf-field-extension-component-local-dimension give
   local dimension one on the model. It is locally Noetherian, so
   lem-sbc-constant-local-dimension-components on its top open gives pure dimension one.
6. The residue field of the image of a k-point embeds into k over k_m by
   def-weil-residue-field. It is algebraic over k_m because k/k₀ is algebraic.
   Apply lem-kun-closed-point-field (a) to conclude closedness and finite residue degree.
7. The model was fixed in step 1, independently of the point. Step 6 holds universally,
   so applies simultaneously to each member of any prescribed finite set of points. -/
theorem exists_smooth_closed_curve_finiteField_model (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (CommRingCat.of D.k₀)))
    [IsAffine X₀.left] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (C : Scheme.{u}) (i : C ⟶ (D.geometricFiber X₀).left)
    [IsClosedImmersion i] [IsAffine C] [ConnectedSpace C]
    [Smooth (i ≫ (D.geometricFiber X₀).hom)] (hC : C.IsPureDimension 1) :
    ∃ (m : ℕ) (hm : 1 ≤ m)
      (Cₘ : Over (Spec (CommRingCat.of (D.extensionSubfield m hm))))
      (iₘ : Cₘ ⟶ (Over.pullback
        (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj X₀),
      IsAffine Cₘ.left ∧ LocallyOfFiniteType Cₘ.hom ∧ QuasiCompact Cₘ.hom ∧
      IsClosedImmersion iₘ.left ∧ Smooth Cₘ.hom ∧ GeometricallyConnected Cₘ.hom ∧
      Cₘ.left.IsPureDimension 1 ∧
      ∃ e : Over.mk (i ≫ (D.geometricFiber X₀).hom) ≅
          (Over.pullback (Spec.map
            (CommRingCat.ofHom (D.extensionSubfield m hm).subtype))).obj Cₘ,
        (e.hom.left ≫
            pullback.fst Cₘ.hom
              (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)) ≫
            iₘ.left ≫
            pullback.fst X₀.hom
              (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))) =
          i ≫ pullback.fst X₀.hom
            (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) ∧
        ∀ (c : Over.mk (𝟙 (Spec (CommRingCat.of D.k))) ⟶
            Over.mk (i ≫ (D.geometricFiber X₀).hom)) (z : Cₘ.left),
          (e.hom.left ≫ pullback.fst Cₘ.hom
              (Spec.map (CommRingCat.ofHom (D.extensionSubfield m hm).subtype)))
            (c.left (IsLocalRing.closedPoint D.k)) = z →
          z ∈ closedPoints Cₘ.left ∧ (Cₘ.hom.residueFieldAlgebraMap z).Finite := by
  classical
  obtain ⟨m, hm, Cₘ, iₘ, hiₘ, ⟨e, he⟩, _⟩ :=
    D.exists_closed_subscheme_finiteField_descent X₀ C i
  have := hiₘ
  let E := D.extensionSubfield m hm
  let t := Spec.map (CommRingCat.ofHom E.subtype)
  have hAffineAmbient : IsAffine ((Over.pullback
      (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj X₀).left :=
    inferInstanceAs (IsAffine (pullback X₀.hom _))
  have : IsAffine Cₘ.left := isAffine_of_isAffineHom iₘ.left
  have hft : LocallyOfFiniteType Cₘ.hom := by
    rw [← Over.w iₘ]
    have : LocallyOfFiniteType ((Over.pullback
        (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))).obj X₀).hom :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom _))
    infer_instance
  have hqc : QuasiCompact Cₘ.hom := by
    rw [← Over.w iₘ]
    infer_instance
  have htS : Surjective t := inferInstance
  have htF : Flat t := inferInstance
  have htQ : QuasiCompact t := inferInstance
  have hsm : Smooth (pullback.snd Cₘ.hom t) := by
    change Smooth ((Over.pullback
      (Spec.map (CommRingCat.ofHom E.subtype))).obj Cₘ).hom
    rw [← Over.w e.inv]
    change Smooth (e.inv.left ≫ (i ≫ (D.geometricFiber X₀).hom))
    infer_instance
  have hs : Smooth Cₘ.hom :=
    MorphismProperty.of_pullback_snd_of_descendsAlong
      (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨⟨htS, htF⟩, htQ⟩ hsm
  have hconn : ConnectedSpace ↥(pullback Cₘ.hom t) :=
    e.hom.left.homeomorph.connectedSpace_iff.mp (by
      change ConnectedSpace C
      infer_instance)
  let : Cₘ.left.Over (Spec (CommRingCat.of E)) := ⟨Cₘ.hom⟩
  have : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  have hg : GeometricallyConnected Cₘ.hom :=
    (geometricallyConnected_iff_connectedSpace_of_isAlgClosed
      (k := E) (Ω := D.k) Cₘ.left).mpr hconn
  have hCtop := component_dimensions_homeomorph (Homeomorph.Set.univ C).symm 1 hC
  have hlocalC (x : C) : topologicalKrullDimAt x = (1 : WithBot ℕ∞) :=
    topologicalKrullDimAt_eq_of_equidimensional_open
      (i ≫ (D.geometricFiber X₀).hom) ⊤ 1 hCtop x (by trivial)
  have hdim := (field_extension_component_local_dimension (L := D.k) Cₘ.hom).2.1
  have hlocal (y : Cₘ.left) : topologicalKrullDimAt y = (1 : WithBot ℕ∞) := by
    obtain ⟨w, rfl⟩ := (pullback.fst Cₘ.hom t).surjective y
    obtain ⟨x, rfl⟩ := e.hom.left.homeomorph.surjective w
    exact (hdim _).symm.trans
      ((local_dimension_homeomorph e.hom.left.homeomorph x).symm.trans (hlocalC x))
  have : IsLocallyNoetherian Cₘ.left := LocallyOfFiniteType.isLocallyNoetherian Cₘ.hom
  have hpure : Cₘ.left.IsPureDimension 1 :=
    component_dimensions_homeomorph (Homeomorph.Set.univ Cₘ.left) 1
      (topologicalKrullDim_component_eq_of_constant_local_dimension ⊤ 1
        (fun x _ ↦ hlocal x))
  refine ⟨m, hm, Cₘ, iₘ, inferInstance, hft, hqc, hiₘ, hs, hg, hpure, e, he, ?_⟩
  intro c z hz
  let q : Spec (CommRingCat.of D.k) ⟶ Cₘ.left :=
    c.left ≫ e.hom.left ≫ pullback.fst Cₘ.hom t
  have hq : q ≫ Cₘ.hom = t := by
    simp only [q, Category.assoc, pullback.condition]
    have hew : e.hom.left ≫ pullback.snd Cₘ.hom t =
        i ≫ (D.geometricFiber X₀).hom := Over.w e.hom
    have hcw : c.left ≫ (i ≫ (D.geometricFiber X₀).hom) = 𝟙 _ := Over.w c
    rw [← Category.assoc e.hom.left, hew, ← Category.assoc c.left, hcw,
      Category.id_comp]
  have hpoint : q (IsLocalRing.closedPoint D.k) = z := hz
  let : Algebra D.k₀ E := (D.extensionEmbedding m hm).toAlgebra
  have hEmb : E.subtype.comp (D.extensionEmbedding m hm) = algebraMap D.k₀ D.k :=
    (FiniteField.exists_unique_subfield_of_closure D.p D.a D.q D.prime D.exponent_pos
      D.cardinality_eq D.k₀ D.card_base D.k m hm).choose_spec.2.2.2.2.2.2.choose_spec
  have : IsScalarTower D.k₀ E D.k := IsScalarTower.of_algebraMap_eq' hEmb.symm
  have : Algebra.IsAlgebraic E D.k := Algebra.IsAlgebraic.tower_top (K := D.k₀) E
  let := (Cₘ.hom.residueFieldAlgebraMap z).toAlgebra
  obtain ⟨φ, hφ⟩ := (Cₘ.hom.exists_fieldPoints_base_eq_iff D.k z).mp
    ⟨⟨q, hq⟩, by
      change q (default : Spec (CommRingCat.of D.k)) = z
      exact (congrArg q (Subsingleton.elim _ _)).trans hpoint⟩
  let ψ : Cₘ.left.residueField z →ₐ[E] D.k :=
    { toRingHom := φ.hom
      commutes' := fun a ↦ RingHom.congr_fun hφ a }
  have : Algebra.IsAlgebraic E (Cₘ.left.residueField z) :=
    Algebra.IsAlgebraic.of_injective ψ ψ.injective
  have hc : z ∈ closedPoints Cₘ.left :=
    (closedPoint_iff_residueField_trdeg_zero_and_finite Cₘ.hom z).1.mpr
      (by rw [trdeg_eq_zero_iff]; infer_instance)
  have hf := (closedPoint_iff_residueField_trdeg_zero_and_finite Cₘ.hom z).2.1.mp hc
  exact ⟨hc, hf⟩

end WeilConjectures.FiniteFieldDatum
