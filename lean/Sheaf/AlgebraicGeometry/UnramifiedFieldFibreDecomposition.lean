/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Finiteness.Defs

import Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct
import Sheaf.AlgebraicGeometry.SpecFiniteProductFields
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Unramified schemes over a field as disjoint unions of finite separable spectra

Source: Stacks Project, Morphisms, Lemma 02G7 (lemma-unramified-over-field), part (1).
(blueprint: lem-trf-unramified-field-fibre-decomposition)
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A scheme over a field is unramified exactly when it is a disjoint union, over that field,
of spectra of finite separable field extensions. The index set may be empty or infinite.
Source: Stacks Project, Morphisms, Lemma 02G7 (lemma-unramified-over-field), part (1).
(blueprint: lem-trf-unramified-field-fibre-decomposition)

Proof:
1. Suppose the structure morphism is unramified. Choose an affine open cover of `X`.
   By `lem-weil-pbc-unramified-base-change-open`, restriction to each chart is unramified.
   By `lem-weil-pbc-unramified-algebra-over-field-product`, its algebra is a finite product
   of finite separable extensions of `k`, with the empty product allowed.
2. By `lem-weil-pbc-spec-finite-product-fields`, each factor spectrum is the singleton
   open subscheme belonging to its projection kernel. These singletons exhaust the chart.
   The identification is over `k`, since projection of the chart's algebra structure is
   precisely the factor's algebra structure, and `Spec.map` reverses composition.
3. Index the singleton open subschemes by the points of `X`. They are pairwise disjoint
   and cover `X`. For every open `V`, the sheaf axiom identifies its sections with the
   product of the sections on these singletons in `V`, compatibly with restrictions.
   Thus their coproduct is isomorphic to `X` as a scheme over `k`. For empty `X`, use
   the empty index set; no finiteness condition on the whole index set is needed.
4. Conversely, each finite separable extension has etale spectrum by
   `lem-weil-pbc-finite-separable-extension-etale`. By `def-weil-etale-morphism` this is
   unramified. The criterion `lem-weil-pbc-unramified-ring-map-iff-unramified-affine`
   gives finite type and vanishing relative differentials on every summand.
5. The summands form an affine open cover. The affine-cover formulation in
   `def-weil-unramified-morphism` now gives unramifiedness of the structure morphism.
   For the empty union the condition is vacuous. -/
theorem unramified_iff_exists_iso_coproduct_spec_finite_separable
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    (LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)) ↔
      ∃ (I : Type u) (L : I → Type u) (_ : ∀ i, Field (L i))
        (_ : ∀ i, Algebra k (L i)),
        (∀ i, Module.Finite k (L i) ∧ Algebra.IsSeparable k (L i)) ∧
          ∃ e : (∐ fun i : I ↦ Spec (.of (L i))) ≅ X,
            ∀ i : I, Sigma.ι (fun j : I ↦ Spec (.of (L j))) i ≫ e.hom ≫ f =
              Spec.map (CommRingCat.ofHom (algebraMap k (L i))) := by
  classical
  constructor
  · rintro ⟨hft, hdiag⟩
    let := hft
    let := hdiag
    have hlocal (x : X) :
        ∃ (L : Type u) (_ : Field L) (_ : Algebra k L),
          Module.Finite k L ∧ Algebra.IsSeparable k L ∧
          ∃ a : Spec (.of L) ⟶ X, IsOpenImmersion a ∧
            Set.range a = {x} ∧
            a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
      obtain ⟨C, a, ha, z, hz⟩ := X.exists_Spec_apply_eq x
      let := ha
      let g := a ≫ f
      let φ := Spec.preimage g
      let : Algebra k C := φ.hom.toAlgebra
      have hg : Spec.map (CommRingCat.ofHom (algebraMap k C)) = g :=
        Spec.map_preimage g
      have hgt : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k C))) := by
        rw [hg]
        infer_instance
      have hgd : IsOpenImmersion
          (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap k C)))) := by
        rw [hg]
        have : FormallyUnramified f := inferInstance
        have : FormallyUnramified g :=
          IsZariskiLocalAtSource.comp (inferInstanceAs (FormallyUnramified f)) a
        infer_instance
      obtain ⟨n, L, hL, hA, hfin, ⟨e⟩⟩ :=
        exists_algEquiv_pi_finite_separable_of_unramified_spec k C hgt hgd
      let := hL
      let := hA
      let b : Spec (.of (∀ j, L j)) ⟶ Spec C :=
        Spec.map (CommRingCat.ofHom e.toRingHom)
      have hb : IsIso b := by
        change IsIso (Scheme.Spec.map e.toRingEquiv.toCommRingCatIso.hom.op)
        infer_instance
      let p : Spec (.of (∀ j, L j)) := inv b z
      have hparts := spec_finite_product_fields n L
      obtain ⟨j, hj⟩ := (hparts.1 p.asIdeal).mp p.isPrime
      let q : Spec (.of (L j)) ⟶ Spec (.of (∀ j, L j)) :=
        Spec.map (CommRingCat.ofHom (Pi.evalRingHom L j))
      have hq : IsOpenImmersion q := (hparts.2.2.2.2 j).1
      have hp : p ∈ Set.range q := by
        change p ∈ Set.range (fun t : PrimeSpectrum (L j) ↦
          (Spec.map (CommRingCat.ofHom (Pi.evalRingHom L j))).base t)
        rw [(hparts.2.2.2.2 j).2.1]
        exact hj
      obtain ⟨t, ht⟩ := hp
      let c : Spec (.of (L j)) ⟶ X := q ≫ b ≫ a
      have hct : c t = x := by
        change a (b (q t)) = x
        rw [ht]
        simpa only [p, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id,
          Category.id_comp] using hz
      refine ⟨L j, hL j, hA j, (hfin j).1, (hfin j).2, c, inferInstance, ?_, ?_⟩
      · ext w
        constructor
        · rintro ⟨v, rfl⟩
          simpa only [Set.mem_singleton_iff, Subsingleton.elim v t] using hct
        · rintro rfl
          exact ⟨t, hct⟩
      · change q ≫ b ≫ g = _
        rw [← hg]
        change Spec.map (CommRingCat.ofHom (Pi.evalRingHom L j)) ≫
          Spec.map (CommRingCat.ofHom e.toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k C)) = _
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
        ext r
        exact congrFun (e.commutes r) j
    choose L hL hA hfin hsep a hopen hrange hcomp using hlocal
    let := hL
    let := hA
    let := hopen
    have hdesc : IsOpenImmersion (Sigma.desc a) := by
      apply isOpenImmersion_sigmaDesc
      intro x y hxy
      change Disjoint (Set.range (a x)) (Set.range (a y))
      rw [hrange x, hrange y]
      exact Set.disjoint_singleton.mpr hxy
    let := hdesc
    have hiso : IsIso (Sigma.desc a) := by
      apply isIso_of_isOpenImmersion_of_opensRange_eq_top
      ext x
      change (∃ t, (Sigma.desc a) t = x) ↔ True
      rw [iff_true]
      obtain ⟨t, ht⟩ := (hrange x).symm ▸ Set.mem_singleton x
      exact ⟨Sigma.ι (fun x ↦ Spec (.of (L x))) x t, by
        simpa [← Scheme.Hom.comp_apply] using ht⟩
    refine ⟨X, L, hL, hA, fun x ↦ ⟨hfin x, hsep x⟩, asIso (Sigma.desc a), ?_⟩
    intro x
    simpa using hcomp x
  · rintro ⟨I, L, hL, hA, hfin, e, he⟩
    let := hL
    let := hA
    have hs (i : I) : Etale (Sigma.ι (fun j ↦ Spec (.of (L j))) i ≫ e.hom ≫ f) := by
      rw [he i]
      let := (hfin i).1
      let := (hfin i).2
      have : Algebra.Etale k (L i) := Algebra.Etale.of_finite_of_isSeparable
      exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
        (RingHom.etale_algebraMap.mpr inferInstance)
    have hf : Etale (e.hom ≫ f) :=
      IsZariskiLocalAtSource.of_openCover (P := @Etale)
        (sigmaOpenCover (fun i ↦ Spec (.of (L i)))) hs
    have : Etale f := by
      have : f = e.inv ≫ (e.hom ≫ f) := by simp
      rw [this]
      infer_instance
    exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry
