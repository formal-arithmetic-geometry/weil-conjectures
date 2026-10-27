/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q03
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Sheaf.AlgebraicGeometry.FlatSmoothPointBaseChange
import Sheaf.TraceFormula.NodeAlgebraicallyClosedExtension
import Sheaf.TraceFormula.RelativeDimensionBaseChange

/-! # Chosen nodal fibres and arbitrary geometric points

Source: Stacks Project, curves.tex, Tags 0C56 and 0C59; morphisms.tex, Tags 02NK and 02V4.
(blueprint: lem-trf-chosen-nodal-fibres-universal)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Nodal fibres over chosen residue-field algebraic closures give nodal fibres at every
geometric point. Geometric points are parametrized by `s` and `φ` using
`Scheme.SpecToEquivOfField`. The fibre associativity isomorphism respects both projections.
The relative smooth locus is the Mathlib open `f.smoothLocus`; its neighbourhood
characterization and its equality with the inverse image after every base change are included.

Source: Stacks Project, curves.tex, Tags 0C56 (lemma-node-field-extension) and 0C59
(lemma-nodal-family); morphisms.tex, Tags 02NK and 02V4(1).
(blueprint: lem-trf-chosen-nodal-fibres-universal)

Proof:
1. For `s` and the residue-field embedding `φ`, apply
   lem-weil-pbc-algebraic-extension-embeds-algebraically-closed to the algebraic closure
   `k s` to obtain an embedding `ψ` extending `φ`. The fibre-product universal property
   (def-pc-fibre-product) identifies the iterated fibre product with the geometric fibre,
   compatibly with its maps to `Y` and `Spec Ω`.
2. Local finite presentation implies local finite type (retain the polynomial generators).
   By lem-weil-pbc-lft-base-change the chosen geometric fibre is locally of finite type.
   Apply lem-trf-relative-dimension-base-change with dimension one to see that each chosen
   or arbitrary geometric fibre is empty or pure of dimension one.
3. Apply lem-trf-node-algebraically-closed-extension to the chosen geometric fibre and
   `ψ`, using its assumed nodal completed local rings. Transport through the isomorphism
   from step 1 to obtain the asserted completed local rings over `Ω`.
4. The union of smooth open neighbourhoods is open and smooth by
   lem-weil-pbc-smooth-local-on-source, so it is precisely `f.smoothLocus`. For arbitrary
   base change, lem-sfb-scheme-flat-smooth-point-base-change identifies smoothness near
   each point with smoothness near its image. Hence the smooth open is the inverse image
   of `f.smoothLocus`, which is its fibre product by def-pc-fibre-product. Taking
   complements gives the nonsmooth-image assertion. No quasi-compactness or Noetherian
   hypothesis on the base is used; all assertions allow empty fibres.
-/
theorem chosen_nodal_fibres_universal
    {Y S : Scheme.{u}} (f : Y ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hpure : ∀ s : S, Nonempty (f.fiber s) → (f.fiber s).IsPureDimension 1)
    (k : S → Type u) [∀ s : S, Field (k s)]
    [∀ s : S, Algebra (S.residueField s) (k s)]
    [∀ s : S, IsAlgClosure (S.residueField s) (k s)]
    (hnodal : ∀ (s : S)
        (x : pullback (C := Scheme.{u}) f
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) (k s))) ≫
            S.fromSpecResidueField s)),
      (¬ ∃ V : (pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) (k s))) ≫
            S.fromSpecResidueField s)).Opens,
        x ∈ V ∧ Smooth (V.ι ≫ pullback.snd f
          (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) (k s))) ≫
            S.fromSpecResidueField s))) →
      Nonempty
        (AdicCompletion
          (IsLocalRing.maximalIdeal ((pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) (k s))) ≫
              S.fromSpecResidueField s)).presheaf.stalk x))
          ((pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) (k s))) ≫
              S.fromSpecResidueField s)).presheaf.stalk x) ≃+*
          (MvPowerSeries (Fin 2) (k s) ⧸
            Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) (k s)) *
              MvPowerSeries.X 1}))) :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : S) (φ : S.residueField s →+* Ω),
      (∃ ψ : k s →+* Ω, Function.Injective ψ ∧
        ψ.comp (algebraMap (S.residueField s) (k s)) = φ ∧
        ∃ e : pullback (C := Scheme.{u}) f
            (Spec.map (CommRingCat.ofHom φ) ≫ S.fromSpecResidueField s) ≅
          pullback
            (pullback.snd f
              (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) (k s))) ≫
                S.fromSpecResidueField s))
            (Spec.map (CommRingCat.ofHom ψ)),
          e.hom ≫ pullback.snd _ (Spec.map (CommRingCat.ofHom ψ)) =
            pullback.snd f (Spec.map (CommRingCat.ofHom φ) ≫ S.fromSpecResidueField s) ∧
          e.hom ≫ pullback.fst _ (Spec.map (CommRingCat.ofHom ψ)) ≫
              pullback.fst f
                (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) (k s))) ≫
                  S.fromSpecResidueField s) =
            pullback.fst f (Spec.map (CommRingCat.ofHom φ) ≫ S.fromSpecResidueField s)) ∧
      (Nonempty (pullback (C := Scheme.{u}) f
          (Spec.map (CommRingCat.ofHom φ) ≫ S.fromSpecResidueField s)) →
        (pullback f (Spec.map (CommRingCat.ofHom φ) ≫ S.fromSpecResidueField s)).IsPureDimension
          1) ∧
      ∀ x : pullback (C := Scheme.{u}) f
          (Spec.map (CommRingCat.ofHom φ) ≫ S.fromSpecResidueField s),
        (¬ ∃ V : (pullback f
            (Spec.map (CommRingCat.ofHom φ) ≫ S.fromSpecResidueField s)).Opens,
          x ∈ V ∧ Smooth (V.ι ≫ pullback.snd f
            (Spec.map (CommRingCat.ofHom φ) ≫ S.fromSpecResidueField s))) →
        Nonempty
          (AdicCompletion
            (IsLocalRing.maximalIdeal ((pullback f
              (Spec.map (CommRingCat.ofHom φ) ≫ S.fromSpecResidueField s)).presheaf.stalk x))
            ((pullback f
              (Spec.map (CommRingCat.ofHom φ) ≫ S.fromSpecResidueField s)).presheaf.stalk x) ≃+*
            (MvPowerSeries (Fin 2) Ω ⧸
              Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
                MvPowerSeries.X 1}))) ∧
    (∀ y : Y, y ∈ f.smoothLocus ↔
      ∃ V : Y.Opens, y ∈ V ∧ Smooth (V.ι ≫ f)) ∧
    (∀ (S' : Scheme.{u}) (g : S' ⟶ S),
      (pullback.snd f g).smoothLocus = pullback.fst f g ⁻¹ᵁ f.smoothLocus ∧
      ∀ x : pullback (C := Scheme.{u}) f g,
        x ∉ (pullback.snd f g).smoothLocus → pullback.fst f g x ∉ f.smoothLocus) := by
  sorry

end AlgebraicGeometry
