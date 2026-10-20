/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.LimitAffineTransition
public import Sheaf.TraceFormula.LocalCompleteIntersectionScheme
import WeilConjectures.AlgebraicGeometry.AffineChartTensorComparison
import Sheaf.RingTheory.SyntomicRingFilteredColimitDescent
import Sheaf.RingTheory.LocalCompleteIntersectionFieldChange
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Sheaf.TraceFormula.SyntomicGeometricFibresAffineCriterion

/-!
# Descent of complete-intersection fibres along affine inverse limits

Source: Stacks Project, Limits, Tag 0C3L (lemma-descend-syntomic),
together with
Algebra, Tags 00S9 and 00SJ (blueprint: lem-trf-complete-intersection-fibres-limit-descent).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Canonical base-change morphism of a morphism over a base change.
Source: Stacks Project, Limits, Tag 0C3L
(blueprint: lem-trf-complete-intersection-fibres-limit-descent). -/
def canonicalBaseChangeMap
    {X Y S T : Scheme.{u}} (f : X ⟶ Y) (a : X ⟶ S) (b : Y ⟶ S)
    (p : T ⟶ S) (h : f ≫ b = a) : pullback a p ⟶ pullback b p :=
  pullback.map a p b p f (𝟙 _) (𝟙 _) (by simpa using h.symm) (by simp)

/-- Flat morphisms with local complete-intersection geometric fibres descend to a common
stage of an inverse system with affine transitions. All stages and both initial schemes
are quasi-compact and quasi-separated. A geometric point with arbitrarily large field is
represented by a point `y` and a residue-field embedding `φ`; its geometric fibre is
specified on affine charts of the ordinary fibre, tensored with that field.
Empty source covers and empty fibres are allowed.
Source: Stacks Project, Limits, Tag 0C3L, with Algebra, Tags 00S9 and 00SJ
(blueprint: lem-trf-complete-intersection-fibres-limit-descent).

Proof (the six steps of the DAG node):
1. By `lem-weil-pbc-qcqs-morphism-permanence` (1), `g₀` is quasi-compact. Choose finitely
   many affine target opens mapping into affine base opens, and finitely many affine source
   opens covering each inverse image, using `def-weil-finite-type-morphism`. Their inverse
   images continue to cover at every stage and at the limit.
2. For each affine triple, `lem-weil-pbc-affine-morphism-permanence` and
   `lem-weil-pbc-limit-affine-transition` identify the base charts with spectra of rings
   `Rᵢ` and the limit chart with `Spec R`, where `R` is their filtered colimit.
   `lem-weil-pbc-affine-chart-tensor-comparison` gives fixed algebras `B₀`, `C₀` and a
   finitely presented map between them, identifying the chart arrows with
   `Rᵢ ⊗[R₀] B₀ → Rᵢ ⊗[R₀] C₀`, and likewise at the limit. No finite presentation of
   `B₀` over `R₀` is asserted.
3. Local finite presentation survives base change by
   `lem-weil-pbc-qcqs-morphism-permanence` (3). Combine it with flatness and the geometric
   fibre hypothesis. Apply (1) to (2) of
   `lem-trf-syntomic-geometric-fibres-affine-criterion`: each limit chart ring map is flat
   and finitely presented, with local-complete-intersection ordinary residue-field fibres.
4. Apply `lem-trf-syntomic-ring-filtered-colimit-descent` to each of the finitely many
   triples. Choose a common upper bound for the resulting indices and `i₀`; when there
   are no source charts choose `i₀` itself.
5. For every subsequent `j` and each chosen stage `k`, the canonical identity
   `Cⱼ ≅ Bⱼ ⊗[Bₖ] Cₖ` sends `(r ⊗ b) ⊗ (s ⊗ c)` to
   `r αⱼₖ(s) ⊗ φ₀(b)c`; its inverse sends `r ⊗ c` to `(r ⊗ 1) ⊗ (1 ⊗ c)`.
   The balanced tensor relations make these maps well-defined and mutually inverse. Hence
   `lem-weil-pbc-flat-module-base-change` and
   `lem-weil-pbc-finite-presentation-base-change-composition` (1) preserve flatness and
   finite presentation. If a prime `q` of `Bⱼ` lies over `p` of `Bₖ`, its residue-field
   fibre is the extension of the fibre over `p` along `κ(p) → κ(q)` (with residue fields
   from `def-weil-pbc-localization-at-prime`). The latter fibre is finite type and a local
   complete intersection, so `lem-weil-pbc-lci-field-change` preserves the property.
6. The target and source chart covers persist. Their ring maps now satisfy condition (3)
   of `lem-trf-syntomic-geometric-fibres-affine-criterion`; its implication (3) to (1)
   gives all three asserted properties at every `j` on the common tail, including empty
   fibres. The affine tensor-product description covers every algebraically closed field.
-/
theorem completeIntersectionFibres_limit_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c)
    (i₀ : I)
    (U₀ V₀ : Scheme.{u})
    [CompactSpace U₀] [QuasiSeparatedSpace U₀]
    [CompactSpace V₀] [QuasiSeparatedSpace V₀]
    (u₀ : U₀ ⟶ D.obj (op i₀)) (v₀ : V₀ ⟶ D.obj (op i₀))
    (g₀ : U₀ ⟶ V₀) (h₀ : g₀ ≫ v₀ = u₀)
    [LocallyOfFinitePresentation g₀]
    (hflat : Flat (canonicalBaseChangeMap g₀ u₀ v₀ (c.π.app (op i₀)) h₀))
    (hfib : ∀ (Ω : Type (max u v)) [Field Ω] [IsAlgClosed Ω]
      (y : pullback (C := Scheme.{u}) v₀ (c.π.app (op i₀)))
      (φ : (pullback (C := Scheme.{u}) v₀ (c.π.app (op i₀))).residueField y →+* Ω),
      IsLocalCompleteIntersectionOverExtension _
        ((canonicalBaseChangeMap g₀ u₀ v₀ (c.π.app (op i₀)) h₀).fiber y)
        ((canonicalBaseChangeMap g₀ u₀ v₀ (c.π.app (op i₀)) h₀).fiberToSpecResidueField y)
        Ω φ) :
    ∃ i : I, ∃ hi : i₀ ≤ i,
      ∀ j : I, ∀ hj : i ≤ j,
        Flat (canonicalBaseChangeMap g₀ u₀ v₀ (D.map (homOfLE (hi.trans hj)).op) h₀) ∧
        LocallyOfFinitePresentation
          (canonicalBaseChangeMap g₀ u₀ v₀ (D.map (homOfLE (hi.trans hj)).op) h₀) ∧
        (∀ (Ω : Type (max u v)) [Field Ω] [IsAlgClosed Ω]
          (y : pullback (C := Scheme.{u}) v₀ (D.map (homOfLE (hi.trans hj)).op))
          (φ : (pullback (C := Scheme.{u}) v₀
            (D.map (homOfLE (hi.trans hj)).op)).residueField y →+* Ω),
          IsLocalCompleteIntersectionOverExtension _
            ((canonicalBaseChangeMap g₀ u₀ v₀ (D.map (homOfLE (hi.trans hj)).op) h₀).fiber y)
            (Scheme.Hom.fiberToSpecResidueField
              (canonicalBaseChangeMap g₀ u₀ v₀ (D.map (homOfLE (hi.trans hj)).op) h₀) y) Ω φ) := by
  sorry

end AlgebraicGeometry
