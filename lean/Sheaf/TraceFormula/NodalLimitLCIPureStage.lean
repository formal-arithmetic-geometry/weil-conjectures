/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.FiniteStability
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import Sheaf.TraceFormula.CompleteIntersectionFibresLimitDescent
import Sheaf.AlgebraicGeometry.NodalCurveLCICriterion
import Sheaf.TraceFormula.PureRelativeDimensionFiniteStage
import Sheaf.TraceFormula.RelativeDimensionBaseChange

/-! # Local complete intersection and pure dimension at finite stages of a nodal limit

Source: Stacks Project, Curves, Tags 0C5F and 0C4E; Limits, Tags 0C3L and 0EY2;
Morphisms, Tag 02FY (blueprint: lem-trf-nodal-limit-lci-pure-stage).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A flat nodal limit of a finitely presented family has a common tail of flat,
locally finitely presented stages with pure-one-dimensional ordinary fibres and
pure-one-dimensional local-complete-intersection geometric fibres. Empty fibres are allowed.
The affine neighbourhood condition in the conclusion is precisely an affine open cover
by finite type algebras that are local complete intersections over the geometric field.
Geometric points use the scheme universe, as in the recorded geometric-point convention.

Source: Stacks Project, Curves, Tag 0C5F, first proof paragraph, and Tag 0C4E;
Limits, Tags 0C3L and 0EY2; Morphisms, Tags 02FY and 02NK.
(blueprint: lem-trf-nodal-limit-lci-pure-stage).

Proof:
1. Finite presentation survives base change, by
   `lem-weil-pbc-finite-presentation-base-change-composition`; all fibres are locally
   of finite type.
2. For a nonempty geometric fibre, use `lem-trf-nodal-curve-lci-criterion` over its
   already algebraically closed field, taking that field as its own algebraic closure.
   Smooth points and the specified nodal completions give an affine LCI cover.
   The empty geometric fibre has the empty cover.
3. Apply `lem-trf-complete-intersection-fibres-limit-descent` with initial target the
   base stage and its identity structure map. This gives flatness, local finite
   presentation and geometric LCI fibres on a common tail.
4. For an ordinary fibre at the limit, extend its residue field to an algebraic closure.
   `lem-pc-field-extension-surjective` and `lem-weil-pbc-surjective-base-change` give
   surjectivity onto that ordinary fibre. On the nonempty geometric fibre use
   `lem-sbc-equidimensional-open-local-dimension` to obtain local dimension one.
   `lem-trf-field-extension-component-local-dimension` descends local dimension and
   supplies local Noetherianness; `lem-sbc-constant-local-dimension-components` then
   gives pure dimension one for the ordinary fibre. Empty fibres impose no restriction.
5. Apply `lem-trf-pure-relative-dimension-finite-stage` with dimension one to obtain
   another tail on which all nonempty ordinary fibres are pure of dimension one.
6. Choose a common upper bound of the two indices and the initial stage. Flatness,
   local finite presentation and geometric LCI hold there by step 3. Ordinary purity
   holds by step 5. `lem-trf-relative-dimension-base-change` gives geometric purity
   after every geometric point, completing all clauses on the entire common tail.
-/
theorem nodal_limit_lci_pure_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (a : I)
    (Xₐ : Scheme.{u}) [CompactSpace Xₐ] [QuasiSeparatedSpace Xₐ]
    (gₐ : Xₐ ⟶ D.obj (op a))
    [LocallyOfFinitePresentation gₐ] [QuasiCompact gₐ] [QuasiSeparated gₐ]
    (hflat : Flat (pullback.snd gₐ (c.π.app (op a))))
    (hfib : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (y : Spec (.of Ω) ⟶ c.pt),
      IsEmpty (pullback (C := Scheme.{u}) (pullback.snd gₐ (c.π.app (op a))) y) ∨
        ((pullback (C := Scheme.{u}) (pullback.snd gₐ (c.π.app (op a))) y).IsPureDimension 1 ∧
          ∀ z : pullback (C := Scheme.{u}) (pullback.snd gₐ (c.π.app (op a))) y,
            z ∉ (pullback.snd (pullback.snd gₐ (c.π.app (op a))) y).smoothLocus →
            Nonempty
              (AdicCompletion
                (IsLocalRing.maximalIdeal
                  ((pullback (pullback.snd gₐ (c.π.app (op a))) y).presheaf.stalk z))
                ((pullback (pullback.snd gₐ (c.π.app (op a))) y).presheaf.stalk z) ≃+*
                (MvPowerSeries (Fin 2) Ω ⧸
                  Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) Ω) *
                    (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) Ω)})))) :
    ∃ b : I, ∃ hab : a ≤ b, ∀ (i : I) (hbi : b ≤ i),
      Flat (pullback.snd gₐ (D.map (homOfLE (hab.trans hbi)).op)) ∧
      LocallyOfFinitePresentation (pullback.snd gₐ (D.map (homOfLE (hab.trans hbi)).op)) ∧
      (∀ s : D.obj (op i),
        Nonempty ((pullback.snd gₐ (D.map (homOfLE (hab.trans hbi)).op)).fiber s) →
        ((pullback.snd gₐ (D.map (homOfLE (hab.trans hbi)).op)).fiber s).IsPureDimension 1) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ D.obj (op i)),
        IsEmpty (pullback (C := Scheme.{u})
          (pullback.snd gₐ (D.map (homOfLE (hab.trans hbi)).op)) y) ∨
        ((pullback (C := Scheme.{u})
            (pullback.snd gₐ (D.map (homOfLE (hab.trans hbi)).op)) y).IsPureDimension 1 ∧
          ∀ z : pullback (C := Scheme.{u})
              (pullback.snd gₐ (D.map (homOfLE (hab.trans hbi)).op)) y,
            ∃ U : (pullback (C := Scheme.{u})
                (pullback.snd gₐ (D.map (homOfLE (hab.trans hbi)).op)) y).affineOpens,
              z ∈ U.1 ∧
              ∃ ft : @Algebra.FiniteType Ω _ _ _
                  (((pullback.snd
                    (pullback.snd gₐ (D.map (homOfLE (hab.trans hbi)).op)) y).appLE
                      ⊤ U.1 (by simp)).hom.comp (Scheme.ΓSpecIso (.of Ω)).inv.hom).toAlgebra,
                @Algebra.IsLocalCompleteIntersection Ω _ _ _
                  (((pullback.snd
                    (pullback.snd gₐ (D.map (homOfLE (hab.trans hbi)).op)) y).appLE
                      ⊤ U.1 (by simp)).hom.comp (Scheme.ΓSpecIso (.of Ω)).inv.hom).toAlgebra
                  ft)) := by
  sorry

end AlgebraicGeometry
