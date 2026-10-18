/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.FiniteTypeExceptionalInverseImage
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.Topology.KrullDimension
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.EquivFin
public import Sheaf.Paper.FiniteFieldFiber
import Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals
import Sheaf.AlgebraicGeometry.OpenComplementCondition
import Sheaf.Paper.FiniteTorAmplitudeSites
import Sheaf.Paper.OpenComplementUnconditional
import Sheaf.Paper.PurityGeneralAdmissibility

/-!
# Affine-chart assembly for constructible exceptional inverse image

Source: Weil blueprint, `sec-six-functors/sk-prop-sf-rf-shriek-preservation`,
`cor-pur-general-admissibility-datum` (blueprint: cor-pur-general-admissibility-datum).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Specialize the published functor `finiteTypeExceptionalInverseImage` to the actual
positive-level quotient and the supplied compactification. Its defining composite is
`ν_X^* f^× Rν_{Y,*}`; the right adjoint and compactification choices are determined up
to their canonical isomorphisms. The `ULift` changes only the coefficient universe.
Source: blueprint cor-pur-general-admissibility-datum, applying the finite-level
defining formula of def-weil-exceptional-inverse-image (order 1489)
(blueprint: cor-pur-general-admissibility-datum). -/
noncomputable def sfFiniteExceptionalInverseImage
    (k : Type u) [Field k]
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    {f : X ⟶ Y} [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (c : Compactification f) :
    _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))) ⥤
      _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))) :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  letI : HasCompactification f := ⟨⟨c⟩⟩
  finiteTypeExceptionalInverseImage
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)) k f

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme

/-- The chosen finite affine target cover, finite affine source covers over its members,
and closed affine-space presentations. The equations specify that each presentation is
over its target open. Empty opens and empty index sets are permitted.
Source: blueprint, affine charts in cor-pur-general-admissibility-datum
(blueprint: cor-pur-general-admissibility-datum). -/
structure SfAffineChartPresentation {X Y : Scheme.{u}} (f : X ⟶ Y) where
  count : ℕ
  target : Fin count → Y.Opens
  target_affine : ∀ i, IsAffineOpen (target i)
  target_cover : ∀ y : Y, ∃ i, y ∈ target i
  size : Fin count → ℕ
  source : (i : Fin count) → Fin (size i) → X.Opens
  source_affine : ∀ i j, IsAffineOpen (source i j)
  source_le : ∀ i j, source i j ≤ f ⁻¹ᵁ target i
  source_cover : ∀ (i : Fin count) (x : X), x ∈ f ⁻¹ᵁ target i →
    ∃ j : Fin (size i), x ∈ source i j
  dimension : (i : Fin count) → Fin (size i) → ℕ
  presentation : (i : Fin count) → (j : Fin (size i)) →
    (source i j).toScheme ⟶ AffineSpace (ULift.{u} (Fin (dimension i j))) (target i).toScheme
  presentation_closed : ∀ i j, IsClosedImmersion (presentation i j)
  presentation_over : ∀ i j,
    presentation i j ≫
        (AffineSpace (ULift.{u} (Fin (dimension i j))) (target i).toScheme ↘
          (target i).toScheme) ≫ (target i).ι = (source i j).ι ≫ f

open Classical in
/-- Omit precisely the empty source charts, retaining the target cover and every
surviving chart's affine-space presentation. The subtype of surviving indices is
reindexed by `Fintype.equivFin`. A point in an original chart witnesses its
nonemptiness, so these charts still cover every inverse image of a target open.
Source: blueprint cor-pur-general-admissibility-datum, omission of empty charts
(blueprint: cor-pur-general-admissibility-datum). -/
noncomputable def SfAffineChartPresentation.nonemptyCharts
    {X Y : Scheme.{u}} {f : X ⟶ Y} (C : SfAffineChartPresentation f) :
    SfAffineChartPresentation f :=
  let e (i : Fin C.count) :=
    (Fintype.equivFin {j : Fin (C.size i) // Nonempty (C.source i j)}).symm
  { count := C.count
    target := C.target
    target_affine := C.target_affine
    target_cover := C.target_cover
    size := fun i ↦ Fintype.card {j : Fin (C.size i) // Nonempty (C.source i j)}
    source := fun i j ↦ C.source i (e i j).val
    source_affine := fun i j ↦ C.source_affine i (e i j).val
    source_le := fun i j ↦ C.source_le i (e i j).val
    source_cover := by
      intro i x hx
      obtain ⟨j, hj⟩ := C.source_cover i x hx
      refine ⟨(e i).symm ⟨j, ⟨⟨x, hj⟩⟩⟩, ?_⟩
      simpa only [Equiv.apply_symm_apply] using hj
    dimension := fun i j ↦ C.dimension i (e i j).val
    presentation := fun i j ↦ C.presentation i (e i j).val
    presentation_closed := fun i j ↦ C.presentation_closed i (e i j).val
    presentation_over := fun i j ↦ C.presentation_over i (e i j).val }

/-- Maximum chart embedding dimension, with `sup ∅ = 0` in `ℕ`.
Source: blueprint affine-chart maximum
(blueprint: cor-pur-general-admissibility-datum). -/
def SfAffineChartPresentation.maxDimension {X Y : Scheme.{u}} {f : X ⟶ Y}
    (C : SfAffineChartPresentation f) : ℕ :=
  Finset.univ.sup (fun ij : (i : Fin C.count) × Fin (C.size i) ↦ C.dimension ij.1 ij.2)

/-- Finite-type schemes over a field have finite Krull dimension. This integer-valued
reading takes the nonnegative dimension for a nonempty such scheme and zero for the
empty scheme, whose topological dimension is bottom.
Source: blueprint dimension convention in the affine-chart assembly
(blueprint: cor-pur-general-admissibility-datum). -/
noncomputable def sfDimension (Y : Scheme.{u}) : ℕ :=
  ((topologicalKrullDim Y).unbotD 0).toNat

open Classical in
/-- The maximum over the nonempty source charts in affine-chart assembly;
the empty source has shift zero.
Source: blueprint cor-pur-general-admissibility-datum, definition of `D`
(blueprint: cor-pur-general-admissibility-datum). -/
noncomputable def SfAffineChartPresentation.assemblyDimension
    {X Y : Scheme.{u}} {f : X ⟶ Y} (C : SfAffineChartPresentation f) : ℕ :=
  if Nonempty X then C.nonemptyCharts.maxDimension else 0

open Classical in
/-- The corollary's integer `c = max_U (c_U + 1 + 2(D-d_U))`, with
`c_U = 2(d_U + dim Y)`. Every summand equals the displayed expression when `X`
is nonempty, after applying `nonemptyCharts`. For the empty source `c = 0`.
Source: blueprint cor-pur-general-admissibility-datum, formula for `c`
(blueprint: cor-pur-general-admissibility-datum). -/
noncomputable def SfAffineChartPresentation.assemblyConstant
    {X Y : Scheme.{u}} {f : X ⟶ Y} (C : SfAffineChartPresentation f) : ℤ :=
  if Nonempty X then
    2 * (C.nonemptyCharts.maxDimension : ℤ) + 2 * (sfDimension Y : ℤ) + 1 else 0

/-- The purity assembly gives constructibility, cohomological bounds, and the same
Tor bounds together with finite-Tor constructible membership. The supplied chart
family is arbitrary: `C.nonemptyCharts` omits empty source charts internally, exactly
as in the corollary. The numerical constants use this restricted family.
Source: blueprint cor-pur-general-admissibility-datum
(blueprint: cor-pur-general-admissibility-datum).

Proof:
1. Use the constructible comparison-transported exceptional functor. Its adjunction
   relative to bounded constructible inputs is cor-sf-ambient-adjoint-discharge;
   no unrestricted ambient pro-etale right adjoint is used.
2. If X is empty, every object of its small pro-etale site is empty and has the empty
   covering family. The sheaf condition forces every module of sections to be zero.
   All output cohomology and every degree-zero module-sheaf tensor test are therefore
   zero, giving both conclusions with D=c=0.
3. For nonempty X, apply `C.nonemptyCharts`: its source indices are exactly the
   subtypes of original indices with nonempty source, reindexed by `Fintype.equivFin`.
   Every original covering chart containing a point survives, so source_cover is
   retained. Every surviving source is nonempty by its subtype property; the target
   cover, embedding dimensions and closed presentations are inherited unchanged.
   The chart clause of
   thm-pur-open-complement-unconditional gives the open-complement condition on
   the complement of U in affine d_U-space over V, with bound 2(d_U+dim V).
   Since dim V is at most dim Y, this bound is at most c_U=2(d_U+dim Y).
4. The condition of def-exc-open-complement-bound is monotone in its bound:
   q>c_U implies q>2(d_U+dim V), so its vanishing clause still holds, while its
   constructibility clause is independent of the bound. Thus each chart satisfies
   the condition with precisely the chosen c_U.
5. Apply thm-pur-general-admissibility to f and `C.nonemptyCharts`, whose
   nonemptiness condition is supplied by the index subtype, without a premise on C.
   Its lower shift is -2D with D=`C.nonemptyCharts.maxDimension`, and its upper
   shift is -2D+c, where
   c=max(c_U+1+2(D-d_U)). Every summand equals 2D+2 dim Y+1, exactly the
   assemblyConstant above. The theorem supplies both the cohomological interval
   and finite-Tor constructible membership with the displayed Tor interval. -/
theorem sf_purity_affine_chart_bounds
    (F : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X Y : Scheme.{u})
    [X.Over (Spec (.of F.k))] [Y.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of F.k))] [QuasiCompact (X ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of F.k))] [QuasiCompact (Y ↘ Spec (.of F.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of F.k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification f) (C : SfAffineChartPresentation f) :
    ∀ (a b : ℤ) (_hab : a ≤ b),
      (∀ L : _root_.DerivedCategory (Sheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))),
        ProEtale.DerivedCategory.constructibleIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
          Y a b L →
        ProEtale.DerivedCategory.constructibleIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
          X (a - 2 * (C.assemblyDimension : ℤ))
          (b - 2 * (C.assemblyDimension : ℤ) + C.assemblyConstant)
          ((ProEtale.sfFiniteExceptionalInverseImage F.k l E n hn c).obj L)) ∧
      (∀ K : _root_.DerivedCategory (Sheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))),
        ProEtale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) Y K →
        ProEtale.DerivedCategory.torAmplitudeIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) Y a b K →
        ProEtale.DerivedCategory.constructibleFiniteTor
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))) X
          ((ProEtale.sfFiniteExceptionalInverseImage F.k l E n hn c).obj K) ∧
        ProEtale.DerivedCategory.torAmplitudeIn
          (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)))
          X (a - 2 * (C.assemblyDimension : ℤ))
          (b - 2 * (C.assemblyDimension : ℤ) + C.assemblyConstant)
          ((ProEtale.sfFiniteExceptionalInverseImage F.k l E n hn c).obj K)) := by
  sorry

end AlgebraicGeometry.Scheme
