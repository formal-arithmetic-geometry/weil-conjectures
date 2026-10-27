/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q62
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import Sheaf.AlgebraicGeometry.PureDimension
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Sheaf.AlgebraicGeometry.LocallyQuasiFiniteRelativeDimension
import Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension

/-! # Pure curve fibres and finiteness of a flat horizontal marking

Source: Stacks Project, More on Morphisms, Tags 0GSJ, 0GSK and 02LS;
Morphisms, Tags 02NK and 0397. Retained parent proof Steps 7--8.
(blueprint: lem-trf-flat-proper-curve-marking-fibres)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper flat finitely presented family with dense irreducible one-dimensional generic
fibre has nonempty pure one-dimensional geometric fibres. A flat finitely presented closed
marking with dense finite etale generic fibre is finite and has pure zero-dimensional
nonempty geometric fibres. An empty generic marking forces the marking to be empty.

Source: Stacks Project, More on Morphisms, Tags 0GSJ, 0GSK and 02LS;
Morphisms, Tags 02NK and 0397.

Proof:
1. Put `g = i ≫ f`. Closed immersions are proper and proper morphisms compose
   (lem-weil-pbc-proper-fp-permanence); both morphisms are locally of finite type.
2. Properness makes the image of `f` closed. It contains the generic point because the
   generic fibre is nonempty (def-pc-scheme-fibre), hence is the whole integral base
   (def-sc-generic-point). Surjectivity is preserved by base change
   (lem-weil-pbc-surjective-base-change), so each geometric fibre is nonempty.
3. The irreducible generic curve has one irreducible component, of dimension one
   (def-weil-irreducible-components). Apply
   lem-trf-flat-dense-generic-fibre-pure-dimension with `d = 1` to obtain purity.
4. The generic marking is discrete by lem-weil-pbc-etale-fibre-discrete-separable-points
   over the residue field (def-weil-residue-field and def-pc-scheme-fibre). Its irreducible
   components are singletons and have Krull dimension zero by the chain definition
   (def-weil-irreducible-components and def-kun-topological-krull-dimension).
   If it is empty the component assertion is vacuous.
5. Apply lem-trf-flat-dense-generic-fibre-pure-dimension to `g` with `d = 0` to obtain
   pure zero-dimensional nonempty ordinary and geometric fibres.
6. For any `z : Z`, its corresponding point in the fibre over `g z` exists by
   def-pc-scheme-fibre. That fibre is locally of finite type by
   lem-weil-pbc-lft-base-change. The lemma lem-sbc-equidimensional-open-local-dimension
   gives local dimension zero at this point. The reverse direction of
   lem-trf-locally-quasi-finite-relative-dimension-zero makes `g` locally quasi-finite.
   It is proper by Step 1, hence finite by pqf-lem-proper-lqf-finite (Tag 02LS).
   Flatness and finite presentation were hypotheses; Step 5 gives the geometric clause.
   When `Z` is empty the pointwise criterion is vacuous.
7. If the generic marking is empty, the closure of its image is empty. Its assumed
   density therefore forces `Z` to be empty.
(blueprint: lem-trf-flat-proper-curve-marking-fibres) -/
theorem flat_proper_curve_marking_fibres
    {T X Z : Scheme.{u}} [IsIntegral T]
    (η : T) (hη : IsGenericPoint η (Set.univ : Set T))
    (f : X ⟶ T) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (i : Z ⟶ X) [IsClosedImmersion i] [Flat (i ≫ f)]
    [LocallyOfFinitePresentation (i ≫ f)] [QuasiCompact (i ≫ f)] [QuasiSeparated (i ≫ f)]
    (hXdense : Dense (Set.range (f.fiberι η)))
    (hZdense : Dense (Set.range ((i ≫ f).fiberι η)))
    [IrreducibleSpace (f.fiber η)]
    (hXdim : topologicalKrullDim (f.fiber η) = (1 : WithBot ℕ∞))
    [IsFinite ((i ≫ f).fiberToSpecResidueField η)]
    [Etale ((i ≫ f).fiberToSpecResidueField η)] :
    Surjective f ∧
    (∀ t : T, ∀ (Ω : Type u) [Field Ω] [Algebra (T.residueField t) Ω] [IsAlgClosed Ω],
      Nonempty (pullback (C := Scheme.{u}) (f.fiberToSpecResidueField t)
        (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)))) ∧
      (pullback (C := Scheme.{u}) (f.fiberToSpecResidueField t)
        (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)))).IsPureDimension 1) ∧
    IsFinite (i ≫ f) ∧ Flat (i ≫ f) ∧
    LocallyOfFinitePresentation (i ≫ f) ∧ QuasiCompact (i ≫ f) ∧ QuasiSeparated (i ≫ f) ∧
    (∀ t : T, ∀ (Ω : Type u) [Field Ω] [Algebra (T.residueField t) Ω] [IsAlgClosed Ω],
      Nonempty (pullback (C := Scheme.{u}) ((i ≫ f).fiberToSpecResidueField t)
        (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)))) →
      (pullback (C := Scheme.{u}) ((i ≫ f).fiberToSpecResidueField t)
        (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) Ω)))).IsPureDimension 0) ∧
    (IsEmpty ((i ≫ f).fiber η) → IsEmpty Z) := by
  sorry

end AlgebraicGeometry
