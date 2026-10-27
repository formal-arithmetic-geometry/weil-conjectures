/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.PureDimension
public import Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension
import Sheaf.AlgebraicGeometry.DthFittingSmoothLocus
import Mathlib.RingTheory.Smooth.Basic
import WeilConjectures.RingTheory.SmoothLocalCompleteIntersection

/-! # First-Fitting preparation on a pure curve over a field

Source: Stacks Project, Curves, Tag 0C4E (lemma-nodal-lci), smooth-complement argument;
Divisors, Tag 0C3K (lemma-d-fitting-ideal-omega-smooth).
(blueprint: lem-trf-field-curve-fitting-smooth-preparation)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The smooth open-neighbourhood locus of a pure curve locally of finite type over a field
is the complement of the first-Fitting singular subscheme. Every point of that locus has
an affine open neighbourhood whose coordinate algebra, with the structure induced by `f`,
is finitely generated and a local complete intersection over the field. No hypothesis on
nodality, or on unramifiedness of the singular subscheme, is needed.

Source: Stacks Project, Curves, Tag 0C4E, smooth-complement argument; Divisors, Tag 0C3K.
(blueprint: lem-trf-field-curve-fitting-smooth-preparation)

Proof:
1. Every ideal in the field is zero or the unit ideal, so the field is Noetherian
   (`def-weil-pbc-noetherian-ring`) and its spectrum is locally Noetherian
   (`pqf-def-locnoeth`).
2. The structure map is flat by `Flat.of_field` (`lem-pc-flat-field`). Local finite type
   over the locally Noetherian base gives local finite presentation by
   `LocallyOfFinitePresentation.iff_locallyOfFiniteType` (`pqf-lem-lft-fp-locnoeth`).
3. The generic fibre over the unique point of the field spectrum is canonically the
   curve itself. Its image is dense and its components have dimension one. Apply
   `flat_dense_generic_fibre_pure_dimension`
   (`lem-trf-flat-dense-generic-fibre-pure-dimension`) to get pure geometric fibres.
   The empty curve causes no exception.
4. Apply `dthFitting_smoothLocus` (`lem-trf-dth-fitting-smooth-locus`) with index one.
   Its first Fitting ideal is `Scheme.firstFittingIdealSheaf f`, and the support is the
   image of `Scheme.firstFittingSingularSubscheme f`. This proves the complement equality.
5. At a point of `V`, take a smooth open neighbourhood and then an affine open
   neighbourhood inside it. Smoothness is affine-local (`def-sbc-smooth-morphisms`),
   so its coordinate algebra is smooth over the field. Smooth algebras are finitely
   presented (`def-weil-pbc-smooth-ring-map`), hence finitely generated. Apply
   `Algebra.isLocalCompleteIntersection_of_smooth`
   (`lem-weil-pbc-smooth-over-field-local-complete-intersection`). The affine open lies
   in `V` since every point of the smooth neighbourhood has that neighbourhood as witness.
-/
theorem field_curve_fitting_smooth_preparation
    (k : Type u) [Field k] (C : Scheme.{u}) (f : C ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (hpure : C.IsPureDimension 1)
    (V : Set C)
    (hV : ∀ x : C, x ∈ V ↔ ∃ W : C.Opens, x ∈ W ∧ Smooth (W.ι ≫ f)) :
    V = (Set.range (Scheme.firstFittingSingularSubscheme f))ᶜ ∧
      ∀ (x : C), x ∈ V → ∃ U : C.Opens, x ∈ U ∧ (U : Set C) ⊆ V ∧ IsAffineOpen U ∧
        ∃ ft : @Algebra.FiniteType k (Γ(C, U)) _ _
          (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra),
          @Algebra.IsLocalCompleteIntersection k (Γ(C, U)) _ _
            (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra) ft := by
  sorry

end AlgebraicGeometry
