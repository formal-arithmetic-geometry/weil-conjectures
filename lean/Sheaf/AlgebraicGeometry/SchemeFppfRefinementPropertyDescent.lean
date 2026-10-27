/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Sheaf.RingTheory.FiniteTypeFppfSourceDescent
import WeilConjectures.Mathlib.RingTheory.Finiteness.Descent

/-!
# Scheme morphism properties descend through an fppf refinement

Source: Stacks Project, Descent, Tag 06NB, lemma-curiosity
(blueprint: lem-sfb-scheme-fppf-refinement-property-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Flatness, local finite type, and local finite presentation descend from a composite
along a morphism through which an fppf covering of its target factors.

Source: Stacks Project, Descent, Tag 06NB, lemma-curiosity, statement and three-case proof
(blueprint: lem-sfb-scheme-fppf-refinement-property-descent).

Proof plan (the three implications are proved separately):
1. Fix affine opens V = Spec B in Y and W = Spec C in Z with b(V) contained in W.
   By lem-sfb-fppf-lifts-finite-affine-charts obtain finitely many towers
   C → B → A_j → D_j, with U_j = Spec A_j affine open in X over V, and with
   B → D = ∏ D_j faithfully flat and finitely presented. Put A = ∏ A_j.
2. If a ≫ b is flat, the affine criterion lem-weil-pbc-flat-morphism-affine-criterion
   and lem-weil-pbc-finite-product-flat-modules make A flat over C. In the finite-type
   case, lem-weil-pbc-lft-affine-pairs gives finite generators of each A_j over C;
   their coordinate-supported images and the coordinate idempotents generate A.
   In the finite-presentation case, lem-weil-pbc-lfp-affine-opens-finite-presentation
   gives finite presentations of each A_j, and
   lem-trf-finite-affine-composite-presentation applied over Spec C with identity
   structure map gives finite presentation of A over C. The empty product is the
   zero algebra, which satisfies all three properties.
3. For flatness, tensor an injection N → N₁ of C-modules with B. An element of its
   kernel vanishes after tensoring with A, since A is C-flat, and hence with D.
   By lem-weil-pbc-faithfully-flat-universally-injective the map N ⊗ B → N ⊗ D
   is injective: identify it with M → M ⊗[B] D for M = N ⊗[C] B.
   The element was zero, giving flatness of C → B by def-weil-pbc-flat-ring-map.
4. For finite type, generators of D over B also generate it over A. Combining them
   with the generators of A over C makes D finite type over C. Apply
   lem-a1-finite-type-fppf-source-algebra to C → B → D to get B finite type over C.
5. For finite presentation, A is finite type over B since it is finite type over C.
   The finite presentation of D over B and
   lem-weil-pbc-finite-presentation-over-finite-type-algebra give finite presentation
   of D over A. Compose with C → A using
   lem-weil-pbc-finite-presentation-base-change-composition. Then apply
   lem-trf-finite-presentation-fppf-source-algebra to C → B → D.
6. V and W were arbitrary. Apply the affine criteria for flatness and local finite
   type, and def-sbc-locally-finite-presentation for local finite presentation.
   This also includes empty schemes and empty covering families. -/
theorem properties_of_fppf_refinement_of_comp
    {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    {I : Type v} (T : I → Scheme.{u}) (q : ∀ i : I, T i ⟶ Y)
    (hcover : Presieve.ofArrows T q ∈ Scheme.fppfPrecoverage Y)
    (s : ∀ i : I, T i ⟶ X) (hlift : ∀ i : I, s i ≫ a = q i) :
    (Flat (a ≫ b) → Flat b) ∧
      (LocallyOfFiniteType (a ≫ b) → LocallyOfFiniteType b) ∧
      (LocallyOfFinitePresentation (a ≫ b) → LocallyOfFinitePresentation b) := by
  sorry

end AlgebraicGeometry
