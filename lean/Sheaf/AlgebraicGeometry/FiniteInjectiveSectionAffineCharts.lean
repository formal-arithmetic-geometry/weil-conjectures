/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q152
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.NoetherianSpace

/-! # Affine charts along finite surjections with injective section maps

Source: Stacks Project, Algebra, Tag 00IS; affine-chart assembly of the retained
finite-surjection argument (blueprint: lem-sfb-finite-injective-section-affine-charts).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- A finite surjective morphism with injective maps on affine sections has finite-type
Noetherian affine charts over the base field.

Source: Stacks Project, Algebra, Tag 00IS, together with Morphisms, Tags 01T2,
01T6 and 01WH (blueprint: lem-sfb-finite-injective-section-affine-charts).

Proof plan (the six steps of the DAG node):
1. Finite type of a gives quasi-compactness of X and a finite affine cover by
lem-pqf-finite-affine-cover-qc-open. The affine-pair characterization
lem-weil-pbc-lft-affine-pairs gives finite type over k of each chart ring.
2. By lem-wf-affine-noetherian-components those rings are Noetherian. Thus X is
locally Noetherian by pqf-def-locnoeth and quasi-compact, hence Noetherian.
3. Pull an arbitrary open cover of Z back to X and choose a finite subcover.
Surjectivity of q makes the corresponding finitely many opens cover Z, so Z is
quasi-compact. This also works for the empty cover when X is empty.
4. Apply lem-pqf-finite-affine-cover-qc-open to Z. For any affine open W, finiteness
of q gives an affine inverse image and a finite module map on sections. Apply
lem-weil-pbc-lft-affine-pairs to a and this affine inverse image to get B finite type.
5. The relation q followed by b equals a makes the injective section map a k-algebra
map, identifying A with its image subalgebra T in B. The generators of B as an
A-module generate B as a T-module by replacing coefficients with their images.
A field is Noetherian: any nonzero ideal element is a unit, so the ideal is top;
otherwise it is zero. Apply lem-sfb-artin-tate-subalgebra-finite-type to T in B.
Lift the algebra generators of T through A to obtain finite type of A over k.
6. Apply lem-wf-affine-noetherian-components to A to conclude Noetherianity.
For the empty affine open both section rings are zero; none of the algebraic
inputs requires a nonzero ring, and Fin 0 allows the empty cover.
-/
theorem finite_injective_section_affine_charts
    {k : Type u} [Field k]
    {X Z : Scheme.{u}}
    (a : X ⟶ Spec (CommRingCat.of k))
    (b : Z ⟶ Spec (CommRingCat.of k))
    (q : X ⟶ Z)
    (hcomp : q ≫ b = a)
    [LocallyOfFiniteType a] [QuasiCompact a]
    [IsFinite q] [Surjective q]
    (hinj : ∀ (V : Z.Opens), IsAffineOpen V →
      Function.Injective (q.app V).hom) :
    IsLocallyNoetherian X ∧ CompactSpace X ∧
      ∃ (n : ℕ) (V : Fin n → Z.Opens),
        (∀ j, IsAffineOpen (V j)) ∧
          (⨆ j, V j) = ⊤ ∧
            ∀ (W : Z.Opens), IsAffineOpen W →
              IsAffineOpen (q ⁻¹ᵁ W) ∧
                Function.Injective (q.app W).hom ∧
                (q.app W).hom.comp
                    ((b.appLE ⊤ W le_top).hom.comp
                      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) =
                  (a.appLE ⊤ (q ⁻¹ᵁ W) le_top).hom.comp
                    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom ∧
                RingHom.FiniteType
                  ((a.appLE ⊤ (q ⁻¹ᵁ W) le_top).hom.comp
                    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) ∧
                (q.app W).hom.Finite ∧
                RingHom.FiniteType
                  ((b.appLE ⊤ W le_top).hom.comp
                    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) ∧
                IsNoetherianRing (Γ(Z, W)) := by
  sorry

end AlgebraicGeometry
