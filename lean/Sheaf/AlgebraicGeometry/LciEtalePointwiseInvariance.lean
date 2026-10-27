/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Sheaf.TraceFormula.LciPointwiseCriterion
public import Sheaf.RingTheory.CompleteIntersectionLocalAlgebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Sheaf.TraceFormula.SyntomicLocusBaseChange

/-!
# Étale invariance of the pointwise complete-intersection condition

Source: Stacks Project, Descent, Tag 036S, and Morphisms, Tags 01UE and 02V3
(blueprint: lem-sfb-lci-etale-pointwise-invariance).

The local-ring meaning is that of `lci_pointwise_criterion`, expressed using the
existing `Algebra.IsCompleteIntersectionLocalAlgebra` predicate of Algebra, Tag 00SD.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An étale morphism over a field preserves and reflects the complete-intersection
condition at corresponding local rings. The scalar structures on both stalks come from
their specified structure morphisms. No surjectivity, quasi-compactness, separation,
perfection, or nonemptiness is assumed.

Source: Stacks Project, Descent, Tag 036S; Morphisms, Tags 01UE and 02V3; and
Algebra, Tag 00SD (blueprint: lem-sfb-lci-etale-pointwise-invariance).

Proof:
1. The structural morphisms of `Y` and `Z` are flat: their stalks are vector spaces,
   hence flat by lem-weil-pbc-module-over-field-flat and def-weil-flat-morphism.
   The field spectrum is locally Noetherian (pqf-def-locnoeth), so local finite type
   implies local finite presentation by pqf-lem-lft-fp-locnoeth.
2. Apply lem-trf-syntomic-locus-base-change to both structural morphisms. Their fibre
   over the unique point of Spec k is the scheme itself, with its given k-action
   (def-pc-scheme-fibre). Thus the largest syntomic source opens L_Y and L_Z are exactly
   their complete-intersection stalk loci, in the sense of lem-trf-lci-pointwise-criterion.
3. If e(z) lies in L_Y, restrict e to e⁻¹(L_Y) → L_Y. This map is étale by open-immersion
   composition and cancellation (lem-weil-pbc-etale-composition-cancellation).
   Syntomic ascent from lem-sfb-syntomic-etale-source-locality makes its structural
   morphism syntomic. Maximality of L_Z gives z ∈ L_Z.
4. Conversely, if z ∈ L_Z, the image V = e(L_Z) is open by
   lem-weil-pbc-etale-morphism-open-map. The map L_Z → V is surjective and étale,
   using the same composition and cancellation. Descent along this singleton cover
   (lem-sfb-syntomic-etale-source-locality) makes V → Spec k syntomic, whence
   e(z) ∈ V ⊆ L_Y by maximality. Empty sources have no points to test; e need not cover Y.
-/
theorem lci_etale_pointwise_invariance (k : Type u) [Field k]
    (Y Z : Scheme.{u}) (sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))
    [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]
    (e : Z ⟶ Y) [Etale e] (_he : e ≫ sY = sZ) (z : Z) :
    @Algebra.IsCompleteIntersectionLocalAlgebra k (Z.presheaf.stalk z) _ _
      (((Scheme.ΓSpecIso (.of k)).inv ≫ sZ.appLE ⊤ ⊤ le_top ≫
        Z.presheaf.germ ⊤ z trivial).hom.toAlgebra) ↔
    @Algebra.IsCompleteIntersectionLocalAlgebra k (Y.presheaf.stalk (e z)) _ _
      (((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appLE ⊤ ⊤ le_top ≫
        Y.presheaf.germ ⊤ (e z) trivial).hom.toAlgebra) := by
  sorry

end AlgebraicGeometry
