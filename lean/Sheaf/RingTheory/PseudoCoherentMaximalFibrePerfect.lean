/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.RingTheory.RingPseudoCoherent
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Sheaf.Algebra.Homology.DerivedChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Sheaf.Algebra.Homology.BoundedFlatKFlat
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Ideal.Maximal
import Sheaf.Algebra.Homology.FreeComplexResidueDegreeCancellation
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.RingTheory.PerfectPrincipalCoverGlue
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients

/-!
# Perfectness detected by uniformly bounded maximal residue fibres

Source: Stacks Project, More on Algebra, Tag 068V, lemma-check-perfect-pointwise,
implication (3) to (1) (blueprint: lem-weil-pbc-pseudocoherent-maximal-fibre-perfect).

The derived tensor is the existing monoidal structure on the module derived category.
For a maximal ideal, its quotient ring is regarded as an R-module in degree zero.
Vanishing of the underlying R-module cohomology is equivalent to vanishing of the
residue-field cohomology of derived scalar extension.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory

/-- A pseudo-coherent complex with maximal residue fibres concentrated in the fixed interval
is perfect, and its derived tensor with every module has cohomology in that same interval.

Source: Stacks Project, Tag 068V, implication (3) to (1).
Proof:
1. Choose a bounded-above finite-free representative P by
   def-pc-ring-pseudo-coherent-complex. It is K-flat by lem-pc-module-bounded-flat-kflat
   and def-pc-module-kflat-complex. The comparison lem-pc-source-kflat-module-tensor-model
   computes derived tensors with arbitrary modules; lem-pur-derived-change-of-rings gives
   scalar extension with its target-ring structure. Localization commutes with cohomology:
   clear denominators in cycles and boundaries to obtain mutually inverse maps.
2. For each degree outside the interval, apply
   lem-weil-pbc-free-complex-residue-degree-cancellation at each maximal ideal. The resulting
   localized complex has zero term in that degree. Hence its cohomology vanishes locally,
   and lem-weil-pbc-linear-map-bijective-at-maximal-localizations applied to the map to zero
   shows the original cohomology vanishes.
3. Cancel degree a-1 locally by the same cancellation lemma. Split the complex at its zero
   term. The lower summand is acyclic by step 2, so projection onto the upper summand gives
   a bounded finite-free representative supported in degrees at least a.
4. Cancel degree b+1 in this representative near the chosen maximal ideal, and split again.
   The upper summand is acyclic by step 2. Projection now gives a finite-free representative
   supported in [a,b]. Two successive principal localizations combine into one, still away
   from the chosen maximal ideal.
5. These principal elements generate the unit ideal, by
   lem-weil-pbc-proper-ideal-contained-in-maximal; a finite subfamily suffices. Their local
   representatives are perfect by def-pc-perfect-ring-complex. Apply
   lem-weil-pbc-perfect-ring-principal-cover-glue. For the zero ring all modules are zero.
6. Tensor the local representatives supported in [a,b] with an arbitrary module. K-flat
   comparison identifies these with the localized derived tensors; their cohomology outside
   [a,b] vanishes termwise. Detect vanishing at maximal localizations once again using
   lem-weil-pbc-linear-map-bijective-at-maximal-localizations.
(blueprint: lem-weil-pbc-pseudocoherent-maximal-fibre-perfect) -/
theorem isPerfect_and_tensor_homology_vanish_of_maximal_fibres
    {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (C : DerivedCategory (ModuleCat.{u} R)) (hC : C.IsPseudoCoherent)
    (a b : ℤ) (hab : a ≤ b)
    (hfibres : ∀ (m : Ideal R), m.IsMaximal → ∀ i : ℤ, (i < a ∨ b < i) →
      IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj
        (C ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R (R ⧸ m))))) :
    C.IsPerfect ∧ ∀ (M : ModuleCat.{u} R) (i : ℤ), (i < a ∨ b < i) →
      IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj
        (C ⊗ (singleFunctor (ModuleCat.{u} R) 0).obj M)) := by
  sorry

end DerivedCategory
