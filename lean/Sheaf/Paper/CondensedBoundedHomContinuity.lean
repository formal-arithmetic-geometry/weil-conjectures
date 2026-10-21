/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Sheaf.Paper.ConstructibleHomContinuityDevissage
import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import Sheaf.Paper.CondensedSheafExtContinuity
import Sheaf.CategoryTheory.DerivedCategory.BoundedCohomologyConeWitness
import Mathlib.CategoryTheory.Triangulated.Triangulated

/-! # Shifted Hom continuity for bounded constructible condensed complexes

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/
lem-sfb-constructible-cocone-hom-surj.proof.md, paragraph 2.
(blueprint: lem-sfb-condensed-bounded-hom-continuity)

The cocone is a colimit degree by degree in the module category. Its image under the
ordinary derived localization need not be a colimit in the derived category.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The canonical additive comparison for a bounded constructible condensed complex is
an isomorphism in every integer shift, for a filtered diagram with a common termwise
lower bound and any supplied termwise colimit cocone.

Source: blueprint main-20261015, lem-sfb-constructible-cocone-hom-surj.proof.md,
paragraph 2 (blueprint: lem-sfb-condensed-bounded-hom-continuity).

Proof:
1. For the fixed diagram and cocone let P(C) assert the comparison for every integer
shift. The formal part of det-lem-constructible-ext-continuity-devissage proves closure
under shifts, isomorphisms and distinguished extensions on any scheme. Degreewise
universality identifies the supplied cocone with the chosen complex colimit: the
degreewise identifications commute with the differentials since they do so on every
colimit leg. Thus they preserve the canonical comparison (def-weil-pbc-category-colimit).
2. By def-sfb-dcons-subfield and sk-def-sfb-bounded-constructible, K has bounded,
constructible cohomology. Apply lem-weil-pbc-condensed-sheaf-ext-continuity to each
H^q(K), the same finite E, the topologically Noetherian X and the common lower bound
of N. This proves P for each cohomology module placed in degree zero, hence for its
shifts. No constructibility of the second arguments is used.
3. Apply lem-sfb-bounded-cohomology-cone-witness to K.obj. Induct along its finite list
ending in K.obj. Shifted cohomology leaves satisfy P by step 2 and isomorphism closure.
For a cone step F_i -> F_j -> F_r[s] -> F_i[1], with i,j earlier, rotate the distinguished
triangle by TR2 (def-weil-triangulated-category). Its endpoints F_j and F_i[1] satisfy P,
so extension closure gives P(F_r[s]); shift back to obtain P(F_r). This also covers K=0.
4. Evaluate P(K.obj) at n. The comparison throughout is induced by the fixed shifted
cocone legs: its value on a representative u_i is u_i followed by Q(c.ι.app i)[n].
The source colimit is in abelian groups; no derived colimit property is assumed.
-/
theorem isIso_boundedConstructible_condensed_hom_colimit
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K : PadicSubfieldConstructible X ℓ E)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (N : I ⥤ CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) ℤ)
    (c : Cocone N)
    (hc : ∀ r : ℤ, IsColimit ((HomologicalComplex.eval _ _ r).mapCocone c))
    (hN : ∃ a : ℤ, ∀ (i : I) (r : ℤ), r < a → IsZero ((N.obj i).X r))
    (n : ℤ) :
    IsIso (colimit.desc _
      ((DerivedCategory.Q ⋙ shiftFunctor _ n ⋙
        preadditiveCoyoneda.obj (op K.obj)).mapCocone c)) := by
  sorry

end AlgebraicGeometry.ProEtale
