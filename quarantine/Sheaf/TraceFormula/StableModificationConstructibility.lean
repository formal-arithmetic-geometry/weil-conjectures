/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.AlgebraicGeometry.SemistableMultipointedPair
public import Sheaf.AlgebraicGeometry.MultipointedCurveModification
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Constructible
import WeilConjectures.AlgebraicGeometry.Morphisms.FlatFibreEtaleNeighbourhoods
import Sheaf.AlgebraicGeometry.SmoothAtPointFibreCriterion
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.SemistableMarkedBaseChange
import Sheaf.TraceFormula.GenusZeroSmoothProperLine
import Sheaf.AlgebraicGeometry.ProjectiveLineGenusZero

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.AlgebraicGeometry.NodalNormalizationAdjunction
import Sheaf.TraceFormula.ContractedComponentGenericData
import Sheaf.TraceFormula.NodalOpenLocus
/-! # Constructibility of semistable and stable geometric fibres

Source: Temkin, *Stable modification of relative curves*, Lemma 5.1(ii), printed p. 34
(blueprint: lem-trf-stable-modification-constructibility).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/--
Source: Temkin, *Stable modification of relative curves*, Lemma 5.1(ii), printed p. 34
(blueprint: lem-trf-stable-modification-constructibility).

Proof, following the seven steps of the DAG node:
1. Finite presentation makes the total spaces Noetherian. Apply
   `lem-trf-nodal-open-locus` to obtain a closed bad curve locus whose fibre is empty
   exactly when the geometric curve fibre has only ordinary nodes as singularities.
2. On the marking, take the union of the non-etale locus and the inverse image of the
   curve's nonsmooth locus. The flat fibre etale criterion and smooth-at-point fibre
   criterion identify avoidance of this closed set with both marking conditions.
3. Apply `lem-weil-pbc-chevalley-constructible-image` to the two closed bad loci.
   The complement of their images is the semistable constructible set.
4. Write this set as a finite union of locally closed subsets and give each the reduced
   induced scheme structure. Pull back the pairs and the proper maps; the fibres remain
   the original semistable fibres. No modification property after restriction is used.
5. On each stratum use Noetherian induction on closed subsets. On every reduced integral
   component, `lem-trf-contracted-component-generic-data` makes the finite multiset of
   contracted-component triples (arithmetic genus, self-nodes, special points) constant
   on a dense open. Delete intersections with other components and partition the proper
   closed complement inductively. This gives a finite locally closed partition.
6. By `lem-trf-nodal-normalization-adjunction` zero self-nodes means the component is
   smooth. For a contracted component, properness and arithmetic genus zero then identify
   it with the projective line using `lem-trf-genus-zero-smooth-proper-line`. Conversely
   `lem-asd-projective-line-genus-zero` gives zero genus and no self-nodes for that line.
   Thus the exceptional triples are exactly (0,0,b) with b at most two, counting distinct
   points on the component.
7. Select the finitely many partition pieces with no exceptional triple. Their union is
   exactly the stable set and is constructible. Neither generization stability nor
   semistability over the whole base is used.
-/
theorem stable_modification_constructibility
    {S : Scheme.{u}} [IsIntegral S] [IsNoetherian S]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (X Y : MultipointedCurve S) (f : Y.Hom X)
    (hf : f.IsEtaModification (S.fromSpecResidueField η)) :
    ∃ Cₛ Cₜ : Set S,
      Topology.IsConstructible Cₛ ∧ Topology.IsConstructible Cₜ ∧
      (∀ s : S,
        s ∈ Cₛ ↔
          ((MultipointedPair.ofCurve Y).baseChange
            (S.fromSpecResidueField s)).IsSemistable) ∧
      (∀ s : S,
        s ∈ Cₜ ↔
          ((MultipointedPair.ofCurve Y).baseChange
            (S.fromSpecResidueField s)).IsSemistable ∧
          MultipointedPair.HasGeometricStability
            ((MultipointedPair.ofCurve Y).baseChange
              (S.fromSpecResidueField s))
            ((MultipointedPair.ofCurve X).baseChange
              (S.fromSpecResidueField s))
            ((Over.pullback (S.fromSpecResidueField s)).map
              (Over.homMk (U := Over.mk Y.x) (V := Over.mk X.x) f.curve
                f.curve_over))) := by
  sorry

end AlgebraicGeometry
