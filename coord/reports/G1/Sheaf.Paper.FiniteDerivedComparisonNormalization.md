## What changed

Proved the associator and unit/symmetry components of the finite normalized derived
pullback comparison. The proof descends the given cochain counit to the homotopy
category, obtains a right adjoint for that same derived functor from resolving-class
adjunction, and constructs its canonical tensor edge. Uniqueness of the canonical representative
normalization identifies the edge comparison with the existing tensorComparison.
canonicalTensorDiagrams then supplies the required coherence equations; conjugating
its inverse-unitor equations gives the forward unitor equations in this module.

Added the fully proved modules Sheaf.Paper.FiniteDerivedTensorModels,
Sheaf.Paper.CanonicalCochainTensorComparison and
Sheaf.Paper.NormalizedCochainTensorDiagrams, plus
Sheaf.Paper.FiniteTensorComparisonProofSupport. Together they identify the two
ordinary comparison interfaces, the two flat representative
predicates, the tensor-model restriction, the counit components and the unit maps.
These are presentation identifications, with no new mathematical hypotheses or holes.
The common coherence proof is separate from its presentation bridge and its
application to this item. The native-instance and square-pasting proof support is
also separated to meet the per-file compile limit. Its native imports retain the
original coefficient-sized instance context needed to elaborate these signatures.
All added imports in the item are private proof imports. Existing public signatures,
definitions and public imports are unchanged.
The already proved private native instance lemmas, cochain comparison construction,
component and total-tensor map lemmas, and generic tensor-square descent lemmas are
moved to the proof-support module; their proof bodies are retained. The
composition specialization uses the same argument through the imported support. The
native tensor-model naturality and cochain compositor equations are proved once in
that API and reused in the specialization, avoiding repeated large unfoldings. No
adopted source-library file is changed.

Validation: lcompile.py --all succeeds without warnings. The final item compile
took 55.0 seconds and the extracted support file took 26.1 seconds; all five
files passed the per-file limit.

## Proved and sorry left

Closed both original holes (2 of 2):

- CategoryTheory.FiniteDerivedComparison.tensorComparison_coherence_associator
  (lem-pur-finite-derived-comparison-normalization-associator).
- CategoryTheory.FiniteDerivedComparison.tensorComparison_coherence_unit_symmetry
  (lem-pur-finite-derived-comparison-normalization-unit-symmetry).

No sorry remains in the item; none is added in any helper module. No hole is split off.
The proofs use existing dependency declarations, including canonicalTensorDiagrams;
those dependencies remain separate stage-3 items where they still contain sorry.
The right-derived functor uses the already proved CategoryTheory.exists_derived
helper from Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition.

## No longer needed

The two coherence-component proofs do not directly use
lem-pur-cochain-pullback-tensor-coherence
(Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence),
lem-weil-pbc-site-derived-tensor-descent
(Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients), or
lem-sfb-ringed-derived-monoidal-comparisons
(Sheaf.SixFunctors.RingedDerivedMonoidalComparisons).
Their old direct proof-dependency edges are replaced by the canonical tensor-diagram
route and the explicit presentation bridge. These modules are not withdrawn: other
proofs and existing imports still need them. In particular the item's shift and unit
imports retain their public imports of the cochain coherence module. No existing
public import is removed and no globally unreachable module is claimed pruned.
The composition proof also replaces the old direct
lem-weil-pbc-resolving-representative-whiskering edge
(Sheaf.Paper.ResolvingRepresentativeWhiskering) by its actual fully faithful
restriction argument; no module is withdrawn on this account.

## Where the brief, the DAG or earlier work was wrong

The older component plans called for separate descent arguments. The library already
states canonicalTensorDiagrams for the same normalized comparisons, so only the
identification of its presentations with those of this module is needed. The required
derived adjunction can be produced for the supplied universal derived functor, without
replacing that functor or changing the target statements. The unit's realized route is
unchanged. The proof uses no stronger flatness, exactness or boundedness assumptions.

## New nodes

lem-pur-finite-derived-tensor-model-bridge records the fully proved presentation
identifications in Sheaf.Paper.FiniteDerivedTensorModels. The native and site-flat
predicates are related by the existing natural tensor isomorphism; total comparison
maps retain the same ordinary tensor isomorphisms. The unit identification follows
from the existing scalar-action unit specification and its single-complex definition.
The constructions also apply to identity pullbacks and zero complexes, without
nonzero assumptions. There is no new unfinished theorem and no change record is needed.

lem-pur-normalized-cochain-tensor-diagrams records the fully proved general coherence
argument for a specified universal cochain counit and a tensor comparison normalized
on native flat-term K-flat complexes. The item supplies both the computation and the
normalization hypotheses from its previously proved declarations. The general theorem
introduces no assumption into the item's public statements and leaves no proof hole.

lem-pur-canonical-cochain-tensor-comparison records the fully proved
canonicalComparison_eq lemma. It rewrites the restricted tensor models and the
homotopy counit components, then applies uniqueness of the canonical representative
square. It is separate from the model constructions and the general coherence proof
to keep all three files within the compile limit. Its source is the same canonical
comparison construction in Stacks 07A4 and 0G7E.

lem-pur-finite-tensor-comparison-proof-support records the previously proved generic
square-pasting and cancellation argument, now extracted with the native tensor instance
cache and the native cochain comparison and map API. Its comparison_tensor_descends
proof uses fully faithful restriction only after
proving the representative equation. No existing public declaration is moved or removed;
only proof support is relocated. The composition node's restriction dependency is also
corrected from resolving-representative-whiskering to the actually used
derived-resolving-pair-restriction theorem.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
