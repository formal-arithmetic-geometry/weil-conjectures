## What changed

Replaced the rejected restatement from the earlier attempt with the componentwise proof
of `AlgebraicGeometry.IsCurve.assertions_of_isIso_comp`, with its signature unchanged.
The proof constructs the normalized retraction, proves injectivity on cohomology, and
proves surjectivity and bijectivity of pullbacks descend, using three proved private helpers.
It then fills all eight assertion fields, transferring the supplied conditional hypotheses.
No existing definition or statement was changed, and the unit route is preserved.

Added the proof import `Sheaf.AlgebraicGeometry.ConstructibleIntegralCoefficients`.
This new module isolates the comparison between underlying-set constructibility and
module constructibility for torsion sheaves with canonical integral coefficients.
The comparison is needed only for C4 and C5. It is not a renamed assertion-transfer theorem:
it mentions neither retracts, curve assertions, cohomology, finiteness of cohomology,
field extensions, nor the theorem's coefficient-transfer hypotheses.
Updated the item's DAG proof and dependencies to follow the Lean proof.

## Proved and sorry left

`AlgebraicGeometry.IsCurve.assertions_of_isIso_comp`: its one original sorry is removed.
The complete componentwise proof compiles from the comparison theorem below.
`cohomology_section_injective`, `pullback_surjective_of_retract`, and
`pullback_bijective_of_retract` are private, completely proved helpers.

The only sorry in the delivery is
`AlgebraicGeometry.Scheme.isConstructibleSheaf_integral_iff`, node
`q1-constructible-integral-coefficients`, in its own new module.
Its source and full natural-language proof are in its docstring and node.
The torsion hypothesis is essential: a constant integral module Z is finitely generated,
while its underlying set is infinite. Empty schemes, empty trivializing cover members,
the zero sheaf, finite constant torsion groups, and algebraically closed versus
separably closed geometric fields are addressed in the proof in words.

## No longer needed

Removed imports:
- `Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (already exposed by Assertions;
  the actual upperStar declaration is still used).

Removed proof dependencies:
- `lem-weil-pbc-cohomology-pullback-functorial`: the needed naturality is already proved
  as `Etale.cohomologyMap_map` in TopologicalInvariance. Composition in scheme morphisms
  and identity coherence are not needed here.
- `def-weil-pbc-etale-cohomology`: assertions use Sheaf.H directly; comparison to derived
  global sections and K-injective resolutions is not needed for this retract proof.
- `lem-weil-pbc-functor-preserves-retract`: use map_comp and map_id directly.
- `lem-weil-pbc-retract-of-zero-object`: use injectivity into a subsingleton directly.

Dropped the unlanded restatement node `lem-weil-pbc-curve-assertions-retract-core` and
its declaration from the sandbox. Neither is used. All C1--C8 definitions, coefficient
conditions, inverse image, pullback and assertion-package nodes remain dependencies.
This prunes dependencies of this item; other target branches may still need them.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt moved the entire conclusion into an identical `_core` theorem and
therefore made no reduction. This delivery instead writes the normalized-retraction and
all eight component arguments. The DAG's resolution-lifting detour is unnecessary:
the existing Ext cohomology API already proves composition, identities and naturality.

The planned constructibility transfer silently crosses two predicates: the hypothesis
is set-valued `CurveCoefficientPair.IsConstructible`, whereas C4 and C5 ask for
`Scheme.IsConstructibleSheaf` of integral modules. Existing comparisons for finite
coefficient rings and for bounded Z/n sheaves do not give this integral comparison.
The new comparison explicitly retains torsion, without which it would be false.
Read Stacks Tags 03RW and 095E on their public pages; the local literature tree on this
machine does not contain etale-cohomology.tex. The comparison proof is agent-written
from those definitions, and is not claimed as a verbatim Stacks lemma.
LeanSearch returned HTTP 500; the actual failed search is recorded as unavailable.
LeanFinder, Loogle, Mathlib grep, the source-library search and blueprint search were run.

## New nodes

`q1-constructible-integral-coefficients`: equivalence of the two constructibility
predicates for a torsion abelian sheaf on any scheme, after conversion to canonical
ULift Z coefficients. The source comparison, finite-stalk argument, and refinement
making finite group operation tables constant are written in its proof.
There are no change records because existing statements and definitions are unchanged.

## Second reading by Q1

1. Compared the delivered `RetractAssertions.lean` with the repository version. The theorem
   signature and all existing declaration statements are byte-for-byte unchanged; only the
   proof body and proof-only imports differ. The added module and node are explicitly recorded.
   Verdict: pass.
2. Compiled both sandbox modules with `lcompile.py --all`; both compile without errors or
   warnings. The target theorem has no `sorry`; the only remaining `sorry` is the named,
   documented `isConstructibleSheaf_integral_iff` split theorem. No forbidden declarations or
   hollow definitions occur. Verdict: pass.
3. Checked `isConstructibleSheaf_integral_iff` against its torsion hypothesis and edge cases
   (zero and empty sheaves, finite stalks, and the failure for nontorsion constant `ℤ`). Its
   statement is the exact constructibility transfer needed by C4 and C5, and is not a
   restatement of the retract assertion. The node, docstring, and Lean declaration agree.
   Verdict: pass.
4. Read the proof from the target downward. It uses direct `Sheaf.H` functoriality and the
   existing `Etale.cohomologyMap_map`, then the new constructibility comparison only where
   required. Removed imports and dependencies are listed above; the unit route and all eight
   assertion fields are retained. Verdict: pass.
5. Checked the DAG node proofs, dependencies, origins, and the new node's Lean record against
   the code. The old unlanded restatement node is removed, and the unit's realized route is
   preserved. Verdict: pass.

Changed during second reading: no mathematical statements or definitions; added this review
record only. The delivery remains the componentwise retract proof plus the documented
constructibility comparison split.
