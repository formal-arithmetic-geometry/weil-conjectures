## What changed

Proved `AlgebraicGeometry.Etale.unrestricted_strictHenselization_stalk` without changing
its signature. Choose the canonical germ restriction, use its existing isomorphism
lemma, and apply the comparison isomorphism lemma. Split the cohomology comparison factor into its own module and combine it with the
germ restriction. All added imports are proof-only.
Updated the item's DAG proof, proof dependencies and proof origin to this factorization.
The unit `sk-thm-br` has no realized node corresponding to this item; its Brauer-group
injection and Tsen route is unchanged.

Removed the earlier attempt's identical sandbox copies of `StrictLocalGermRestrictionIso`
and `StrictLocalBaseChangeGlobalHomology`: these modules and their nodes already exist
in the library. A new intermediate theorem packages the remaining comparison compatibility; it is documented below as a new node.

## Proved and sorry left

Proved: `AlgebraicGeometry.Etale.unrestricted_strictHenselization_stalk`
(node `lem-weil-pbc-unrestricted-strict-henselization-stalk`), from the existing germ restriction declarations and the split comparison theorem.
One intermediate sorry remains in the new module
`Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso`, named
`AlgebraicGeometry.Etale.isIso_strictHenselizationCohomologyComparison`; its node is
`lem-weil-pbc-unrestricted-strict-henselization-stalk-comparison`.
There are no sorries in the item module.
The existing dependency theorems
`AlgebraicGeometry.Etale.isIso_strictHenselizationStalkRestriction`
(node `lem-weil-pbc-strict-local-germ-restriction-iso`) and
`AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_globalHomology`
(node `lem-weil-pbc-strict-local-base-change-global-homology`) still contain sorry
in the library; they are unchanged and are the next proof obligations.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`
- `Sheaf.AlgebraicGeometry.AffinePointedNeighbourhoodCofinal`
- `Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit`
- `Sheaf.AlgebraicGeometry.FibreProductNeighbourhoodLimit`
- `Sheaf.AlgebraicGeometry.StrictHenselization`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

Removed the unused direct import `Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology`;
its conclusion is needed only by the split comparison obligation.
The last four listed imports already have the declarations needed here publicly exposed
through `StrictHenselizationRestriction`; their definitions are still needed.

The following old direct proof dependencies are no longer invoked by this module:
`sbc-lem-higher-direct-image-presheaf`, `def-weil-pbc-geometric-stalks`,
`def-weil-pbc-pointed-etale-neighbourhoods`, `lem-weil-pbc-sheafification-geometric-stalk`,
`lemma-weil-pbc-affine-neighbourhood-cofinal`, `def-weil-pbc-strict-henselization-limit`,
`lemma-weil-pbc-fibre-product-limit`, `def-weil-pbc-scheme-conventions`,
`def-weil-pbc-inverse-image`, `lem-weil-pbc-derived-etale-cohomology-limit`,
`def-weil-pbc-derived-inverse-image`, `lem-weil-pbc-inverse-image-composition`,
`def-weil-pbc-etale-cohomology`.
These are a refactoring of direct dependencies, not a claim that the continuity or
neighbourhood theory is globally unnecessary: it remains below the retained strict-local
lemmas, or in the definitions exposed by `StrictHenselizationRestriction`.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt copied two already-landed modules into the sandbox and imported them
twice. It supplied no node update or report. Reused the existing library declarations and
nodes instead. The original three-step plan is implemented inside the existing strict-local
base-change/global-homology dependency; the assembly here only needs its conclusion and
the germ-restriction isomorphism. Local searches found no independent Mathlib theorem:
Lean Finder returned only topological stalk/pullback lemmas, Loogle did not recognize
`IsIso`, and the Mathlib grep search had no strict-henselization stalk match.

## New nodes

`lem-weil-pbc-unrestricted-strict-henselization-stalk-comparison` records the strict-local
cohomology comparison isomorphism used as the final factor. It is strictly a part of the
item's argument and does not restate the item's existential conclusion. Lean module: `Sheaf.AlgebraicGeometry.StrictHenselizationCohomologyComparisonIso`. File:
`dag/nodes/sec-curve-estimates/lem-weil-pbc-unrestricted-strict-henselization-stalk-comparison.json`.

No change records.

The initial server-cache blocker has cleared: the second reader's dry run compiled
on the server and reached preflight. The remaining preflight issue was the missing
second-reading section, supplied below.

## Second reading by M1

1. Compared the item with the repository version. The entire existing theorem signature
   is byte-for-byte identical; no definitions or target statements changed. The only
   existing-node differences are proof, proof_deps and proof_origin. Verdict: pass.
2. Both delivered files compile locally without errors or non-sorry warnings. Inspected
   all declarations: no axiom, unsafe, opaque, implemented_by, extern or hollow definition.
   Scratch #print axioms checks for both delivered theorems returned exactly
   propext, Classical.choice, Quot.sound and sorryAx from the named open obligations. Verdict: pass.
3. The comparison lemma is only the second factor of the canonical restriction; it does
   not restate the existential stalk theorem. Checked its four-map definition: three
   factors are functor images of isomorphisms, while the global-homology base-change
   factor is supplied by the existing strict-local theorem, specialized to F[0]. The
   argument covers q=0, the zero sheaf and empty X without any torsion hypothesis.
   Independent rg searches of Mathlib, upstream and lean/Sheaf found no duplicate;
   Loogle with qualified IsIso and Lean Finder with functor-preservation wording found
   Functor.map_isIso, which justifies the elementary assembly. Verdict: pass.
4. Read the retained strict-local dependencies and the unit sk-thm-br. Its realized
   arrays contain no nodes for this item, so no unit step is bypassed. All thirteen
   former proof_deps appear under No longer needed; removed imports supply either
   unused direct proof routes or definitions already exposed by the public import.
   All additional existing-module imports are proof-only. Verdict: pass.
5. Checked the new node's declaration, signature, source, proof, ownership, chapter,
   unit, searches and Lean record, and the item's three-step factorization. Each
   dependency is a declaration actually used by this route. Verdict: pass.

Changes: added this independent review and recorded the now-cleared cache blocker.
Tried direct comparison assembly; unfolding and delta both exceeded the 60-second
single-file limit. Passing the base-change proof explicitly also exceeded that limit. Restored the
named comparison obligation unchanged; no additional statements were split off.
The expensive comparison definition needs a separately claimed repair, so this
delivery does not change it or split files to evade the compiler limit.
