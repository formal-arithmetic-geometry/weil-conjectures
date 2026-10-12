## What changed

Replaced the remaining proof of `CategoryTheory.cohomology_colimit_sites_eventual_vanishing`
by induction on the degree, generalizing the entire compatible sheaf system and its
cohomology diagram. The degree-zero argument uses injectivity of the group-colimit
comparison and Mathlib's finite-stage equality theorem. In positive degree a corrected
lower-degree lift is killed by the induction hypothesis; naturality of its connecting
transformation and functoriality identify the resulting zero with the transitioned class.
The original declaration and all its hypotheses are unchanged.

Added two modules, each with one public intermediate theorem, a source, a proof in words,
and a node. Updated the item's proof plan to match the induction actually written.
Only ordinary proof imports were changed; the public imports were retained.

## Proved and sorry left

The item's one original sorry is reduced to the following two named intermediate theorems:

- `CategoryTheory.cohomology_colimit_sites_zero_comparison_injective`
  (`lem-weil-pbc-colimit-sites-zero-comparison-injective`): injectivity of the comparison
  from the degree-zero group colimit. This is restricted to degree zero and does not
  assert eventual vanishing.
- `CategoryTheory.cohomology_colimit_sites_corrected_lift`
  (`lem-weil-pbc-colimit-sites-corrected-lift`): a natural connecting transformation
  from a compatible system one degree lower, with target-zero corrected lifts. This
  does not kill the lifts. That step is the induction in the delivered main proof.

These are the only sorries in the delivery. The main theorem has no direct sorry.
Their standard source arguments use existing lemmas, including class descent only in
strictly smaller degree for the correction from the injective system. No use is made
of class descent or eventual vanishing in the degree being proved.

## No longer needed

Removed the direct proof imports `Sheaf.CategoryTheory.ColimitSiteCechComplex`,
`Sheaf.CategoryTheory.ColimitSiteSections`, `Sheaf.CategoryTheory.SiteCechVanishingCriterion`,
`Sheaf.CategoryTheory.SiteInjectiveCechAcyclic`, `Sheaf.Paper.ColimitSitesInjectiveSystem`,
and `Sheaf.CategoryTheory.SiteCechComplex`.
The main induction uses neither a Čech complex nor an injective embedding directly.
The section comparison and injective embedding remain needed below the two new nodes.
The Čech comparison, injective Čech acyclicity and Čech criterion remain needed by the
existing lower-degree class-descent theorem. These modules are not globally obsolete.

The original direct proof dependencies are replaced by the two new nodes and
`def-weil-pbc-category-colimit`. In particular the main proof has no direct use of
`lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`,
`lem-weil-pbc-filtered-colimit-abelian-groups-exact`,
`def-weil-pbc-site-cech-complex`, or `lem-weil-pbc-derived-functor-injective-vanishing`.
Exact sheaf colimits and stage injective vanishing remain below the corrected-lift node.
No unit statement or realized unit step has been bypassed.


Complete list of removed direct proof dependencies (retained below helpers or in signatures
where applicable; no claim of global obsolescence):

- `lem-weil-pbc-colimit-of-sites`
- `def-weil-pbc-sites-and-cohomology`
- `lem-weil-pbc-site-cohomology-pullback`
- `lem-weil-pbc-colimit-of-sites-sections`
- `lem-weil-pbc-colimit-of-sites-injective-system`
- `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`
- `lem-weil-pbc-colimit-of-sites-cech-complex`
- `lem-weil-pbc-site-injective-cech-acyclic`
- `lem-weil-pbc-filtered-colimit-abelian-groups-exact`
- `def-weil-pbc-site-cech-complex`
- `lem-weil-pbc-site-cech-vanishing-criterion`
- `lem-weil-pbc-derived-functor-injective-vanishing`

The second reading also removed the redundant direct proof import
`Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`; its declarations are available
through `Mathlib.Algebra.Category.Grp.FilteredColimits`.

## Where the brief, the DAG or earlier work was wrong

The existing ColimitSiteSections declaration compares sections of a fixed diagram of
sheaves already on the colimit site. It does not by itself identify the stage section
groups with those sections: the inverse-image inner-colimit formula of Sites 0A35 and
flattening in Sites 09YN are still needed. The degree-zero helper records that gap.

The corrected-lift argument needs stage injective acyclicity and exactness at the target
cokernel cohomology group. It does not need positive-degree acyclicity of the injective
colimit at that point. Degree-n class descent for the injective system supplies the
correction, and the induction in this delivery supplies degree-n detection for the
cokernel system. Thus using the corrected-lift helper is strictly part of the argument,
not moving the original eventual-vanishing statement to a new name.

Edge cases checked in the statements: degree zero is handled separately; the corrected
lift has degree n+1 and includes n=0; zero sheaf systems allow the zero lift; a filtered
index category is nonempty, and arbitrary stages t are retained. No surjectivity or
finite-stage detection hypothesis is added to the main theorem. All endpoint transports
and both map compatibility hypotheses are retained in the new statements.

Searches used LeanFinder, Loogle and Mathlib grep; LeanSearch returned Internal Server
Error and is recorded as unavailable. Blueprint searches for colimit sites and dimension
shifting found no existing node; the finite-stage search gave unrelated statements.
The source paragraphs read were Stacks 09YP, 0739, 09YN and 0A35.

A full DAG closure scan encounters an existing cycle between
`lem-weil-pbc-sheaf-algebraic-structures-objects` and
`lem-weil-pbc-sheaf-algebraic-structures-abelian-component`. Neither new node has a
dependency path back to the item; this delivery introduces no cycle involving its nodes.
The unrelated existing cycle is reported for maintainer attention.

## New nodes

`lem-weil-pbc-colimit-sites-zero-comparison-injective`, in
`Sheaf.CategoryTheory.CohomologyColimitSitesZeroComparison`, isolates degree-zero
comparison injectivity before Mathlib's finite-stage equality argument.

`lem-weil-pbc-colimit-sites-corrected-lift`, in
`Sheaf.CategoryTheory.CohomologyColimitSitesCorrectedLift`, isolates the injective/cokernel
construction and correction of a connecting lift. Its conclusion stops before killing
that lift, which the delivered induction proves. No change records are required:
existing public statements and public imports are unchanged.

## Second reading by F2

1. Compared the complete module diff and extracted the original declaration's signature.
   Verdict: byte-for-byte unchanged; no existing definition or public import changed.
   Only the original proof body and ordinary proof imports change. The two other modules
   and their declarations are new, and require no existing-statement change record.
2. Compiled all three modules locally with lcompile.py, without errors or warnings.
   Scanned each whole file: no forbidden declaration or attribute, no hollow definition,
   and precisely two sorries, each the entire proof of the named helper listed above.
   A scratch module printed axioms of all three declarations: only propext,
   Classical.choice, Quot.sound and sorryAx. Thus the main theorem is a checked reduction,
   not yet an axiom-free completion of continuity. Its zero branch uses finite-stage
   equality of group-colimit representatives; its successor branch evaluates naturality
   of delta and composes the two transition arrows.
3. Read the full two new signatures and their docstring arguments against
   [09YP](https://stacks.math.columbia.edu/tag/09YP),
   [0739](https://stacks.math.columbia.edu/tag/0739),
   [09YN](https://stacks.math.columbia.edu/tag/09YN), and
   [0A35](https://stacks.math.columbia.edu/tag/0A35).
   Verdict: genuine parts of the argument, not restatements of eventual vanishing.
   The corrected-lift lemma constructs a compatible cokernel system and a natural
   connecting map in strictly lower degree; the original theorem supplies the killing
   of its corrected class. Checked degree n=0, zero classes and zero systems, a single
   identity stage, arbitrary starting stage, and the endpoint equality transports.
   Naturality and connecting-map compatibility are available for every sheaf, including
   the auxiliary systems. Stage injectivity suffices to lift in degree n+1, while target
   exactness at H^n(R) and lower-degree class descent suffice for the correction; target
   injective acyclicity is not needed at that point.
   Searched independently with LeanFinder for dimension shifting and kernel lifts,
   Loogle for injectivity of colimit.desc, and grep for sheaf colimits and surjective
   connecting maps; no existing declaration closes either helper. One exploratory
   Loogle query was malformed and was not counted as evidence. Read the upstream
   nonempty_iso_of_connecting theorem: it requires compatible cohomology functors on an
   abelian category of systems and the connecting-map/exactness data that these helpers
   still construct, so it gives no immediate shortcut. Neither helper can be closed by
   a few-minute specialization of the available results.
4. Checked the induction from the original item downward, the original proof dependencies,
   all removed imports, and dag/units/sk-thm-p1.json realized statements and steps.
   Verdict: the unit's realized nodes are not bypassed. The six original direct proof
   imports are removed, but remain below class descent where appropriate. Completed
   No longer needed with SiteCechComplex and the exact twelve old dependency IDs removed
   from the main node. Tested dropping two additional Mathlib imports: Filtered.Final
   is required for the filtered Under-category instance; ConcreteCategory.Basic is
   redundant through Grp.FilteredColimits and was removed. Public imports remain needed
   by the signatures. No module is asserted globally obsolete.
5. Checked every node's proof and proof_origin against the source route and Lean reduction.
   Verified proof_deps is exactly the union of proof-step uses; both new lean.statement
   records equal the whitespace-normalized full signatures, and each named sorry has its
   matching node, source and complete proof docstring. Existing node changes are confined
   to proof, proof_deps and proof_origin. New-node metadata includes creation, blueprint,
   chapter, unit and actual Mathlib search records. Traversed both new dependency closures:
   neither reaches the original eventual-vanishing node. The unrelated pre-existing cycle
   reported above does not invalidate this reduction.

Second reading changed only the redundant ConcreteCategory.Basic proof import and the
report's complete pruning inventory; the checked proof and new statements were retained.
