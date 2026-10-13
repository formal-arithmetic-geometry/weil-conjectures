## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.sectionCohomologyPresheaf_pow_lifts` with a complete
Lean reduction. The statement and existing public imports are unchanged. Added the
proof-only import `Sheaf.AlgebraicGeometry.SectionCohomologyUnitComparisons`.

The proof constructs the qcqs inverse-image scheme, applies the already-proved
`invertS_cohomology` to its tensor unit, transports its canonical generator equation,
and uses quotient/direct-sum induction to prove denominator lifting for every class.
For two classes with exponents n,m and numerators y,y′, the proof supplies exponent
n+m and numerator a^m y+a^n y′. Surjectivity of the composite additive equivalence
then finishes. The proof does not normalize a fraction to one generator.

Added `Sheaf.AlgebraicGeometry.SectionCohomologyUnitComparisons`, containing the one
remaining comparison theorem. Updated the parent DAG proof and proof dependencies,
and supplied a complete node, source, proof in words and Mathlib search record for
the new theorem. Both Lean modules compile together with `lcompile.py --all`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.sectionCohomologyPresheaf_pow_lifts`
(node `lem-pc-section-cohomology-principal-denominators`). No sorry remains in the
item's module. This is a decomposition, not an unconditional proof: one upper hole
closed and one lower hole added, net zero before the project ledger's closure audit.

The sole new sorry is
`AlgebraicGeometry.Scheme.Modules.sectionCohomology_unit_comparisons`
(node `lem-pc-section-cohomology-unit-comparisons`), in
`Sheaf.AlgebraicGeometry.SectionCohomologyUnitComparisons`. Its whole proof is
`:= by sorry`. It identifies derived sections with raw section cohomology and records
compatibility with tensor-unit scalar powers and restriction. It contains no
localization, denominator lifting, quotient representatives, or compactness argument;
it even omits quasi-coherence, affineness and qcqs hypotheses. It is strictly the
comparison step of the argument, not the original statement renamed.

Edge cases checked mathematically: the comparison holds for arbitrary W and any F;
when a=0 the nonvanishing open and raw target complex are empty; when a is invertible
they identify with the whole inverse-image open; n=0 uses the right unitor and scalar
1. Empty W, zero coefficients and q=0 use the same resolution comparisons. The main
proof's zero and sum branches work uniformly in all of these cases.

## No longer needed

No existing imports, nodes or modules were removed. `InvertSCOhomology` is used, and
all four existing public imports are needed for the unchanged statement. The new
module's public imports provide only its statement's notions.

Pruned the planned single-fraction normalization and its common-degree transition
calculation: quotient induction plus additive direct-sum induction prove exactly the
existential denominator property needed. No additional module or node for fraction
normal forms, transition identities or a common numerator is required. This does not
prune `CohomologyFractionPresentation` itself or any dependency of `invertS_cohomology`.
The unit record has empty realized lists, and no unit statement or step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The original DAG treated simultaneous restriction/scalar-compatible identification
of raw section cohomology with derived sections as a step without a matching Lean
interface. `FlatBaseChangeOpenChoices` defines raw cohomology and restricted-resolution
data but does not assert that comparison. `OpenRestrictionModuleCohomology` proves a
coefficient-natural restriction equivalence, and `ResolutionSectionsHomologyScalar`
states scalar transport for a specified resolution. Neither alone supplies the two
simultaneous compatibility equations needed here; the new comparison node isolates
the remaining glue and its tensor-unit specialization.

No mathematical error in the original statement was found. The common-degree
normalization in its proof plan is unnecessary for denominator existence.

Process note: I briefly wrote scratch copies under /tmp and issued one read-only
`git show`, contrary to the sandbox-only/no-git brief. No repository file was edited
by those operations. The delivery files themselves are all in the assigned sandbox.

## New nodes

`lem-pc-section-cohomology-unit-comparisons`:
`dag/nodes/sec-picard-framework/lem-pc-section-cohomology-unit-comparisons.json`,
with Lean module `Sheaf.AlgebraicGeometry.SectionCohomologyUnitComparisons`.
The source is Stacks Tags 01E1 and 01E4, specifically restriction of injective
resolutions and evaluation of the section complex. Its docstring explains the
construction of the three families of additive equivalences and both commuting
squares, including tensor-unit powers and scalar transport.

Not duplicates: the new node shares 01E4 with the parent denominator node and with
`lem-pc-resolution-sections-homology-scalar`, and 01E1 with
`lem-pc-open-restriction-module-cohomology` and
`lem-weil-pbc-module-open-restriction-injectives`. The parent asserts existence of
power denominators; this node only compares cohomology models. The scalar node
compares a specified restricted resolution's homology with raw homology, but neither
identifies the derived cohomology groups nor supplies their restriction square or
tensor-unit powers. The restriction node is natural in coefficients, but says
nothing about the raw section presheaf, scalar action or the second open. The
injective-restriction node supplies exactness and injectivity, not these homology
comparisons. These existing results are retained as proof dependencies of the new
node. No change record or forced adaptation is needed.


## Second reading by T2

1. Compared the sole existing delivered module with the repository using diff and
   a byte comparison of the entire theorem signature. Verdict: unchanged signature,
   unchanged definitions and public imports; the added comparison import is proof-only.
   The existing node changes only proof, proof_deps and proof_origin. No change record
   or forced adaptation is required.
2. Compiled both modules in import order with lcompile.py. Inspected all proof bodies:
   no forbidden declaration or hollow definition; the only direct sorry is the named
   sectionCohomology_unit_comparisons theorem, as reported. The quotient induction
   descends an existential property of the image, and the direct-sum addition branch
   correctly uses exponent n+m and numerator a^m*y+a^n*y'. No unproved existence
   theorem is used to define data: the equivalences are eliminated inside a proof.
   Both #print axioms checks allow only propext, Classical.choice, Quot.sound and
   sorryAx. This remains one upper hole closed and one lower hole added, a decomposition.
3. Read the comparison statement and its complete docstring proof, its node, and the
   definitions of raw and open cohomology. Checked Stacks 01E1 and 01E4 directly:
   restriction preserves injectives, and the section-complex identification computes
   cohomology. Canonical tensor-unit identifications turn the tensor-section map into
   multiplication by b^n; resolution naturality and exact presheaf evaluation give
   both displayed equations. Empty opens, zero modules, n=0, q=0, a=0 and invertible a
   impose no missing hypotheses. The comparison contains no denominator existence
   claim and is strictly a part of the parent argument. Independent leanfinder search
   for resolution computation compatible with restriction of scalars and unit
   isomorphisms returned generic resolution lemmas. Loogle on NatTrans.rightDerived
   found InjectiveResolution.rightDerived_app_eq; grep confirmed it and
   isoRightDerivedObj_hom_naturality. Read OpenRestrictionModuleCohomology,
   ResolutionSectionsHomologyScalar, HigherDirectImageCoefficientComparison and the
   upstream DirectImage/Sections module: none states the simultaneous two-open,
   tensor-power and scalar comparison. Generic tools help prove this remaining hole
   but do not close it directly in a few minutes. Verdict: true, needed, not a duplicate.
4. Read the old dependency plan, InvertSCOhomology and the fraction presentation.
   All old proof_deps remain used. The additive induction avoids single-fraction
   normalization without bypassing any unit step. The unit sk-thm-picard-coherence
   has empty realized statement and step lists; its route and record are unchanged.
   No existing module or node is pruned. Imports of the delivered code are confined
   to statement notions and the two actual proof inputs. Planned comparison lemmas
   remain named in its DAG; they are not newly imported for its sorry body. An attempted
   import of ResolutionSectionsHomologyScalar was unavailable in the published
   compiled snapshot and was removed; no duplicate was created to work around it.
5. Checked both node files against Lean, including verbatim lean.statement fields,
   source, creation, blueprint, chapter/unit, searches, and the union of step uses.
   The parent records its qcqs reduction, comparison, and additive induction; the
   new node records only the remaining comparison plan. Verdict: DAG and code agree.

Changed only the new comparison docstring: specified that exact evaluation means
presheaf evaluation together with scalar forgetting, rather than sections as a
functor on sheaves. No proof, signature, dependency, or pruning change was needed.
Sources checked: https://stacks.math.columbia.edu/tag/01E1 and
https://stacks.math.columbia.edu/tag/01E4.
