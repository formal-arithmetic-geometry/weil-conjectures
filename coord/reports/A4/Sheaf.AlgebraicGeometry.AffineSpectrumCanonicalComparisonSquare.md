## What changed

Reduced `AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_canonicalComparison_square`
to the ordinary tensor comparison square, in the new module
`Sheaf.AlgebraicGeometry.AffineSpectrumOrdinaryComparisonSquare`, and the derived counit equation, in the new module
`Sheaf.AlgebraicGeometry.AffineSpectrumCounitSquare`. The original theorem's signature and all public
imports are unchanged. Added proof-only imports of these two modules.

Constructed `comparisonIntoTensorPullback` by the first three factors of the existing
comparison and `affineSpectrumTensorComplexIso` by the actual adjunction-mate composition
isomorphisms. Neither construction chooses data from an existence theorem.
The counit-square node specializes the existing representative-map theorem to an identity
chain map. The original module applies naturality and functoriality, composes this equation
with the ordinary square, and proves the original square by real Lean equality transitivity.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_canonicalComparison_square`
(node `lem-pc-affine-spectrum-canonical-comparison-square`).

Added two holes:
`AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_ordinaryComparison_square`
(node `lem-pc-affine-spectrum-ordinary-comparison-square`). This is a decomposition,
not a complete axiom-free proof: one upper hole is closed and two lower holes added.
The lower statement concerns ordinary pullback, contains neither inverse counit along
gprime nor its spectrum map, and makes no assertion involving
`affineSpectrumDerivedPullbackIso`. Its hypotheses do not require K-flatness or invertible
counits. The separate derived equation is the second hole,
`AlgebraicGeometry.SingleComplexBaseChange.affineSpectrum_counit_square`
(node `lem-pc-affine-spectrum-counit-square`). It contains no base-change square,
point, stalk cohomology or localized comparison. There are no other new holes, and no holes
in definitions.
The counit node plans to use the existing representative-map theorem, which has its own
recorded hole.

## No longer needed

All four original public imports are retained for the unchanged interface.
Removed the redundant direct `Mathlib.AlgebraicGeometry.AffineScheme` import from
the new ordinary-square module; it is already exported by the module-sheaf dependency.
No whole module is claimed pruned from the target import closure.
The following old proof dependencies are no longer direct dependencies of the
original node: `def-pc-affine-spectrum-derived-coordinates`,
`def-pc-base-derived-tensor-cohomology-model`,
`def-pc-single-complex-base-change-stalk-condition`,
`lem-pc-ringed-spaces-derived-pullback-composition`,
`lem-pc-stalk-comparison-source-transport`,
`lem-pc-stalk-derived-extension-comparison`, and
`lem-weil-pbc-module-stalk-pullback`. Their definitions remain in the signature or
in the two lower statements; this is no claim that their modules are unreachable.
The derived counit node packages the composition step; the ordinary-square node
packages the scalar-transport step. Their transitive dependencies remain needed.
In particular `comparisonIntoPullback_naturality` is not used: its module stays for the
comparison's definition, which the original signature requires.

## Where the brief, the DAG or earlier work was wrong

The existing source-transport and pullback-naturality statements compare two representatives
on the same scheme and square. They do not directly handle the changes of stalk rings
under isoSpec. That ring-coordinate part is the new ordinary-square item. The already stated `affineSpectrum_representative_map_eq` supplies the canonical derived
composition compatibility mathematically. Its specialization requires aligning
Scheme.Modules and SheafOfModules plus quotient localization factors. Attempts to write
that specialization exposed expensive type-conversion glue; it is left in the separate
counit node, whose proof in words specifies the existing theorem to use.

Initially even the unmodified item could not compile because the published cache lacked
`IsoPullbackStalkCohomology.olean`. The cache refreshed during this session and work resumed
without copying or rebuilding that dependency.

Checked the new statement on identity coordinate maps, zero complexes and zero rings;
all comparisons and coordinate transports specialize to the corresponding tensor
identities. An empty Xprime has no z0, so that case is vacuous. No boundedness,
quasi-coherence, Tor-independence, or invertibility of localizedComparison is used.
The unit's realized statement/step lists are empty and no unit route is bypassed.

## New nodes

`lem-pc-affine-spectrum-ordinary-comparison-square` states the ordinary part of steps 1--3
of the assigned node. Its module constructs the source comparison without the inverse
gprime counit and fixes the actual chain composition isomorphism. The proof plan identifies
stalk rings, transports base-derived scalar extension across their exact equivalences,
and identifies the ordinary target transport by the tensor-stalk germ formula.
Sources read online: Stacks Tags 0DJ8 (equation-bc and affine reduction), 0098
(stalks of module pullback), and 0D5S (composition of derived pullback).
Mathlib searches are recorded in searches.jsonl: LeanFinder, Loogle, grep, and the unavailable
LeanSearch service. Blueprint searches for affine spectrum counit, stalk pullback and
derived tensor found no duplicate of this coordinate-specific ordinary square.
`lem-pc-affine-spectrum-counit-square` is the derived part of step 3, independent of
all stalk data and of f and g. Its plan uses the existing representative-map theorem,
with identity chain map and the pinned counits, then categorical cancellation. Searches
for pullback composition and affine reduction found no matching imported blueprint node.
No change record is needed; no existing interface changes.


## Second reading by A4

1. Compared the complete existing module with the repository by `diff` and extracted
   the original theorem signature through `:= by`: byte-for-byte identical. Its
   docstring and four public imports are unchanged. The only existing proof hole is
   replaced by the equality reduction. Neither new definition chooses a witness:
   `comparisonIntoTensorPullback` is the explicit first three comparison factors;
   `affineSpectrumTensorComplexIso` is the explicit composition of adjunction mates.
   No existing definition or statement changes, so no change record is required.
2. Compiled all three submitted files locally without errors or warnings. Read the
   main proof: substitution eliminates equality transport; `hl` gives the ordinary
   square, `hcH` is the functorial image of the counit square, and `hn` is naturality
   of the explicitly constructed stalk isomorphism. Their orientations agree in
   `hL.trans (hC.symm.trans hN.symm)`. The sole private helper unfolds the existing
   comparison definition. The two new named theorems are the only new `sorry`s;
   neither definition contains one. No axiom, unsafe declaration, opaque declaration,
   implementation override, or external implementation occurs. Axiom checks permit
   only the three standard axioms and inherited/named `sorryAx`; this is a
   decomposition, not an axiom-free proof of the original result.
3. Read Stacks 0DJ8 (affine reduction and the localized tensor comparison), 0098
   (stalk pullback formula), and 0D5S (composition of derived pullbacks). The ordinary
   square requires only the exact coordinate equivalences, not the quasi-coherence
   hypothesis of the larger 0DJ8 equivalence. Its comparison ends at ordinary
   pullback, and requires neither K-flatness nor inverse counits. The counit square
   uses hP and the two stated invertibility assumptions, has no cartesian square,
   point or stalk comparison, and is the identity-map specialization of
   `affineSpectrum_representative_map_eq`. The explicit chain mate agrees with that
   theorem's `a`. Both statements are strictly smaller than the original. In the
   zero complex both squares are equalities of zero maps; for identity gprime the
   counit square is the composition unit law; zero rings force the relevant empty
   spectra, and an empty Xprime has no z0. Unbounded complexes and arbitrary degree
   introduce no extra hypotheses. Read both complete docstring proofs and their
   node plans. Searched LeanFinder for derived counit composition, Loogle for map
   inverse, Mathlib grep for counit composition, and the Sheaf/upstream sources for
   isoSpec and comparison transport. The existing representative-map theorem is
   the appropriate derived ingredient; no existing declaration states the ordinary
   coordinate square. A bounded attempt to specialize it in Lean hit the file
   compilation limit on module-category conversions, so retained the honest named
   counit hole with that theorem imported only for its planned proof.
4. Read source transport and pullback naturality: both fix the stalk rings, so they
   do not directly replace the ordinary coordinate square. Retained the first
   worker's reduction and explicit constructions. Removed the redundant direct
   AffineScheme import from the new module and the unused local H from the proof.
   Expanded No longer needed to name all seven removed old direct proof dependencies;
   none is claimed pruned transitively. Read `dag/units/sk-thm-picard-semicon.json`:
   realized.statement is empty and realized.steps is `[[]]`; no realized unit node
   is bypassed or edited.
5. Checked each node's proof steps, uses union, proof_origin and verbatim Lean
   statement. The original node records the ordinary/counit/naturality reduction;
   the ordinary node records exact stalk ring and tensor transport, with the
   specified model equations and composition mate; the counit node records the
   existing representative-map specialization and cancellation. New nodes have
   source, statement dependencies, search records, creation, blueprint and Lean
   fields. Repaired doubled TeX escapes in both new natural-language statements.

Changes in this reading: corrected the two node statements' TeX escaping; imported
AffineSpectrumRepresentativeMap privately for the counit proof plan; removed the
redundant new AffineScheme import and unused local H; used the standard mapsto
notation in proof lambdas; completed the pruning report. Existing signatures and
the mathematical decomposition are unchanged. Holes closed: one; holes added: two;
net minus one, with no whole module pruned.


Final verification: deliver3.py --no-push returned OK with review class CODEX.
Explicit #print axioms on all five public declarations showed only propext,
Classical.choice and Quot.sound for the two constructed definitions; the original
result and the two lower theorems additionally depend on sorryAx, as reported.
The scratch axiom-print file is outside the delivery. All three delivered modules
compiled without warnings in the successful dry run.
