## What changed

The returned version failed the singleton zero-leg counterexample: hA_map followed
from functoriality, hκ_desc was reflexive, and hcA_ι merely named the cocone legs.
This delivery replaces that false interface. Both intermediate
interfaces have now been redesigned: they fix a qcqs descended finite covering,
construct all tail families by actual pullback, identify the nerves by their
projection equations, prescribe γ/δ by their first-projection equations over the
fixed bases, and prescribe every A.map and cA.ι component by the actual adjunction
units, coefficient transitions and L.ι. The item passes all these witnesses and
equations in a complete Lean proof, keeping its original signature.

Validation: all three delivered modules compile without warnings with lcompile.py.
The item signature is byte-for-byte identical to the library signature. Its direct
importer, EtaleLimitInjectiveColimitAcyclic, compiles unchanged against the repaired
modules. The three edited nodes have no dependency cycle, and each proof_deps list
equals the exact union of the proof-step citations. A separate Lean check in
`checks/CanonicalZeroLeg.lean` proves that invertible identifications cannot
turn a zero leg into the identity on the integer group; it compiles and is
validation only, not a delivered module. In the full singleton test the unit
for the identity base map, the singleton product projections and all nerve
comparisons are isomorphisms, so the prescribed right-hand section map is
nonzero even before choosing identity coordinates. A zero leg makes the
left-hand map zero and fails the final equation.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.etale_limit_finite_cech_complex_colimit`
(node `lem-weil-pbc-etale-limit-finite-cech-complex-colimit`).

Two holes are added, each the whole proof of a named public theorem:
`AlgebraicGeometry.Etale.exists_etale_limit_finite_cech_stage_data`
(node `lem-weil-pbc-etale-limit-finite-cech-stage-data`), for finite-cover descent
and canonical complex/cocone construction;
`AlgebraicGeometry.Etale.finite_cech_stage_data_is_colimit`
(node `lem-weil-pbc-etale-limit-finite-cech-colimit`), for section continuity,
finite products and the degreewise universal property.
This is a decomposition, not a completed proof from sorry-free dependencies.
One upper hole is closed and two lower holes are added; no positive net hole
reduction is claimed. No data definition uses an unproved existence theorem.

## No longer needed

The item removes these original proof imports and uses only the two intermediate modules:
`WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit`,
`Sheaf.AlgebraicGeometry.EtaleInverseLimitDescent`,
`Sheaf.AlgebraicGeometry.DescendSurjective`,
`Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`,
`Sheaf.CategoryTheory.ColimitSiteCechComplex`,
`Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`,
`Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`, and
`Sheaf.CategoryTheory.ColimitSiteSections`.
The old direct proof dependencies removed from the item node are:
`thm-pd-spreading-out`, `lem-weil-pbc-descend-etale`,
`lem-weil-pbc-descend-surjective`, `lem-weil-pbc-scheme-over-limit`,
`lem-weil-pbc-affine-etale-site-colimit`, `lem-weil-pbc-affine-etale-site-topos`,
`lem-weil-pbc-colimit-of-sites-sections`,
`lem-weil-pbc-colimit-of-sites-cech-complex`, and
`lem-weil-pbc-filtered-colimits-commute-finite-limits`.
Their mathematical inputs remain needed below the intermediate statements, except
`Sheaf.CategoryTheory.ColimitSiteCechComplex` and node
`lem-weil-pbc-colimit-of-sites-cech-complex`: the construction is directly by the displayed adjunction-unit and product
formulas, and the universal-property argument uses section continuity and
degreewise products directly. The colimit
module does not need stage-data existence as a proof dependency. The stage-data
node no longer cites the item's theorem. No unit-level route is bypassed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: The returned colimit interface is false for the singleton
nonzero constant diagram with zero legs. The returned equations did not rule out that data; they have been removed,
including κ and its reflexive equation. The corrected interface does exclude it:
its last equation has the actual unit, eG inverse and L.ι on the right, and has
cA.ι on the left. With identity coefficient/colimit comparisons its degree-zero
right side is the nonzero identity, whereas a zero leg makes its left side zero.
The stage-data dependency on the item also caused a DAG cycle. Its replacement
plan cites descent, base change and canonical cocone construction; the colimit
plan cites section continuity and finite-product colimits, never stage-data existence.

## New nodes

`lem-weil-pbc-etale-limit-finite-cech-stage-data`: existence of the fixed descended
family and canonical nerve/complex/cocone data, with all equations in the Lean
signature and a self-contained mathematical statement. Its proof plan spells out
descent, covering preservation, nerve identification and canonical maps.

`lem-weil-pbc-etale-limit-finite-cech-colimit`: universal property for precisely
that canonical comparison cocone. The self-contained statement defines all
parameters and every map equation; the proof plan uses section continuity,
finite-product commutation, and the degreewise complex universal property.

Both proof_deps lists equal the exact unions of their proof-step uses. Their
stmt_deps contain definition nodes rather than the item's theorem. Both modules
have complete source-specific proof docstrings. The existing item node records
only the two intermediate results that its Lean proof actually combines.

Change record: `coord/changes/etale_limit_finite_cech_complex_colimit.md`.
The old and new sections contain the verbatim prior signatures and exact corrected
signatures, including every equation. The effects on both intermediate modules,
the item and its direct importer are listed in its Users table.

The previous second reading is removed because it endorsed false equations.
The independent second reader must recheck each equation: eU/eV identifies the
covering; eNj/eNlim preserves nerve projections; γ/δ is uniquely determined over
the fixed base by its first projection; the all-arrow transition equation
prescribes the unit followed by φ; and the leg equation prescribes the unit
followed by eG inverse and L.ι. In the singleton example the first four conditions
hold for the canonical identity data, but the zero leg fails the last condition.

The newer generic cocone-construction module is present in source but absent from
the last green compiled snapshot. It is not imported or duplicated; the stage-data
statement records the direct construction on actual pullbacks instead.


## Second reading by V1

1. **Interfaces: PASS.** Compared every delivered module with the read-only
   repository. Only the item exists there; its theorem signature is byte-for-byte
   unchanged, as are its public imports and visibility. The two intermediate
   modules are new relative to the repository. Their rejected predecessor
   interfaces and the replacement signatures are documented in the change record.
   No definition or target statement changes. No forced adaptation is delivered.
2. **Proof and axioms: PASS as a decomposition.** All three modules compile through
   lcompile.py, in dependency order, without errors or unexpected warnings.
   Scratch copies with `#print axioms` confirm only propext, Classical.choice,
   Quot.sound and sorryAx. The item contains no sorry; each intermediate has
   exactly its reported named theorem with `:= by sorry`. No forbidden declaration
   or data definition occurs. The upper proof passes exactly the witnesses from
   construction to the universal-property theorem and extracts the covering clause.
3. **Split statements: PASS.** Read every quantified witness and equation. The
   descended covering uses actual pullbacks; the nerve comparisons preserve every
   projection. The first-projection equations for γ and δ, together with being
   arrows over the new base, determine the pullback-pasting maps. The final two
   equations prescribe every tuple component of transitions and legs using the
   actual adjunction units, φ, eG inverse and L.ι. Thus the universal-property
   theorem concerns the canonical cocone. Singleton constant nonzero coefficients
   exclude zero legs; the existing CanonicalZeroLeg scratch check compiles.
   Empty K gives zero degree objects, and zero coefficients cause no exception.
   Finite products over the qcqs descended family are qcqs, so section continuity
   applies. Construction does not assert a colimit, and the colimit theorem assumes
   supplied construction data: each is strictly part of the argument, rather than
   a renamed copy of the item. Their proof docstrings describe complete arguments.
   Independently searched LeanFinder for filtered-colimit étale section continuity,
   Loogle for isColimitOfPreserves, and rg for Čech colimits and section continuity
   in Mathlib, upstream and Sheaf. Upstream SectionContinuity handles a fixed
   coefficient sheaf and remains sorry; it does not close the varying-coefficient
   theorem. The generic site Čech construction requires different site data and
   comparisons, so is not an immediate application or duplicate of these statements.
   Neither remaining hole can be closed in a few minutes by the available results.
4. **Route and pruning: PASS after report repair.** Reviewed from the item down.
   The public imports provide signature notions; added proof dependencies use plain
   import. The intermediate imports retain their documented mathematical inputs.
   Listed every removed old direct proof dependency explicitly above. Only the
   generic site Čech complex route is no longer mathematically needed; the other
   inputs move below the new statements. The sk-thm-p1 realized statement and steps
   remain intact; none is bypassed. This closes one upper hole and adds two lower
   holes, net minus one, with no positive proof-progress claim.
5. **DAG: PASS.** All three proof_deps lists equal the unions of their proof-step
   citations. The item cites just the two statements its proof combines. The new
   nodes have sources, searches, creation and blueprint provenance, statement
   dependencies, unit/chapter and exact Lean signatures. Neither cites the item as
   a proof dependency, so the rejected dependency cycle is gone. The existing node
   changes only proof, proof_deps and proof_origin.

Second reading changed report wording to distinguish rejected equations from the
replacement, completed the explicit list of removed dependency nodes, and recorded
this independent review. No Lean proof or statement repair was needed.
Sources were checked directly against
[09YP](https://stacks.math.columbia.edu/tag/09YP),
[09YN](https://stacks.math.columbia.edu/tag/09YN), and
[09YQ](https://stacks.math.columbia.edu/tag/09YQ): the displayed Čech-complex colimit,
varying-coefficient section continuity and qcqs scheme realization agree with the
mathematical route of the split. The cited local Stacks source files are absent on
this machine, so the primary online text was used for this check.
