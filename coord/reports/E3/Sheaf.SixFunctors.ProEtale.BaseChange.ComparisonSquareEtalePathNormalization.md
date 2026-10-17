## What changed

Proved `AlgebraicGeometry.ProEtale.comparisonSquareEtalePath_normalization` with its
original statement unchanged. Added the proof-only import
`Sheaf.Paper.DerivedSquarePasting` and private, proved helpers for exact path pasting,
endpoint naturality, bounded-below restriction, and the derived edge comparisons.
The explicit private path constructors preserve the public endpoint presentations.

The earlier candidate's concrete `square_restrict` proof exceeded the kernel's limit.
The new generic `restriction_path` proves the calculation for arbitrary exact functors.
Separate proved equations `etale_square_expansion` and `plus_square_expansion` identify
the two scheme-square constructions before evaluating their components. This avoids
repeated conversion of the bounded-below derived constructions. No definition or
public signature changed, and no consumer adaptation is needed.

Updated the existing node's proof route and proof dependency to record the use of
`lem-weil-pbc-derived-square-pasting` and the completed restriction calculation.
The unit's statement and route are preserved.

Change record: `coord/changes/E3-etale-path-proof-local-commands.md`. The delivery
scanner flags the added local attributes/options and closed helper-section variables;
the record documents their scope and the unchanged interfaces of downstream users.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.comparisonSquareEtalePath_normalization`
(node `stage3-proetale-comparison-square-etale-path-normalization`).

There are zero remaining holes in the item, zero holes added elsewhere, and zero
split-offs. Every private helper is proved. A complete single-file compile passed in
7.9 seconds with no warnings. `#print axioms` for the assigned theorem reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

None. No original import, DAG node, module, or unit step is pruned. The proof uses
neither underived square coherence nor pro-etale path normalization. The unused
private `plus_comp` candidate from the inherited sandbox was removed.

## Where the brief, the DAG or earlier work was wrong

The original DAG's first calculation can use the existing proved
`CategoryTheory.Functor.mapDerivedCategorySquareIso_paste`; its node is now an explicit
proof dependency. No statement error was found.

The previous sandbox report's missing-import obstruction no longer prevents local
compilation. Its proof candidate was not kernel-verified: the concrete square
restriction needed the generic argument and separate expansion equations described
above. The complete assigned theorem now compiles and passes its axiom check.

## Second reading by E3

1. **Visible declarations: PASS.** Compared the complete delivered module with the
   shared repository using `diff -u`. The only existing declaration is
   `AlgebraicGeometry.ProEtale.comparisonSquareEtalePath_normalization`; a separate
   byte comparison confirms its entire signature is unchanged and equals the node's
   `lean.statement`. All added declarations are private. The sole added import,
   `Sheaf.Paper.DerivedSquarePasting`, is proof-only. Read the change record: its
   local irreducibility attributes, file options, and closed section variables do
   not change any exported statement or construction. No downstream adaptation.
2. **Proof and constructions: PASS.** Independently compiled the delivered module
   through `lcompile.py`: exit 0, 9.2 seconds, no warnings. Compiled a scratch copy
   with `#print axioms AlgebraicGeometry.ProEtale.comparisonSquareEtalePath_normalization`:
   exactly `propext`, `Classical.choice`, `Quot.sound` (8.3 seconds). Scanned all
   delivered Lean for forbidden declarations and holes: none. Read every helper;
   the four private path definitions are concrete composites of specified
   isomorphisms, with no data chosen from an unproved existence claim. The final
   HEq is obtained from the proved ordinary equality, preserving the original
   endpoint presentations.
3. **Split statements: PASS, none.** No new sorry theorem or DAG node is added.
   Read the general pasting theorem and the exact-functor inclusion comparison
   lemmas actually used. Checked the helper calculations: `exact_path` pastes the
   two edge comparisons and inserts the etale square by right-whiskering naturality;
   `exact_path_with_comparisons` uses inverse-comparison naturality twice;
   `restriction_path` recovers the inverse component through equality of mapped
   isomorphisms. Equality induction proves the middle transport, and the separate
   scheme-square expansions are definitional identifications. Identity edges and
   zero input require no extra hypotheses or cancellation of arbitrary morphisms.
4. **Route and pruning: PASS.** Read `ComparisonSquarePaths`, `DerivedSquarePasting`,
   the blueprint transport lemma, and `dag/units/sk-thm-properbasechange.json` with
   its source `_section.md`. Searched the library using bounded-below inclusion,
   composition, whiskering, restriction, and square-pasting terms, including
   `ComparisonCounit` and the companion pro-etale normalization module. Existing
   infrastructure is used directly; no existing public theorem replaces this
   etale-path calculation. The original public import supplies its statement's
   constructions and the added private import supplies the pasting theorem.
   The old `proof_deps` was empty, so `No longer needed: None` is complete.
   No node realizing the unit's statement or steps is bypassed; `realized` stays
   unchanged. No underived square coherence or pro-etale normalization is assumed.
5. **DAG agreement: PASS.** Diffed the node JSON against the shared version. Only
   `proof`, `proof_deps`, and `proof_origin` change. The sole proof dependency,
   `lem-weil-pbc-derived-square-pasting`, names the theorem applied in `exact_path`.
   The other two steps accurately describe bounded-below restriction and the
   endpoint comparison calculation. The node's statement and Lean record remain
   unchanged; its source, chapter, and unit agree with the reviewed route.

Second-reading changes: added this independent review record only. No Lean or node
repair was needed. Confirmed one original hole closed, zero holes added, zero
split-offs, and no imports or modules pruned.
