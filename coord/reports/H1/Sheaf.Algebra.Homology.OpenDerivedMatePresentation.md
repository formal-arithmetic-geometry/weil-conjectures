## What changed

Proved `CategoryTheory.Adjunction.derivedPresentation_mate` in
`Sheaf.Algebra.Homology.OpenDerivedMatePresentation`, with its signature unchanged.
Added two fully proved private helpers, `derivedPresentation_unit` and
`derivedComparison_fac`. The first transports the chosen adjunction unit through
`derivedPresentation`; the second compares the composite derived restriction with
its termwise model. The main proof applies `d2.homEquiv` injectivity to the mate
identity, uses complex extensionality for the degreewise hypothesis, and finishes
with naturality and cancellation of factorization isomorphisms.

Updated the existing node `lem-sc-localization-nested-adjunction-mate` proof and
proof origin to describe this calculation. Its proof dependencies are unchanged.
No imports, public signatures, definitions, or other modules changed. The unit
route is preserved; this item is not itself a realized unit statement or step.

## Proved and sorry left

Closed one hole: `CategoryTheory.Adjunction.derivedPresentation_mate`
(node `lem-sc-localization-nested-adjunction-mate`). Added zero holes.
No `sorry` remains in the delivered module, including the two private helpers.
The existing `onDerivedCategory`, `derivedPresentation`, and
`derivedPresentation_counit` remain unchanged.

Validation: the complete module compiles through `lcompile.py` without warnings.
The first worker's delivery dry run printed OK, including the declaration axiom
probe and preflight. Independent checks are recorded below.

## No longer needed

None. No imports were added or removed, and no dependency node or module is
pruned. The existing exact-functor factorization dependency is used.
The counit calculation mentioned by the old proof plan is unnecessary for this
proof: transporting units and applying the adjunction hom equivalence suffices.

## Where the brief, the DAG or earlier work was wrong

No statement error or tool failure found. The DAG plan can be implemented
entirely with existing proved library identities, without new unproved nodes.
Its localization step is made precise with the two private helpers; the proof
handles the arbitrary chosen derived adjoints and representative isomorphism
directly rather than first restricting to the localized adjoints and `E = Q K`.

## Second reading by H1

1. **Interface: pass.** Compared the only delivered Lean module with the repository
   using `diff -u`. Every existing declaration signature is byte for byte unchanged;
   `onDerivedCategory`, `derivedPresentation`, and `derivedPresentation_counit` are
   unchanged in full. The only additions are two proved private helpers and the
   replacement of the mate theorem's `sorry`. No public interface or definition
   changed, so no change record or forced adaptation is needed.
2. **Proof and axioms: pass.** Independently compiled the module with `lcompile.py`,
   without errors or warnings. Searched for forbidden declarations and proof escapes;
   none occur, and no `sorry` remains. Compiled a scratch copy with `#print axioms`
   for all four existing declarations and both private helpers: each uses exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. Read the
   degreewise transpose calculation, unit transport, comparison factorization,
   naturality rewrites, and cancellation of invertible morphisms. These prove the
   stated equation for arbitrary chosen adjunctions and representative isomorphism.
   No data is selected from an unproved existence theorem.
3. **Split-off statements: pass (none).** Zero new holes and zero new public
   statements. The two private helpers are fully proved identities, strictly parts
   of the calculation. Their orientations agree with the localization-unit and
   composition-factorization formulas. For identity comparisons and identity
   adjunctions the calculation reduces to identity morphisms; for the zero complex
   it is an equality of zero morphisms. No extra small-case hypotheses are needed.
4. **Shortest route, imports, and unit: pass.** Repeated a Lean Finder search using
   “transport adjunction unit along unique left adjoint isomorphism and localization
   factorization”; it returned the existing localization formulas used here, rather
   than a theorem that closes this mate identity. Searched the library by
   `derivedPresentation`, composition/natural-isomorphism factorization names, and
   localization/mate terminology. Read the upstream `MapDerivedCategoryMate`
   candidates: they require additional resolution/monoidal assumptions and a
   natural isomorphism mate, unlike this arbitrary complex morphism. The direct
   hom-equivalence proof avoids those requirements. All three public imports are
   needed by existing definitions or signatures: termwise adjunction/localization,
   derived composition/comparison, and `leftAdjointUniq`. The sole old proof
   dependency remains used, so `No longer needed: None` is complete. Checked
   `dag/units/sk-thm-picard-duality.json` and searched all unit records: this node
   is not a realized statement or step, and no realized route is changed.
5. **DAG agreement: pass.** Compared the delivered node with the repository.
   Only `proof` and `proof_origin` change; its statement, Lean statement record,
   and proof dependencies remain unchanged. The three steps describe `hK`, the
   two private transport identities, and the final hom-equivalence/cancellation
   argument. Their dependency union is exactly the existing exact-functor
   factorization node. There are no new nodes to validate.

Second reading changed only this report: completed the independent review record
and replaced its stale “second reading pending” validation text. No Lean or DAG
repair was needed. Net holes closed minus added in this delivery: 1 - 0 = 1.
