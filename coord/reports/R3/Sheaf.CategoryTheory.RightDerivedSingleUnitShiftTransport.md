## What changed

Proved `CategoryTheory.Functor.rightDerivedPlusSingleUnit_shift_transport` with its original
statement and original public import unchanged. Added proof-only imports of
`Sheaf.CategoryTheory.SingleQuotientInverseShift` and
`Sheaf.CategoryTheory.MappedSingleInverseShift`, each containing a complete proof.
The target comparison follows by faithful inclusion and cancellation of the lifted shift
comparisons. The source comparison reduces, through the quotient shift compatibility, to a
cochain-map equation supplied by the upstream mapped-single shift compatibility. The original theorem combines them with unit naturality,
the unit CommShift equation, and homology shift naturality.

All three delivered modules compile without warnings through lcompile.py. A probe against the
sandbox compiled modules shows that all three public theorems use only `propext`,
`Classical.choice`, and `Quot.sound`. No signatures, definitions, existing visibility, or target
statements changed. The original statement contains an unused `GS` let-binding; a declaration-local
unusedVariables linter option preserves that statement verbatim while avoiding its warning.

## Proved and sorry left

Closed the single original hole:
`CategoryTheory.Functor.rightDerivedPlusSingleUnit_shift_transport`
(node `lem-pc-right-derived-single-unit-shift-transport`).

Also proved the new supporting declarations
`CategoryTheory.Functor.single_quotient_inverse_shift`
(node `lem-pc-single-quotient-inverse-shift`) and
`CategoryTheory.Functor.mapped_single_inverse_shift`
(node `lem-pc-mapped-single-inverse-shift`). The generic inverse-lift private helper in each new
module is also proved. Second reading adds a proof-only import of
`WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors` to reuse its
proved forward-shift compatibility instead of repeating the coefficient calculation. No sorry remains in any delivered module, and no hole was added or split off.

## No longer needed

None: no original import, node, or module is removed. The original public import is required for
`rightDerivedPlusSingleUnit`. The degree-zero classical augmentation comparison theorem in that
module is not used, but its defining module remains necessary. No cycles projection, injective
resolution augmentation computation, or classical derived-functor comparison is needed for this
transport equation. The unit route is retained; its realized statement and step lists are unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan is mathematically correct, but its source and target coherence calculations
were not available as named bounded-below equations. They are now stated and fully proved.
At second reading, the upstream mapped-single forward-shift compatibility was found and reused
by cancellation in place of repeating its componentwise proof. No disputed statement or forced adaptation was needed.

Searches used LeanFinder, Loogle, Mathlib/source-library ripgrep, and the whole blueprint search.
LeanSearch returned an Internal Server Error for both new statements; the node records report it
as unavailable. The other searches found the constituent isomorphisms, whose definitions and
component formulas supply the proofs. Boundary cases n=0, the zero object, and an additive
non-exact G require no special exclusions: the same cancellation laws and the upstream compatibility theorem prove them.

## New nodes

`lem-pc-single-quotient-inverse-shift` records the proved compatibility of the canonical
single/quotient comparison with the inverse single shift. Its module is
`Sheaf.CategoryTheory.SingleQuotientInverseShift`; it requires no enough-injectives assumption.

`lem-pc-mapped-single-inverse-shift` records the proved compatibility of the mapped-single
comparison with the inverse single shift. Its module is
`Sheaf.CategoryTheory.MappedSingleInverseShift`; it requires only additivity of G and a chosen
derived category on C, with no exactness, enough-injectives, or derived-category assumption on B.

Both nodes realize smaller coherence calculations in step 1 of the original plan. Both are
already proved, so they add no new proof work. There are no change records.


## Second reading by R3

1. **Interface comparison: pass.** Read the repository and delivered modules and diffed
   RightDerivedSingleUnitShiftTransport. Its theorem signature, including all seven let-bindings,
   is byte-for-byte identical (checked directly). The original public import and visibility are
   unchanged. The only imports added to that module are proof-only. Neither new module changes
   an existing declaration, definition, or target, and no change record is needed.
2. **Proof and axioms: pass.** Compiled all three modules in import order with lcompile.py.
   Read both private inverse-lift proofs and all three public proofs. There is no sorry,
   axiom, unsafe, opaque, extern, or implemented_by in the delivered Lean. A scratch copy of
   the main module with #print axioms for each public theorem reports exactly propext,
   Classical.choice, and Quot.sound, with no sorryAx. No data is chosen from an open theorem.
   The delivery dry run additionally probes every declaration, including private helpers.
3. **Supporting statements: pass.** No statement is split off with sorry. The two proved new
   statements are genuine smaller source/target coherence equations, without the derived unit
   or homology conclusion of the item. Checked their category, additivity, and derived-category
   hypotheses against their Lean signatures: the quotient lemma needs only B's derived category;
   the mapped lemma needs only C's derived category and additivity, not exactness or enough
   injectives. At n=0 the cancellations still apply to the shift-zero isomorphisms; for X=0
   the same morphism identities apply. Read SingleFunctorsLift.lean lines 36–99, the ambient
   derived single/quotient definitions in DerivedCategory/Basic.lean, and the upstream
   HomotopyCategory/SingleFunctors.lean lines 29–44. The latter proves the coefficient equation
   for every additive G, including a non-exact G. Independent rg searches for single/shift
   comparisons in lean/ and Mathlib, plus a Loogle search for map_lift_shiftIso_hom_app,
   found constituent equations but no duplicate of either bounded-below statement.
4. **Route and pruning: pass after simplification.** The main proof transports the unit using
   U.naturality h and NatTrans.shift_app_comm, applies H^n, and ends with homology-shift
   naturality. It uses no augmentation comparison theorem or cycles projection. Found the
   existing upstream mapHomologicalComplex_map_singleFunctors_shiftIso_hom_app and replaced
   the mapped lemma's componentwise reproof with this theorem and cancellation, adding only
   a proof import. All imports are needed by signatures or these proofs. Both old proof_deps
   remain: the abstract derived category and the module defining rightDerivedPlusSingleUnit.
   Thus no old dependency is omitted from No longer needed. Read sk-thm-picard-rr.json:
   realized.statement and realized.steps are unchanged, and these smaller coherence proofs
   do not replace a unit statement or step.
5. **DAG agreement: pass after documentation repair.** The item node retains its statement,
   stmt_deps, source, unit and chapter. Its proof_deps is exactly the union of the proof steps'
   uses and retains both original dependencies while adding the two proved coherence nodes.
   The first step gives the derived-level square; the second applies homology naturality,
   matching hd and the final congrArg in Lean. Both new node lean.statement records match
   the corresponding theorem text and have source, search, creation, blueprint, chapter and
   unit records. Updated the mapped node's final step and proof_origin to record reuse of the
   upstream theorem. Corrected the quotient lemma's docstring to describe its actual first
   reduction e_i.inv = identity, followed by the lifted-shift cancellation.

Second reading changed the mapped coherence proof to reuse the upstream theorem, its proof-only
import, both supporting docstrings, the mapped node's proof narrative, and this report. No
signature, definition, hole count, or unit route changed. One original hole closed; zero added.
