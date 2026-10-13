## What changed

Proved `AlgebraicGeometry.scheme_derived_hom_restriction_transport` in
`Sheaf.AlgebraicGeometry.SchemeDerivedHomRestrictionTransport`, preserving its complete
signature and visibility. Added six fully proved private helpers for the comparison
components, pasting of derived squares, and transport of arbitrary morphisms.
The scheme theorem directly specializes this categorical calculation to `overEquiv`,
`overFunctorMap`, and `derivedOpenHomRestriction`. No imports, definitions, public
interfaces, or other modules changed. Updated the item's node proof and proof origin.

The generic calculation follows the factorization lemmas already proved in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` and
`Localization.natTrans_ext`. Search via Lean Finder, Loogle, and rg found these
factorization lemmas but no existing general pasted-square transport theorem.
The unit `sk-thm-picard-duality` has empty realized statement/steps for this node;
its route is preserved. The proof applies to the empty open and to W = U without
any case exclusions. The helper transport theorem needs only fullness, and creates
no new objects from unproved existence statements.

Validation: the complete module compiles cleanly via lcompile.py (23 seconds before
adding helper documentation); the delivery dry run also compiles and checks axioms.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.scheme_derived_hom_restriction_transport`
(node `lem-sc-scheme-derived-hom-restriction-transport`).

There are no remaining sorry declarations in the item and no added holes.
All six private helper lemmas have complete Lean proofs. This is a proof, not a
decomposition into new holed statements.

## No longer needed

No imports removed and no modules pruned. The Mayer–Vietoris exactness theorem
`AlgebraicGeometry.derived_hom_mayer_vietoris` is not used. Its module remains
transitively imported because it supplies `moduleRings` and
`derivedOpenHomRestriction` (the only content used from
`lem-sc-derived-hom-mayer-vietoris`). No dependence on the proof of exactness, the
Mayer–Vietoris triangle, or the extension-by-zero adjunction is introduced.
The original two proof-dependency nodes remain because their definitions occur
in the unchanged statement.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or interface error found. The DAG's coherence step was
not elementary, but is now explicitly proved by localization extensionality and
comparison-factorization formulas. Expanding the full scheme expression during
simplification hit its existing heartbeat budget; proving the same calculation
generically and directly specializing it avoids that expansion and compiles within
the per-file limit. No tool workaround or dependency/interface adaptation was needed.

## Second reading by V2

1. **Interface: pass.** Independently diffed the sole delivered Lean module against
   the repository version. The complete existing theorem signature is byte for byte
   identical, as are its docstring, imports, local instance setup, and options.
   Only six private proved helpers and the original theorem's proof are added.
   There are no changed definitions, public signatures, or change records.
2. **Proof and axioms: pass.** Independently compiled the delivered file through
   lcompile.py: clean, 25.0 seconds. Compiled a scratch copy with explicit
   `#print axioms` for all six private helpers and
   `AlgebraicGeometry.scheme_derived_hom_restriction_transport`: clean, 31.1 seconds.
   Each uses only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
   The delivered source contains no sorry, forbidden declaration, or kernel bypass.
   Read the localization extensionality argument, degreewise complex comparison,
   naturality rewrites, and inverse cancellations. The final specialization uses
   exactly the original unit and overFunctorMap comparisons.
3. **Split statements and edge cases: pass.** No statements are split off and no
   holes are added. The private helpers are proved generic identities, not holed
   restatements. Fullness supplies a preimage with its prescribed image; no object
   is chosen from an unproved mere-existence theorem. The general argument allows
   identity functors, identity comparisons, and zero morphisms. Its scheme
   specialization requires neither strict inclusion nor nonemptiness, so W = U
   and W empty are included without an extra hypothesis.
4. **Route and pruning: pass.** Read the upstream exact-functor factorization laws
   and the actual definition of derivedOpenHomRestriction. Repeated searches with
   different terms: Lean Finder for exact derived-functor associativity and
   localization comparisons; Loogle for Localization.natTrans_ext (not indexed);
   rg over upstream derived-category files and Sheaf categorical/homological files.
   The returned derived-functor composition results concern different constructions;
   no direct replacement for this pasted-square identity was found. Related Ext
   cocycle calculations do not state the required comparison. The only direct
   import, DerivedCategory, is public because schemeDerivedCategory occurs in the
   signature. Both old proof dependencies remain used: the derived-category
   definitions and the moduleRings/restriction definitions and exactness instances
   from DerivedHomMayerVietoris. Its Mayer–Vietoris exactness theorem is not used.
   Thus the No longer needed section is complete: no old dependency or import can
   be removed here. The unit's realized fields are empty statement and one empty
   step; this auxiliary coherence proof changes no unit route.
5. **DAG: pass.** Diffed the node JSON independently: only proof and proof_origin
   differ. Its four steps describe the component formulas, pasted-square coherence,
   morphism transport, and scheme specialization implemented in Lean. proof_deps
   equals the union of step uses and retains the two dependencies actually used.
   The statement, Lean signature record, chapter, unit, and blueprint are unchanged.
   There are no new nodes to check.

Second-reading changes: appended this independent review and verification evidence
only. No repair to the Lean proof or node metadata was needed. Confirmed holes
closed: scheme_derived_hom_restriction_transport (1); holes added: none (0).
