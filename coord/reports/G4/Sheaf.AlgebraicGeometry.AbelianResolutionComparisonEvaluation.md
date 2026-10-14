## What changed

Proved
`AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.abelian_resolution_comparison_evaluation`
from `acyclicComparison_naturality`. Exact forgetting makes the augmentation a
quasi-isomorphism; forgotten module injectives are section-acyclic, and the target's
injective terms are section-acyclic. Naturality for the identity coefficient map gives
the comparison equation. Cancel the inverse target comparison, compose the common
Ext-to-derived-sections prefix, and evaluate the resulting homomorphism equality at z.
The proof uses the existing proof-only import
`Sheaf.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural`. Relative to
the current repository, no import is added. Two redundant proof-only imports are
removed from the evaluation module: `ModuleCohomologyExtResolutionNormalization`
and `InjectiveModuleAbelianAcyclic`; the public cocycle import already supplies the
declarations and instances needed from them.

Repair A3 (reviewer X-15ff5, head 15ff5cacc): selected the permitted alternative of
removing the normalization edits and reworking the dependent proof. The delivery now
contains only the G4-held evaluation and cocycle modules. The original
`ModuleCohomologyExtResolutionNormalization` is preserved in full, including its
`abelianResolutionIso` definition and both private proofs. The common, explicitly
constructed `abelianExtSectionsIso` now belongs to the G4-held cocycle module, whose
target comparison uses it. A new local equation `hsource` in the evaluation proof
identifies the original source comparison with the factored composition, by
`(Iso.trans_assoc _ _ _).symm`. Both comparisons retain their original values, types,
visibility and attributes. The cocycle theorem and its current imports are unchanged.

See `coord/changes/G4-abelian-resolution-shared-comparison.md` for the old and new target
comparison, the complete declaration-user list and effects. No forced adaptation is
asserted. The helper is real data constructed from existing isomorphisms. No target
statement changes, and no new mathematical notion or proof obligation is introduced.

The existing evaluation node already describes this naturality-and-composition route;
its proof, dependencies and origin still agree with the Lean. The realized statement
and steps of `dag/units/sk-thm-p1.json` are preserved. The argument includes degree zero,
zero coefficients and empty schemes, with no extra hypotheses.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.abelian_resolution_comparison_evaluation`
(node `new-abelian-resolution-comparison-evaluation`).

One of one original item holes proved; zero holes added; zero split off. No sorry
remains in the assigned module. The delivered cocycle module retains its original,
untouched
`AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.abelian_counit_cocycle_calculation`
(node `new-abelian-counit-cocycle-calculation`). That theorem is not used by this proof.

Both final delivered modules compiled without warnings through `lcompile.py --all`
under the standard 60-second limit: cocycle 46.1 s and evaluation 38.2 s, against the
original normalization dependency. No compiler limit was raised. A fresh scratch
`#print axioms` check of the evaluation theorem, the new prefix and both resolution
comparison definitions reports exactly `propext`, `Classical.choice` and `Quot.sound`;
none depends on `sorryAx`. The two delivery modules' existing G4 claims were read back
and verified before the final dry run.

## No longer needed

Removed the proposed normalization edits from the delivery: the shared-prefix addition,
the `abelianResolutionIso` body change and both private proof adaptations are no longer
needed. The helper is constructed in the G4-held cocycle module, and the proof directly
reassociates the original source comparison. Removed the evaluation module's redundant
proof-only imports `Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization`
and `Sheaf.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic`. Their declarations
remain needed and available through the public cocycle import: all three original
`proof_deps` are used. No planned node or module is pruned. The public cocycle import
supplies the target comparison in the statement; its cocycle theorem is unused.
All current cocycle imports are retained.
No module is pruned from the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The previous report classified the normalization refactor as a forced adaptation even
though the original normalization module compiled against the changed dependencies.
A3 correctly rejected that classification. This repair removes that module's edits
and the obsolete forced-adaptation claim, using the existing source comparison in the
proof instead.

The requested normalization claim was acquired at 2026-10-14 11:29:00 UTC, but the
dispatcher released it at 11:31:08 UTC because the module has no remaining sorry. The
final repair avoids relying on that claim: both edited modules were already G4-held.
Earlier second readings are archived under `scratchpad/repair-A3/`; the next reader
will review the repaired two-module delivery. No mathematical discrepancy or DAG
route error was found.

## Second reading by G4

1. Interface: PASS. Read both complete delivered modules and their diffs against
   the repository. The declaration parser confirms that every existing statement
   string is byte-identical, with the same visibility and docstring. Attributes and
   options are unchanged. The only definition-body change is the recorded factoring
   of `abelianInjectiveResolutionIso`. Its explicit three factors are unchanged;
   `Iso.trans_assoc` identifies the regrouped isomorphism with the original. The
   normalization module is absent from the delivery, as A3 requested. The change
   record lists both actual declaration users; a fresh downstream search agrees.
2. Proof and trust: PASS. Independently compiled the cocycle and evaluation modules
   in import order without errors or warnings, in 46.1 s and 38.2 s. Compiled the
   sole external direct importer, `AbelianCounitResolutionCalculation`, unchanged
   against the delivered overlay in 41.0 s. Fresh `#print axioms` checks report only
   `propext`, `Classical.choice`, and `Quot.sound` for the evaluation theorem,
   `abelianExtSectionsIso`, and both resolution comparisons. The sole remaining
   theorem hole is the unchanged, named cocycle theorem; its own axiom check also
   reports `sorryAx`, while the evaluation theorem does not depend on it. There are
   no forbidden declarations, hollow definitions, or arbitrary witness choices.
3. Split statements: PASS, none added. The common-prefix helper is explicit data
   constructed from existing isomorphisms, with no theorem obligation. The existing
   cocycle theorem, its source, complete docstring proof and node are untouched.
   The universal naturality argument covers p = 0, the zero module and empty X;
   it uses no positivity, nonzero, or nonempty assumption.
4. Route and pruning: PASS. Fresh LeanFinder, Loogle and targeted Mathlib searches
   found `isoRightDerivedObj_hom_naturality` and its inverse form. Their injective
   source hypothesis prevents direct application to forgotten module injectives;
   the proved library `acyclicComparison_naturality` is the appropriate reduction.
   The local related section-comparison lemmas concern two module resolutions and
   provide no shorter public theorem for this target. Both removed imports are
   redundant via the public cocycle import, and are now listed above. Every old
   proof dependency remains used; no DAG node or module is pruned. Read the unit's
   `realized` statement and all steps: this reduction stays below the unit level
   and changes none of them.
5. DAG agreement: PASS. Read the evaluation and cocycle nodes and the three
   evaluation proof-dependency records. The written proof follows the evaluation
   node exactly: forgotten-term acyclicity, identity-coefficient naturality,
   inverse cancellation, common-prefix composition, and evaluation on z. Its
   `proof`, `proof_deps`, and `proof_origin` remain accurate. There are no new nodes
   or split obligations, and no node or unit edit is needed.

Second reading changed only this report: corrected the added-import claim and
listed the two removed redundant proof imports, updated independent compile
figures, and recorded the five checks. The Lean proof and definitions needed no
repair. One of one item holes is closed; zero holes added; zero split off; no
module pruned.
