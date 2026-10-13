## What changed

Proved `AlgebraicGeometry.Scheme.strictPerfect_relativeTensor_roof_comparison`
with its signature and three public imports unchanged. All additional imports are
proof-only. The proof transports the strictly perfect model to the open subscheme,
uses bounded-above flat K-flatness and the existing derived tensor comparison,
then applies exact scalar restriction.

Repair of the landing refusal: generalized both private duplicate helpers in place.
`flat_retract` now handles retracts of free modules of arbitrary rank `I : Type u`,
instead of only finite ranks. `equivalence_totalTensor_iso` handles any equivalence
between the two module categories, with a supplied natural tensor comparison,
instead of only `Modules.overEquiv U`. Its proof uses `mapTotalIso` and
`HomologicalComplex.Hom.isoOfComponents`. The caller supplies the canonical
comparison from `exists_localizedOpen_tensor_equivalence`. These are strict
mathematical generalizations, not changes of names to evade duplicate detection.
The earlier helpers cannot be reused by ordinary imports: all three are private.
No other module is modified or requires adaptation.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.strictPerfect_relativeTensor_roof_comparison`
(node `lem-pc-strict-perfect-relative-tensor-roof-comparison`).
No sorry remains in the delivered module. No hole was added or split off.
Existing imported dependencies remain their own proof items.

## No longer needed

No original import was removed; the three public imports supply the unchanged
statement. The planned site-level K-flatness node
`lem-pc-bounded-above-flat-kflat-site` and module
`Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat` are not needed: transport to
`U.toScheme` uses `lem-pc-bounded-above-flat-kflat` in
`Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat` instead.
No roof, common-complex, or fraction-representation lemma is needed.
The specialized private `localizedEquiv_totalTensor_iso` is replaced by its
more general equivalence comparison. The finite-rank-only retract helper is
replaced by the arbitrary-rank version. No proof dependency import was removed
in this repair; the generalized helpers need the same categorical ingredients.

## Where the brief, the DAG or earlier work was wrong

The previous delivery copied private helpers whose statements already occurred
elsewhere, so the landing duplicate check refused it after reviewer approval.
This repair generalizes both statements in place, as the return requested.
The DAG route remains valid: the caller still uses the canonical equivalence
and finite-free retracts; only private proof infrastructure is generalized.
The empty open and zero/rank-zero terms require no extra hypotheses. Arbitrary
free rank works because flatness is closed under coproducts and retracts. The
comparison works for any supplied equivalence because it preserves coproducts;
naturality of the supplied tensor comparison gives the two differential identities.
The original and repaired public theorem signatures are unchanged. Verification: the complete module compiled without warnings. The explicit
`tools/import_prune_check.py` check against the original module exited 0.
`deliver3.py H2 Sheaf.AlgebraicGeometry.RelativeTensorRoofComparison --no-push`
printed `OK (dry run)` and exited 0. Nothing was pushed. The prior second reading
is preserved below as superseded; the next independent reader reviews this repair.

Change record: `coord/changes/relative-tensor-roof-proof-local-instances.md`.

## Earlier second reading (a previous round; superseded)

1. **Interface and accidental changes.** Compared the delivered module and node with the repository versions. The theorem signature and the three public imports are byte-for-byte unchanged. The added imports are proof-only, and all added helpers and instances are private or local. Verdict: pass.

2. **Compilation and trust.** Compiled the complete delivered module with `lcompile.py` (exit 0, no warnings). Searched the module for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, and `extern`; none occur. The completed theorem uses only ordinary library declarations; no new split-off theorem or hole was added. Verdict: pass.

3. **Statement and proof correctness.** Read the theorem body from the target downward. The finite-free retract argument establishes flatness and bounded-above K-flatness, the open restriction and derived tensor comparison are composed through the canonical localized-open equivalence, and exact restriction of scalars identifies the stated endpoints. Empty opens and rank-zero terms are covered by the same equivalences and retract argument. The theorem statement is unchanged and no weaker replacement was introduced. Verdict: pass.

4. **Pruning and imports.** Checked the proof against its imported declarations and the updated node. The proof uses the ringed-space bounded-above flat K-flatness result and the localized-open tensor equivalence; the previously planned site-level K-flatness node is correctly removed from `proof_deps`. All added imports are used by the proof, while the three public imports remain required for the unchanged statement. Verdict: pass.

5. **DAG and unit route.** The sandbox node records the four proof steps, their actual dependencies, and H2 as proof origin. The unit remains `sk-thm-picard-semicon`; the proof supplies the local comparison and scalar-restriction step without altering the unit statement or route. Verdict: pass.

Changed during second reading: appended this audit only. No Lean source, theorem statement, definition, public import, or DAG proof route was altered.

## Second reading by H2

1. **Unchanged interface.** Read the full source and compared it with the repository
   using `diff -u`; independently compared the public theorem's signature as text.
   Its signature, existing docstring, visibility, and three public imports are
   byte-for-byte unchanged. The seven added imports are plain proof imports.
   All new definitions, instances, and helper theorems are private or local.
   The local attribute classification is documented in the existing change record.
   Verdict: pass; no accidental public change.

2. **Proof and trust.** Compiled the complete delivered module with `lcompile.py`: exit
   0, no warnings (55.4 seconds). Scanned the delivered source for `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, `extern`, and explicit `sorryAx`: none.
   The only new definition explicitly supplies the existing monoidal structure;
   it chooses no witness from an existence theorem. Read the scalar-restriction
   endpoints against `strictPerfectRelativeTensorComplex`: they agree definitionally.
   The independent scratch-copy axiom check and delivery probe are recorded below.
   Verdict: source and compilation pass.

3. **New statements and edge cases.** No statement is split off and no hole is added.
   Read both generalized helpers: `flat_retract` proves arbitrary-rank free flatness
   by flatness of coproducts of the unit and closure under retracts;
   `equivalence_totalTensor_iso` uses the supplied natural tensor isomorphisms for
   both differentials and equivalence-preserved coproducts for totalization.
   Empty index types, rank zero, zero complexes, and the empty open require no
   additional assumptions. Searched the project with `flat_of_retract`,
   `restrictScalars.*preserves`, `mapTotalIso`, and bifunctor-comparison variants.
   Existing generic ingredients are used; the matching specialized helpers in
   `LocalizedPullbackPerfectModel`, `LocalizedPullbackPerfectCounit`, and
   `LocalizedOpenKFlatTensorRestriction` are private and strictly specialized.
   No public replacement for these generalized comparisons was found. Verdict: pass.

4. **Route and pruning.** Read from the public theorem down through the open tensor
   comparison. The proof first establishes transported flatness and boundedness,
   then uses the existing ringed-space K-flatness, exact derived open restriction,
   K-flat tensor comparison, and localized tensor equivalence. Finally it reflects
   exactness of scalar restriction through the underlying sheaf functor.
   The old proof-dependency set minus the new set is exactly
   `lem-pc-bounded-above-flat-kflat-site`, already listed under No longer needed.
   No original public import is dropped. The added imports provide the cited
   comparisons, totalization transport, flat retract facts, and exactness instances.
   Verdict: pass, subject also to the delivery import check.

5. **Nodes and unit.** Compared the existing node JSON: only `proof`, `proof_deps`,
   and `proof_origin` change. The four steps and their dependency union match the
   Lean argument; statement, Lean statement record, and source are unchanged.
   There are no new nodes. Read `dag/units/sk-thm-picard-semicon.json`: this is local
   tensor-comparison infrastructure below its stated semicontinuity route. Neither
   the unit nor its route is changed. Its existing `realized` lists are empty in
   the baseline; this delivery does not claim to fill them or bypass a unit step.
   Verdict: pass.

Changed during this second reading: appended this independent audit only. No Lean
source, node, or change record required repair.
