## What changed

Proved `RingHom.exists_retraction_of_wlocal_geometric_criterion` in
`lean/Sheaf/RingTheory/WContractibleGeometricCriterion.lean`, preserving its exact signature,
both universe parameters, and every public import.

The proof packages the geometric hypotheses into the existing `IsWContractibleRing` class,
uses `RingHom.WeaklyEtale.exists_indEtale_comp` to refine the cover, applies
`IsWContractibleRing.exists_retraction`, and composes the resulting retraction.
Two fully proved private helpers handle the common-universe proof and transport of
w-contractibility across ring equivalences. The general proof lifts both rings to their
common maximum universe; faithful flatness is transported using flatness and surjectivity
on spectra, and weak etaleness uses Mathlib's ULift equivalence. No data is chosen from
an unproved theorem.

Updated the item's node proof/dependencies and attached two already proved source results
as new DAG nodes. No new Lean modules or public declarations, no definition changes,
and no changes to other modules.

Validation: the final module compiles cleanly in about two seconds via `lcompile.py`.
`#print axioms` for the target and both reused source theorems reports exactly
`propext`, `Classical.choice`, and `Quot.sound`; in particular the complete proof is free
of transitive sorry dependencies. Checked the original and final signatures after whitespace
normalization, and checked that public imports are identical. The constructions and spectrum
arguments require no nontriviality assumption and include zero rings.

The source text is absent from this machine's `literature/` checkout; read the source-library
proofs and verified the corresponding official Stacks statements/proofs at
[Tag 0982](https://stacks.math.columbia.edu/tag/0982) and
[Tag 097Z](https://stacks.math.columbia.edu/tag/097Z).

## Proved and sorry left

Closed the sole original hole:
`RingHom.exists_retraction_of_wlocal_geometric_criterion`
(`lem-weil-pbc-wcontractible-geometric-criterion`).

Holes closed: 1. Holes added: 0. No sorry remains in the delivered module, its private
helpers, or the transitive proof dependencies of its theorem. This is a proof, not a
decomposition. The two new DAG nodes attach existing, fully proved source declarations;
neither is a split-off obligation.

## No longer needed

Removed these nine proof imports:

- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
- `Mathlib.RingTheory.Localization.AtPrime.Basic`
- `Sheaf.RingTheory.IndEtaleStability`
- `Sheaf.RingTheory.RetainedLocalization`
- `Sheaf.RingTheory.RetainedLocalizationProperties`
- `Sheaf.RingTheory.WLocalStalkIsomorphismRetraction`
- `Sheaf.RingTheory.WeakEtaleRefinementProperties`
- `Sheaf.RingTheory.WeaklyEtaleField`
- `WeilConjectures.RingTheory.ProEtale.HenselianLocalRing`

Only `WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale` is needed as a proof import.
The five original public imports support the statement interface and remain unchanged.

The target no longer directly invokes the planned Sheaf refinement construction,
retained-localization construction/properties, stability conjunction, weakly-etale-field
conjunction, or cross-universe w-local stalk-retraction statement. The corresponding
original direct proof dependencies removed from the item's node are:

- `def-weil-pbc-ind-etale-algebra`
- `def-weil-pbc-localization-at-prime`
- `def-weil-pbc-retained-localization`
- `lem-weil-pbc-ind-etale-stability`
- `lem-weil-pbc-retained-localization`
- `lem-weil-pbc-weak-etale-field`
- `lem-weil-pbc-wlocal-stalk-isomorphism-retraction`
- `thm-weil-pbc-weak-etale-refinement`
- `thm-weil-pbc-weak-etale-strict-local`

These are removals from this item's direct route and Lean imports. Their mathematical
content is already implemented by the closed source theorems; some remain recorded in
those theorems' explanatory DAG proof plans or are still used elsewhere in the library.
No global unreachability claim is made. The unit's own statement and realized proof steps
are unaffected; this is a supporting node below that level.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route error was found. The planned argument was already
implemented in the source library, but the DAG lacked attachments for the two exact
source results needed here. Their existing APIs use a common universe, whereas this
item permits independent universes; the explicit transport proof closes that interface gap.

Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch. LeanSearch returned
Internal Server Error and is recorded as unavailable, not as a negative result. The other
services found no Mathlib equivalent; source-library grep found the two reused declarations.
Blueprint searches for the tags, refinement name, ind-etale w-contractible splitting, and
retraction found no duplicate blueprint node. No changes to the blueprint unit are needed.

## New nodes

`lem-weil-pbc-existing-wcontractible-indetale-retraction` attaches the existing
`IsWContractibleRing.exists_retraction` from
`WeilConjectures.RingTheory.ProEtale.WContractible`. It proves ind-etale splitting from
the geometric hypotheses (Tag 0982 (3) to (2)); the source class packages those hypotheses.
The node records the source proof route; its Lean theorem is already fully proved.

`lem-weil-pbc-existing-weakly-etale-indetale-refinement` attaches the existing
`RingHom.WeaklyEtale.exists_indEtale_comp` from
`WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale` (Tag 097Z). It records only the
existential refinement used by this proof, rather than imposing a particular construction.
Its Lean theorem is already fully proved. Neither new node introduces a module or a sorry.
No change record is needed because all existing signatures and public imports are preserved.

## Second reading by F4

1. **Interface: pass.** Compared the delivered module with the repository using `diff` and
   extracted the target signature: it is byte-for-byte identical, including both universes.
   All five public imports are identical. There are no changed definitions, statements,
   visibilities, or other modules; no change record is needed.
2. **Kernel proof: pass.** Independently compiled the module with `lcompile.py` (2 seconds,
   clean) and checked the target and both reused source declarations with `#print axioms`.
   Each uses only `propext`, `Classical.choice`, and `Quot.sound`. No forbidden constructs,
   hollow definitions, or sorry remain. Both private helpers are fully proved.
3. **Attached statements: pass.** There are no split-off holes. Read the source declarations
   and the arguments implementing the two existing results; the attached statements exactly
   describe their common-universe APIs. They are strictly intermediate results: ind-etale
   splitting and weakly-etale refinement, rather than a renamed copy of this target.
   The transport and splitting also cover zero rings; no nontriviality is assumed.
   Independent LeanFinder search for splitting of faithfully flat ind-etale algebras and
   Loogle search for weak-etale universe transport confirmed the chosen route (the latter
   finds the already used `Algebra.WeaklyEtale.ulift_iff`). Searched `lean/Sheaf` and the
   source pro-etale modules for retraction and w-contractibility declarations; no shorter
   existing theorem or duplicate attachment was found. Mathlib grep for faithful-flat
   universe transport found no shortcut.
4. **Top-down route and pruning: pass.** The proof uses the two closed source results and
   then proves the necessary universe transport explicitly. Read the unit's `realized`
   statement and three steps: this supporting ring-theory node replaces none of them.
   The report lists every removed direct proof dependency and all nine removed proof imports.
   Public imports support the original interface and are preserved. Checked that composing
   the ind-etale splitting with the refinement really retracts the original map and that the
   spectrum transport establishes faithful flatness without an additional hypothesis.
5. **DAG agreement: pass.** The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. Each delivered node's dependency list equals the union of its proof-step
   uses. Checked the new nodes' sources, creation records, searches, existing Lean
   declarations, universes, chapter and unit; there is no duplicate declaration attachment.
   The resulting proof-dependency closure (283 nodes) has no cycle. Existing source
   declarations are correctly marked `existing: true`, and neither adds a Lean declaration
   or an open obligation.

Second-reading changes: added this audit report and refreshed the scratch axioms check from
an exact copy of the delivered module. No Lean code or DAG repair was necessary. Holes
closed remain 1 (the named target); holes added remain 0.
