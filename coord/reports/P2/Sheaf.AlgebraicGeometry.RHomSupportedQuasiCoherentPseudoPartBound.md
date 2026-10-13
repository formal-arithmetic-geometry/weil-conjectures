## What changed

Filled `AlgebraicGeometry.rhom_supported_quasiCoherent_pseudo_part_bound` without changing
its signature or docstring. The proof unpacks the local pseudo-coherent representative P,
restricts the lower bound on L by exactness, takes a strictly bounded-below representative G,
and applies the existing bounded-below K-injective resolution theorem to G. If P is zero
above b and the resolution I is zero below m, the Hom complex is zero below m-b. The existing
K-injective RHom computation and open restriction comparison transport this bound to the
required restricted global cohomology sheaf.

Three proved private helpers establish internal Hom vanishing for a zero source or target
and the termwise Hom-complex bound. They introduce no public interface and no definitions.
Added only proof imports `Sheaf.Paper.DerivedInternalHomRestrictOpen` and
`Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution`. Updated the existing item's node
proof, proof_deps, and proof_origin to describe the actual argument.

## Proved and sorry left

Holes closed (one): `AlgebraicGeometry.rhom_supported_quasiCoherent_pseudo_part_bound`,
node `new-lem-sc-rhom-supported-qcoherent-pseudo-part-bound`.
Holes added: none. Sorries left in delivered modules: none. No decomposition remains.
The proposed new `AlgebraicGeometry.rhom_supported_quasiCoherent_pseudo_part_bound_local`
sorry and its module and node were removed during the second reading before delivery.

This closes the item's direct hole, not every transitive dependency: the axiom check of the
item reports propext, Classical.choice, Quot.sound, and sorryAx from existing open inputs,
including `SheafOfModules.exists_boundedBelow_injective_resolution`
(node `lem-sc-bounded-below-injective-resolution`). All three private helpers have only
propext, Classical.choice, and Quot.sound. No new axioms or trust bypasses are introduced.
Closure progress remains the maintainer's pinned sorry-ledger calculation.

## No longer needed

Removed the redundant direct proof import
`Mathlib.Algebra.Homology.DerivedCategory.TStructure`; it is already publicly available
through the existing `PseudoCoherentComplex` dependency. Its module remains transitively
reachable, so this is direct-import cleanup rather than pruning a library module.

Removed the first worker's proposed local module
`Sheaf.AlgebraicGeometry.RHomSupportedQuasiCoherentPseudoPartBoundLocal` and proposed node
`new-lem-sc-rhom-supported-qcoherent-pseudo-part-bound-local` from the sandbox delivery.
They were never in the repository and are not library modules to prune.
The repository item's old proof_deps was empty, so no old dependency node was omitted.
No existing library module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker's local split omitted required node fields (including id and the Lean
statement and provenance), had no searches, an unused point parameter, and an incomplete
proof docstring. Merely unpacking the local witness and handing the entire bound to a new
sorry left the calculation unfinished. The existing bounded-below injective-resolution
and RHom restriction/computation theorems give a route that closes the calculation without
that split. The lower-bound conjunct uses only boundedness of the local source complex;
finite freeness and quasi-coherence are needed for other conjuncts, not for this estimate.
Both original hypotheses remain in the unchanged target signature.

The item's original DAG proof_deps was empty despite needing the Hom computation and
restriction comparisons. The delivered existing-node update now records these inputs.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered module against the repository using diff and independently
   asserted that the entire existing theorem signature is byte-for-byte identical.
   The existing docstring and public imports are unchanged. No target, definition,
   visibility, or existing public interface changed. Verdict: pass.
2. Compiled the module locally through lcompile.py without errors or warnings. Scanned
   the delivered source: no sorry, axiom, unsafe, opaque, implemented_by, extern, or
   data-bearing definition. A scratch copy with print-axioms checks confirms only the
   permitted three axioms on private helpers, and additionally sorryAx on the item from
   existing open dependencies. All chosen resolution objects occur inside a theorem
   proof, not in a data definition. Verdict: pass, with transitive holes explicitly noted.
3. Removed the sole proposed split-off statement, so no new holed statement or node is
   delivered. Searches via msearch loogle for sheaf homObj, leanfinder for cohomology of
   internal Hom with bounded source and target, and grep for strictly bounded Hom-complex
   and zero internal-Hom lemmas found no replacement for the needed calculation.
   Read the existing finite-free model, bounded-below resolution, and open restriction
   declarations before choosing this shorter route. Checked the termwise estimate for
   p>b, p=b, n<m-b, and the boundary n=m-b (where vanishing is not claimed); zero complexes,
   empty opens, and the empty scheme also cause no additional hypotheses. Verdict: pass.
4. The proof follows the target downward and uses existing library inputs before any
   split. The originally proposed local calculation is now proved. Public imports remain
   those required by the statement, all added imports are private proof imports, and the
   redundant Mathlib import is removed. No old proof dependency is missing from the report.
   Read dag/units/sk-thm-picard-duality.json: this item is not a realized unit statement or
   step (the realized arrays are empty); no unit or chapter route is changed. Verdict: pass.
5. Read the existing node against the final Lean: each proof step records the actual
   representative, resolution, product estimate, and restriction transport; proof_deps is
   exactly the union of the step uses. Only stage-3-owned proof fields change, and there
   are no new nodes to validate. Verdict: pass.

Second reading changed: removed the proposed local sorry/module/node; proved its actual
Hom-complex calculation with private helpers; rewrote the target proof using existing
resolution and restriction declarations; removed the redundant Mathlib proof import;
updated the item's proof metadata and corrected this report. Existing statements and
public interfaces remain unchanged.

## Second reading by P2

1. Compared every delivered Lean module (one) with the repository using `diff` and
   checked the existing theorem signature and docstring byte for byte. Both public
   imports and visibility are unchanged; no statement, definition, or target changes.
   The only added declarations are three private proved helpers. Verdict: pass.
2. Independently compiled the delivered module with `lcompile.py --all`, without
   errors or warnings. Compiled the scratch copy containing `#print axioms` for
   the main theorem and each helper. The helpers use only propext, Classical.choice,
   and Quot.sound; the main theorem additionally uses sorryAx through existing
   dependencies, including the existing bounded-below injective-resolution theorem.
   Scanned the delivered source: no sorry or forbidden trust mechanism and no new
   data definitions. Resolution witnesses are eliminated only inside a Prop proof.
   The product specification used by the helper comes from the already proved
   `homComplex_exists`, not an arbitrary witness of an unproved existence result.
   Verdict: pass; the theorem is proved relative to existing open inputs.
3. There are no split-off statements, new nodes, or new holes in this delivery.
   Repeated msearch loogle, leanfinder, and grep searches with bound/vanishing queries
   and searched Lean sources with rg. Loogle does not index the project-specific
   sheaf Hom identifier; leanfinder found general cohomology vanishing results but
   no replacement for the internal-Hom product estimate. Repository searches found
   analogous private helpers in AffinePseudoCoherentRHomQuasiCoherent,
   RHomSupportedQuasiCoherentSupportPart, and HomComplexSingleNatural; these are
   unavailable as public inputs, and the affine helper has a more specialized site.
   Checked p>b and p<=b separately: n<m-b implies p+n<m in the latter case.
   At p=b the same strict inequality holds, whereas n=m-b is correctly excluded.
   Zero source or target, empty neighbourhoods, and the empty scheme introduce
   no missing assumptions. Verdict: pass.
4. Read the representative, injective-resolution, RHom-computation, and restriction
   declarations and checked the isomorphism directions through the proof. The
   argument closes the estimate directly using existing inputs, with no restatement
   hole. Both added imports are needed solely by the proof and are private imports;
   the removed direct Mathlib TStructure import is transitively available through
   the statement dependency. The original node has no proof_deps, so the report's
   list of old dependencies no longer needed is complete. The unit
   sk-thm-picard-duality has empty realized statement/step arrays; no recorded unit
   route is bypassed or changed. No existing library module is claimed pruned.
   Verdict: pass.
5. Compared the delivered node JSON with the repository: only proof, proof_deps,
   and proof_origin change. Independently checked that proof_deps equals the union
   of step uses and that each referenced node has the Lean declaration used by the
   argument. The steps match local models, exact restriction, injective replacement,
   the product estimate, and the final cohomology transport. No new node records
   require validation. Verdict: pass.

Second reading changed: appended this independent review and recorded the additional
search findings. No further Lean or node repair was necessary; the earlier round's
proof repairs and removal of the proposed split-off hole were retained.
