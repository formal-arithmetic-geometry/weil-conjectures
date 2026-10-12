## What changed

Completed the proof of `AlgebraicGeometry.etaleSet_finiteLocalStageRepresentatives`.
The proof obtains finite affine local representatives, descends the finite geometric
cover and factorization data with
`AlgebraicGeometry.etale_finiteCoverFactorizationDescent`, and verifies the section
identities by naturality and the composition-unit equation. Added explicit affine and
site-continuity instances required by elaboration. The existing comparison source was
compiled in the sandbox because its published `.olean` was absent from the local
snapshot; its source and interface were unchanged.

## Proved and sorry left

Closed the existing hole in
`AlgebraicGeometry.etaleSet_finiteLocalStageRepresentatives` (1 of 1 item holes).
Its local representation and composition/naturality arguments are now kernel proofs.
The private helpers `finite_representatives` and `comparison_unit` contain no sorry.

Added one hole: `AlgebraicGeometry.etale_finiteCoverFactorizationDescent`, node
`lem-weil-pbc-etale-finite-cover-factorization-descent`, in its new module.
This is a strictly geometric subproblem: it has no sheaf, section, comparison map,
or matching assertion. Consequently this delivery is a decomposition: one existing
hole closed, one lower hole added, net zero from these declarations. The item still
has a transitive `sorryAx`; it is not an axiom-free completion of a target.

## No longer needed

Removed the unused `Mathlib.AlgebraicGeometry.AffineTransitionLimit` import from the
new geometric statement module; the item's proof retains its plain import to prove
that cone projections are affine. All added proof imports in the item are plain
`import`; the two original public imports support its unchanged statement.

The old item's proof dependencies no longer used directly are:

- `lem-weil-pbc-affine-etale-site-colimit` (`AffineEtaleSiteColimit`): retained in the
  new geometric subproblem's proof plan, so no global pruning is claimed.
- `lem-weil-pbc-affine-etale-site-topos` (`FullAffineEtaleTopos`): no direct use.
- `lem-weil-pbc-etale-inverse-image-algebraic-structures`
  (`EtaleInverseImageAlgebraicStructures`): no direct use; still transitive through
  the existing comparison and composition-unit modules.
- `lem-weil-pbc-sets-affine-etale-inverse-image-comparison`
  (`AffineEtaleInverseImageComparison`): bypassed by direct small-site representatives.
- `lem-weil-pbc-site-sheafification-sections-local`
  (`SiteSheafificationSectionsLocal`): replaced by Mathlib's locally surjective
  sheafification image sieve and the proved Kan representative theorem.

None of those modules was a direct import of the original item, so there are no
removed original import lines and no certified globally pruned modules. The unit's
`realized` route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The local compiled snapshot lacked `EtaleSetSheafComparison.olean` even though the
source module and its dependency were present. Compiling that unchanged source in the
sandbox makes the item and delivery checks elaborate. The prior blocked result was
therefore a snapshot/tooling issue, not a mathematical obstruction.

## New nodes

`lem-weil-pbc-etale-finite-cover-factorization-descent` records finite affine covering
and factorization descent, with the source and proof plan in its docstring and node.

## Second reading by V1

1. Compared every existing delivered module with the repository using diff.
   The sole existing public theorem signature is byte-for-byte identical, including
   its hypotheses, conclusions and visibility. The comparison module is byte-for-byte
   unchanged and is present only to compile the missing local artifact. No existing
   definition or interface changed; no statement-change record is needed.
2. All three sandbox modules compile locally in import order without warnings.
   The item and its private helpers contain no sorry. The one delivered sorry is
   exactly the named geometric theorem listed above, with its docstring and node.
   No axiom, unsafe, opaque, implemented_by, extern or hollow definition was added.
   Scratch `#print axioms` checks and the delivery's all-declarations probe check
   the standard axioms plus the explicitly permitted transitive `sorryAx`.
   Choosing the existing composition isomorphism is justified by its fixed-sheaf
   uniqueness clause, and that existing composition theorem is already proved.
3. Checked the split statement's n=0, empty source/target, constant system, and
   singleton-family cases. Empty covering descent makes W empty eventually; finite
   common upper bounds suffice; arbitrary U need not be qc or separated because its
   étale structure morphism is locally finitely presented. Read the existing affine
   finite-diagram and eventual-covering declarations and searched with Lean Finder,
   Loogle and grep using finite-diagram and locally-finitely-presented-target terms.
   Mathlib supplies the auxiliary morphism-descent step, but no theorem found packages
   all the stated geometry. This is strictly part of the argument, not a renamed
   section-lifting theorem. Verified the sources
   [0EYL](https://stacks.math.columbia.edu/tag/0EYL),
   [01ZM](https://stacks.math.columbia.edu/tag/01ZM), and
   [01ZC](https://stacks.math.columbia.edu/tag/01ZC) online because this clone lacks
   the cited literature source files. The full geometric proof is not a few-minute
   closure; it remains the single split theorem.
4. Read the proof from the target down: sheafification image sieve, proved finite
   affine refinement and Kan representatives, geometric descent, and then proved
   composition-unit compatibility plus naturality. The remaining geometry is a
   documented sourced step. The original public imports are needed for the statement;
   extra proof imports are plain. Completed the list of old proof dependencies no
   longer directly used and distinguished them from genuinely pruned modules. Checked
   `dag/units/sk-thm-iff.json`: its statement and sole step are realized by
   `lemma-weil-pbc-property-iff-acyclicity`; this delivery does not bypass that route.
5. Checked both nodes' statements against Lean and their proof-step dependency unions.
   The existing node records exactly local representatives, geometric descent and
   composition-unit compatibility. The new node has source, complete proof steps,
   dependency records, three search kinds, split status, creation/blueprint metadata,
   chapter/unit and verbatim Lean signature. Updated the stale draft proof-origin text.

Changes made in this reading: replaced proposition-valued `haveI` with `have`, removed
its unnecessary linter suppression and change record, removed the unused geometric
module import, restored the original signature whitespace, made the auxiliary-map
proof in the geometric docstring explicit via 01ZC(3), recorded the independent search,
and corrected the pruning and decomposition accounting in this report.
