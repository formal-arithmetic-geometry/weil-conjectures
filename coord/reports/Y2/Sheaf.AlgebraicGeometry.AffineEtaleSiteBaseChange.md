## What changed

Proved `AlgebraicGeometry.Scheme.affineEtaleBaseChange_isAffine` using Mathlib's
`AlgebraicGeometry.instIsAffinePullbackSchemeOfIsAffineHom_1`: the object property supplies
an affine source, and the given affine morphism supplies the other hypothesis. The
base-change definition and all existing signatures are unchanged. Removed the rejected
three modules/nodes that only restated the target's conjuncts; they are absent from this
delivery. The main theorem retains its original proof obligation.

The second reader removed the unnecessary unused-variable linter suppression and its
change record, removed two unused proof-only imports, and updated the existing node's
proof and proof_origin to record the completed helper and the remaining proof plan.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.affineEtaleBaseChange_isAffine` (one of the two original
theorems with sorry). The definition `AlgebraicGeometry.Scheme.affineEtaleBaseChange` is
unchanged and now has no sorry axiom dependency.

`AlgebraicGeometry.affineEtaleSiteBaseChange` remains the sole sorry, matching
`lem-weil-pbc-affine-etale-site-base-change`. Its original docstring gives the source and
complete mathematical argument. No new sorry theorem or node is added.

## No longer needed

Removed unused proof-only imports `Sheaf.AlgebraicGeometry.EtaleSetInverseImageExact` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`. All three retained public imports
supply the statements or definition: the affine site, site pullback construction, and
`IsAffineHom`/affine pullback API, respectively.

No existing proof-dependency node is pruned: the main site theorem remains open, and its
remaining DAG proof plan still needs those nodes. In particular affine-morphism permanence
is bypassed by Mathlib for the completed helper but remains in the planned fibre-product
argument. The former three restatement modules/nodes were never existing dependencies of
the repository version and are not delivered.

## Where the brief, the DAG or earlier work was wrong

The earlier three split statements only repeated the target's three conjuncts, providing
no reduction. They were removed before this reading. The old linter-suppression record
referred to a proof assembling an existential result that no longer exists; the current
file compiles warning-free without that suppression. The DAG did not yet record the
direct Mathlib proof of the affineness helper; its first step now records this partial
realization explicitly rather than claiming that the site theorem is proved.

## New nodes

None. No statement or definition change record is necessary.

## Second reading by Y2

1. Compared the complete sandbox module with the repository version. All three existing
   declaration signatures are byte-for-byte unchanged, as is the complete definition
   body. The only theorem proof changed is the affineness helper. No target statement,
   new declaration, hypothesis, or conclusion was changed. Verdict: pass.
2. Compiled the delivered file through lcompile.py without warnings or errors. A scratch
   copy with #print axioms for all three declarations shows only propext, Classical.choice,
   Quot.sound for the helper and definition; the open main theorem additionally uses
   sorryAx. Its single sorry is its entire named public theorem proof. No forbidden
   declaration or hollow definition exists. Verdict: pass for this partial delivery.
3. There are no split-off statements, new nodes, or new modules. Checked that the three
   rejected conjunct restatements are absent. Read Mathlib Morphisms/Affine.lean's two
   affine pullback instances (lines 198–207); the selected second instance needs precisely
   IsAffineHom h and IsAffine U, with no affineness assumption on T or T'. Identity base
   change, empty schemes, and a non-affine base introduce no extra restriction. Verdict:
   pass; no split-off obligation to close.
4. The helper already uses the shortest Mathlib route, and was not rewritten. All retained
   imports provide API used by the existing statements or definition; two unused plain
   imports were removed after a clean compile. Read dag/units/sk-thm-iff.json: its realized
   statement and step are lemma-weil-pbc-property-iff-acyclicity, which this helper does
   not replace or bypass. The main theorem is still open, so its remaining dependency
   plan is retained, not misleadingly reported as pruned. Verdict: pass.
5. Read the existing node's proof, proof_deps, proof_origin, and lean record. The signature
   record matches the unchanged Lean theorem. Updated proof step 1 and proof_origin to
   name the actual Mathlib helper proof and explicitly identify steps 2–4 as still open.
   Its dependency union remains the same because those remaining steps still require
   the original nodes. No new-node field requirements apply. Verdict: pass.

Changes made in this second reading: removed the linter option and obsolete change
record; removed the two unused proof imports and excess blank lines; updated the node's
partial-proof metadata; rewrote the report to distinguish one closed helper from the open
site theorem. No existing statement, definition, or mathematical proof was rewritten.
