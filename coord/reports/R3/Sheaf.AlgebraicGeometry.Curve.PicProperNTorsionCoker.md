## What changed

Repaired the returned delivery against the current sheaf-dag version of
lean/Sheaf/AlgebraicGeometry/Curve/PicProperNTorsionCoker.lean. Preserved the public
AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker theorem, its signature,
visibility, docstring, imports, and the Picard decomposition argument. Replaced
only the manual witness proof of hφ with composition of surjections: the Picard
equivalence, first projection, type-tag equivalences, and integer cast modulo n.

Discarded the stale sandbox replacement by the canonical additive interface and
restored the current node record. No interface change or caller adaptation remains.

## Proved and sorry left

AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker has a complete local proof.
The current baseline already has no direct sorries. Holes closed: 0; holes added: 0;
direct holes left: 0. No split-off statements. This is a returned-delivery repair,
not a newly closed hole. Upstream geometric dependencies may still depend on sorry.

## No longer needed

None. Every existing import and both proof dependencies remain. The manual
surjectivity witness construction is replaced by Mathlib's surjection-composition
API. No node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The return states that the module changed on sheaf-dag after base a99f6bca3.
The first repair dry run fetched the current baseline and rejected the stale
sandbox version: it removed Scheme.Hom.pic_proper_ntorsion_coker and added the
canonical additive interface without a change record or caller adaptation. This
repair starts from the current file instead, applies only the hφ simplification,
and preserves its caller interface. The node copy now matches the current route
and signature exactly. The previous second-reading report concerned the stale
version and has been removed so that the next reader can review this repair.

## Second reading by R3

1. Compared the sole delivered Lean module byte for byte with the repository. The
   only difference is the proof of hφ. The existing theorem signature, visibility,
   docstring, imports and definitions are unchanged; no change record is needed.
   The delivered node file is identical to the repository node. Verdict: pass.
2. Compiled the module locally with lcompile.py: exit 0, no warnings. Read the
   complete proof and compiled a scratch copy with #print axioms for
   AlgebraicGeometry.Scheme.Hom.pic_proper_ntorsion_coker: propext,
   Classical.choice, Quot.sound and upstream sorryAx only. There is no local
   sorry, forbidden declaration, hollow definition, or arbitrary data chosen
   from an unproved existence result in this delivery. Verdict: pass.
3. No statement is split off or newly introduced. In particular the repair
   does not rename the original goal as a new assumption. For n = 1 the
   quotient is trivial as expected; n = 0 is excluded by the unchanged field
   hypothesis. Verdict: pass; split-statement searches are not applicable.
4. Read PicardDecomposition and PicProperNTorsionDiv and checked both uses.
   The first-isomorphism calculation retains both dependencies and all imports;
   the geometric imports are private, and public imports provide the statement's
   types and instances. Searched Mathlib's quotient-group power APIs and the
   curve library: the Pi quotient API does not shorten this binary-product
   kernel argument. No old proof dependency is unused. The unit
   sk-thm-curveestimate realizes thm-sc-proper-cohomology with no recorded steps;
   this proof-only repair changes none of its route. Verdict: pass.
5. Checked the node's declaration and verbatim statement, proof steps,
   proof_deps and proof_origin against the Lean. The two recorded geometric
   dependencies and elementary cokernel calculation match. No new node is
   required. Verdict: pass.

Second reading changed only this report: the Lean repair is correct as delivered.
This remains a repair with 0 holes closed, 0 added, 0 split off and no pruning.
