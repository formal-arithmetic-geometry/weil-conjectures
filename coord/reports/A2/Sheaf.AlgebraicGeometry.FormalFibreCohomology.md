## What changed

In `Sheaf.AlgebraicGeometry.FormalFibreCohomology`, proved both completed-ring
scalar-linearity theorems. Added the proof-only import
`Sheaf.AlgebraicGeometry.ModuleCohomologyFMapBasicProperties` and four proved private
helpers: `eval_factorPow`, `scalarMap_transition`, `completedScalarMap_transition`,
and `cohomologyFMap_smul`. Public signatures, definitions, visibility, existing
docstrings, and public imports are unchanged. Updated the existing node's proof,
proof dependencies, and proof origin to describe the completed argument.

The scalar compatibility is proved directly from Mathlib: the first projection
of `pullback.map`, naturality of `ΓSpecIso.inv`, and Cauchy-sequence compatibility
of completion evaluations. The section proof uses `map_mul`; the cohomology proof
uses clause (1) of the already stated h-map basic properties. Explicit module
parameters and a generic private helper keep elaboration within the single-file
limit; the final file compiled without warnings in 12.5 seconds.

## Proved and sorry left

Closed two original holes, both recorded by node
`def-weil-pbc-formal-fibre-cohomology`:

- `AlgebraicGeometry.formalFibreCohomologyTransition_smul`.
- `AlgebraicGeometry.formalFibreSectionsTransition_smul`.

No direct `sorry` remains in this module; no holes are added or split off.
The cohomology proof depends on the existing theorem
`AlgebraicGeometry.Scheme.Modules.moduleCohomologyFMap_basic_properties`, node
`lem-weil-pbc-module-cohomology-fmap-basic-properties`, which remains an upstream
proof obligation. This is a proof from an existing stated dependency, not a claim
that all transitive axioms have been eliminated.

## No longer needed

None. Every original public import supports a statement, definition, or the
module's local enough-injectives instance. The single added proof import is used.
The original node's proof dependency list was empty; no planned dependency is
removed. No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The node recorded only the two previously completed elementary compatibility
proofs and left both scalar-linearity assertions open. Its original theorem
docstrings already identify the correct route: compatibility of quotient scalar
maps plus cohomology h-map linearity. The updated DAG now records the existing
basic-properties theorem as the cohomology proof dependency. No mathematical
statement correction or forced adaptation was needed.

## Second reading by A2

1. PASS: read the whole module and its diff against the repository. Every existing
   declaration signature, definition body, visibility, docstring, and public import
   is byte-for-byte unchanged. Changes are the two proof bodies, four proved private
   helpers, and one plain proof-only import. No change record is needed.
2. PASS: independently compiled the delivered file with lcompile.py without errors
   or warnings (19.7 seconds). A scratch copy with #print axioms for all 26
   declarations compiled (14.9 seconds). All axioms are propext, Classical.choice,
   Quot.sound, or existing upstream sorryAx. In particular the section-linearity
   theorem and the scalar-compatibility helpers have no sorryAx; the cohomology
   additive map already depends on sorryAx before applying basic properties.
   No direct sorry or forbidden declaration mechanism occurs in the delivered file;
   no definition or data construction was changed. The linear witness in the new
   private cohomology helper is used only to prove an equation, and its underlying
   additive map is fixed by the upstream theorem's equality.
3. PASS: no split-off statements, new public statements, nodes, or holes. Checked
   the private helpers mathematically: reduction of completion evaluations works
   for every commutative ring and ideal, including the zero and unit ideals and
   n=0; scalar compatibility follows from the first pullback projection and
   Gamma-Spec naturality. Cohomology linearity specializes the existing theorem's
   first clause without extra geometric hypotheses. The section proof is just
   multiplicativity. A fresh leanfinder search for induced derived global-sections
   maps respecting scalars returned section/presheaf linearity lemmas, not a
   replacement for the upstream derived-cohomology result; rg on the library and
   inspection of Mathlib's completion algebra API found no shorter relevant route.
4. PASS: the proof uses elementary scalar compatibility and the existing stated
   h-map basic-properties theorem directly. The added import is proof-only and
   used; existing imports support the unchanged construction and its local
   enough-injectives instance. The old proof_deps list was empty, so No longer
   needed is complete. Read dag/units/sk-thm-p1.json: this definition node is below
   its realized statement and steps; no realized node or unit route is bypassed.
5. PASS: compared the node JSON against the repository. Only proof, proof_deps,
   and proof_origin differ. The four steps describe the Lean proof, their uses
   union is exactly lem-weil-pbc-module-cohomology-fmap-basic-properties, and its
   declaration and first clause match the proof-only import. No new node schema
   obligations arise.

Changes made in the second reading: appended this independent review only; no
Lean or DAG repair was needed. Two original named holes closed, zero holes added,
zero split off; transitive cohomology obligations remain explicitly acknowledged.
