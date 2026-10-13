## What changed

Replaced the sole hole of `Sheaf.AlgebraicGeometry.SingleComplexQcqsInduction` by a
complete Lean source-open induction following Stacks Tag 0DJ9. The original signature,
visibility and public imports are unchanged. The induction establishes compactness and
quasi-separatedness of the source over affine bases, applies the affine-open base case,
checks compactness of intersections, applies union gluing, and evaluates at the top open.
A conditional target-locality lemma then passes from affine bases to arbitrary bases.

Added five modules, each with its own node: `SingleComplexOpenComparison` is a real
construction of the restricted canonical comparison, using exactly the pullback
composition expression of `RelativeMayerVietoris`; the other four state transport steps
that the existing declarations do not directly supply. No arbitrary coefficient object
or map is chosen from a mere existence theorem. The only selected isomorphisms are the
existing canonical derived pullback composition comparisons.

The four remaining statements are strictly parts of the argument: an affine source-open
case (no qcqs assumption on f), union gluing (no stalk hypothesis, assumes the three
local comparisons), top-open normalization (arbitrary commutative squares and objects),
and conditional target locality (assumes the affine-base criterion). In particular,
no new hole asserts the original unconditional qcqs theorem under another name.

All six modules compile together; the original module also compiles separately against
the compiled sandbox overlay. The original module contains no `sorry`. No existing
module outside the item is adapted, and no existing interface is changed.

## Proved and sorry left

Closed: `AlgebraicGeometry.singleComplexBaseChangeQcqsInduction`
(node `lem-pc-rf-single-complex-qcqs-induction`), by complete Lean induction and application
of the four named steps below. This is a decomposition, not a proof with all dependencies
closed: one original hole closed, four new holes added, net minus three holes.

Added holes, each the whole proof of a named public theorem in its own module:

- `AlgebraicGeometry.singleComplexOpenComparison_affine`,
  node `lem-pc-single-complex-open-affine`, module `SingleComplexOpenAffine`.
- `AlgebraicGeometry.singleComplexOpenComparison_union`,
  node `lem-pc-single-complex-open-union`, module `SingleComplexOpenUnion`.
- `AlgebraicGeometry.singleComplexOpenComparison_top`,
  node `lem-pc-single-complex-open-top`, module `SingleComplexOpenTop`.
- `AlgebraicGeometry.singleComplexBaseChange_targetLocal`,
  node `lem-pc-single-complex-target-locality`, module `SingleComplexTargetLocality`.

Each carries a source and a complete proof in words. The existing affine and relative
Mayer--Vietoris holes are not changed. The new definition
`AlgebraicGeometry.singleComplexOpenComparison` contains no hole.

Edge cases checked in the statements and their mathematical proofs: empty source/open,
empty target, redundant cover members, zero objects, unbounded complexes, non-affine
or non-compact global targets. The gluing step assumes compactness of the intersection;
the actual induction supplies it from quasi-separatedness. The target-locality step
assumes only local affine bases and does not infer global compactness of X.

## No longer needed

Removed these direct proof imports from the original module:

- `Sheaf.Algebra.Homology.SingleComplexAffineBaseChange`;
- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`;
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`;
- `Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh`;
- `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection`;
- `Sheaf.AlgebraicGeometry.RelativeMayerVietoris`.

Only `Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection`, node
`pqf-lem-qs-intersection-qc`, is genuinely pruned from this route: the proof uses
Mathlib `QuasiSeparatedSpace.inter_isCompact` directly. This does not assert that
other targets or other consumers no longer need that module.

The other five imports are not globally pruned: their mathematical work remains
in the affine, union and locality steps. They are replaced as direct dependencies of
this item's node by the new explicitly typed steps. The affine equivalence, preservation
of quasi-coherence, and affine tensor description remain dependencies of the existing
affine lemma; Mayer--Vietoris remains the union step's dependency. The unit's route
through affine base change, source-open induction and relative Mayer--Vietoris is kept.

## Where the brief, the DAG or earlier work was wrong

The prior sandbox attempt had only the unchanged original hole and search logs.
There was no proof to preserve.

The DAG's mathematical argument is correct, but its transport steps are not elementary
Lean applications of the listed declarations. The affine criterion is stated only for
literal spectra and ring maps; passing to arbitrary affine opens and transporting the
stalk condition and coefficient morphism needs a separate compatibility argument.
Likewise `relativeMayerVietoris` assumes U and V cover its entire source; induction
requires applying it inside U union V and transporting nested-open comparisons. Target
locality and normalization at the top open also require canonical-map compatibility.
These are the four steps split off here, not assertions that the existing holes are
unusable merely because they are holes.

The literature checkout is absent on this machine. The public Stacks Tag 0DJ9 and its
TeX source were read online; the TeX copy is in sandbox `scratchpad/perfect.tex` for
reference, not delivered. LeanSearch was unavailable; the failure is recorded without
an absence verdict. LeanFinder, Loogle, Mathlib grep, project-source searches and a
blueprint search were also performed. Existing coordinate-naturality, top-vertex transport,
and open-restriction detector declarations were inspected; none directly supplies these
four statements with their given coefficient map and source-open coordinates.

## New nodes

`def-pc-single-complex-open-comparison`: module
`Sheaf.AlgebraicGeometry.SingleComplexOpenComparison`, a constructed morphism b_U
for the cartesian inverse image of each source open. It repeats no mathematical
construction with different data: it names the explicit expression already present in
the Mayer--Vietoris hypotheses for reuse in the induction.

`lem-pc-single-complex-open-affine`: module
`Sheaf.AlgebraicGeometry.SingleComplexOpenAffine`, affine base case using the existing
`singleComplexAffineBaseChange` after restriction and affine-coordinate transport.

`lem-pc-single-complex-open-union`: module
`Sheaf.AlgebraicGeometry.SingleComplexOpenUnion`, transport of the existing
`relativeMayerVietoris` statement to a union which need not be all of X.

`lem-pc-single-complex-open-top`: module
`Sheaf.AlgebraicGeometry.SingleComplexOpenTop`, canonical normalization at the top open,
independent of stalk hypotheses and geometric finiteness.

`lem-pc-single-complex-target-locality`: module
`Sheaf.AlgebraicGeometry.SingleComplexTargetLocality`, the conditional local-to-global
step supplied with the affine-base criterion which this item's proof establishes by
induction. It leaves the source induction to its caller.

All node files are under `dag/nodes/sec-picard-framework/`; the original node's proof,
proof dependencies and proof origin now follow the actual Lean reduction.
No change record is needed: existing signatures, definitions and public imports stay
identical, and the new modules introduce only new declarations.

## Second reading by B4

1. **Interfaces: pass.** Diffed all six delivered modules against the repository.
   Five are new. The existing theorem signature is byte-for-byte unchanged, as
   are its visibility, universe declarations and four public imports. Only its
   proof, private proof imports and proof docstring change. No existing definition,
   target or other module is adapted; no change record is required.
2. **Proof and axioms: pass as a decomposition.** Compiled all six modules in
   import order with lcompile.py. Independently printed the axioms of the new
   definition, the four split theorems and the original theorem in a scratch copy.
   The definition uses only propext, Classical.choice and Quot.sound; the theorems
   use those and sorryAx. The only four explicit holes are the named statements
   listed above. No forbidden declaration or hollow definition occurs. The
   comparison is the exact constructed expression of relativeMayerVietoris;
   its composition comparisons have their canonical counit equations, and the
   definition's axiom check confirms no open theorem supplies arbitrary data.
3. **Split statements: pass.** Read each signature and complete docstring proof,
   the matching node, the affine criterion and relativeMayerVietoris. Affine
   source opens have affine inverse images because S' to S is affine; restriction
   transports the actual coefficient map and stalk condition. The union step is
   Mayer--Vietoris inside U union V, with compact overlap explicitly supplied.
   The top step is transport along isomorphisms for any commutative square.
   Target locality assumes the affine criterion and establishes only the passage
   to arbitrary bases; the source induction is still performed by its caller.
   Checked empty schemes/opens, zero objects, repeated union members, unbounded
   objects and noncompact global bases. None of these statements is the original
   unconditional criterion renamed. Repeated LeanFinder, Loogle and Mathlib grep
   searches with identity pullback, Mayer--Vietoris squares, affine tensor and
   morphism restriction queries, and rg searches of both project roots. Inspected
   derivedBaseChange coordinate naturality, top-vertex isomorphism transport,
   pasting, open pullback restriction and the open restriction isomorphism
   detector. They provide components, not the four stated comparisons; no direct
   replacement or short complete proof of a remaining hole was found.
4. **Route and pruning: pass.** Checked the actual induction from the upper
   theorem downward: affine-base locality, affine source opens, compact overlap,
   union gluing and normalization at top. Public imports are needed by signatures;
   the changed proof imports supply the called declarations. The locality module's
   affine tensor import also contains the general derivedPullback_openRestriction_iso,
   so its use is not limited to globally affine schemes. Compared all seven old
   proof dependencies: six direct imports are replaced and all are reported above;
   only pqf-lem-qs-intersection-qc is pruned from the mathematical route, using
   Mathlib instead. Read dag/units/sk-thm-picard-semicon.json: its realized fields
   impose no additional named step here, and its prescribed base-change route
   through affine comparison, open induction and relative Mayer--Vietoris stays.
5. **DAG: pass after metadata cleanup.** Checked all six node records against
   their Lean declarations, sources, chapter/unit, blueprint ancestry and proof
   dependencies. The original node's four proof steps match the Lean reduction;
   the new nodes name the appropriate affine, gluing and restriction dependencies.
   All five new nodes carry the stage-3 fields, source and search records. Corrected
   stray Lean doc-comment terminators from four natural-language node proof texts.
   Confirmed the definition's lean.statement uses the delivery parser's normalized
   signature (def, with the noncomputable modifier omitted).

Changes by the second reader: synchronized the original theorem's proof docstring
with its actual four-step reduction and corrected the node metadata described in
point 5. No signature, definition body, proof body or hole count was changed.
The delivery remains one upper hole closed and four lower holes added: a
**decomposition, net minus three holes**, not a completed axiom-free proof.
