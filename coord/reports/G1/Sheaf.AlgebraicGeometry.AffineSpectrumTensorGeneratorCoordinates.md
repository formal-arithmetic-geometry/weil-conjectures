## What changed

The existing target and `affineSpectrumTensorAdditiveIso` keep their signatures and
bodies (apart from the target proof) unchanged. The target now combines a proved
canonical ring-coordinate theorem with existence of compatible input-complex
coordinates and a generator equation. Both new statements have their own modules.
The new proof import is private to this module. A declaration-local heartbeat limit of 800000 permits the equality check of
the unchanged stalk comparison expression (25 seconds in local compilation,
within the 60-second file limit). A declaration-local unused-variable
linter option accommodates the unchanged target signature's redundant let bindings.

`AffineSpectrumCanonicalStalkRingCoordinates` constructs the actual isoSpec stalk
ring equivalences and proves their three compatibility equations. Its private
component proofs reuse the argument already proved in `AffineSpectrumStalkCoordinateData`;
the latter's public theorem does not pin its existential witnesses to these maps,
so it cannot supply the compatibility needed here.

`AffineSpectrumCanonicalTensorGeneratorFormula` states only the remaining complex
coordinate and generator calculation, with eA and eD fixed to those actual stalk
maps. It spells out the existing additive comparison expression to avoid a cyclic
import; the target proof unfolds its unchanged definition to identify that expression.

## Proved and sorry left

Closed upper hole: `AlgebraicGeometry.SingleComplexBaseChange.exists_affineSpectrum_tensor_generator_coordinates`
(node `lem-pc-affine-spectrum-tensor-generator-coordinates`).

Added lower hole: `AlgebraicGeometry.SingleComplexBaseChange.exists_canonicalSpectrum_tensor_generator_formula`
(node `lem-pc-affine-spectrum-canonical-tensor-generator-formula`). Its docstring gives
the construction of q and the complete section-germ argument. No sorry occurs in a
definition or in the canonical ring-coordinate module.

Also proved: `AlgebraicGeometry.SingleComplexBaseChange.exists_canonicalSpectrum_stalk_ring_coordinates`
(node `lem-pc-affine-spectrum-canonical-stalk-ring-coordinates`) and its private
naturality, point-transport and pure-tensor component lemmas.

This is a decomposition: one old hole closed, one new hole added, net zero holes.
The target still depends on sorryAx through the generator theorem; it is not an
axiom-free completed proof. The first worker's false `affineSpectrum_tensor_generator_formula`
and its erroneous new node were removed before delivery.

## No longer needed

No repository import is removed and no module is claimed pruned. The first worker's
proposed import `AffineSpectrumStalkCoordinateData` is not used in the repaired proof.

The parent's former direct proof-dependency edges to `def-pc-scheme`,
`def-pc-single-complex-base-change-stalk-condition`,
`def-pc-tensor-pullback-composition-iso` and
`lem-pc-iso-pullback-stalk-cohomology` are replaced by the two new intermediate nodes.
These original nodes remain used transitively, and the original public imports
remain necessary for the unchanged definition and public signatures.

## Where the brief, the DAG or earlier work was wrong

The first worker's new theorem quantified over every q while its hypotheses only
constrained ring maps. For a nonzero complex over a field of characteristic other
than two, q and -q satisfy exactly the same hypotheses but give opposite generator
images. Since H is fixed and invertible, both asserted formulas cannot hold.
Even the identity square over a field exhibits this problem; the zero-complex
case alone would fail to detect it. The repaired theorem fixes the actual ring
maps and asserts existence of a compatible q instead.

The first worker's node copied the parent's existential natural-language statement,
used a placeholder instead of the verbatim Lean statement, copied unrelated review
metadata, and made its proof depend on the parent which in turn depended on it.
The repaired nodes record the actual distinct statements and have no proof cycle.
The original target docstring was accidentally attached to the new false theorem;
it is preserved and attached to the original target in the repaired module.

## Second reading by G1

1. Compared all existing declarations against the repository version: the target
signature and the complete additive-isomorphism definition are byte-for-byte
unchanged. No existing statement, definition, or visibility is changed; no change
record or adaptation is required. Verdict: pass after repair.
2. Read all delivered Lean declarations and checked for forbidden constructs and
hollow data. The only new sorry is the named generator theorem. Local compilation
and axiom probes are recorded below. Verdict: the reduction is valid, with its
one explicit remaining mathematical obligation.
3. Rejected the first split statement by the q/-q counterexample. The replacement
separates ring compatibility from the complex generator calculation. The canonical
ring construction is explicit; the lower theorem has no arbitrary-coordinate
universality claim. Tested zero complexes, nonzero identity squares and empty
spectra conceptually. Searches using new leanfinder, loogle and grep queries find
component lemmas, not these fixed-coordinate statements. Existing private ring
proofs were reused rather than inventing a different ring argument. Verdict: pass.
4. The target is reduced from the top using a proved ring theorem and the remaining
section-germ calculation. Imports were checked against their use in statements,
definitions and proofs. `dag/units/sk-thm-picard-semicon.json` has empty realized
statement and step lists; this below-unit split changes no unit route. All four
old parent dependency edges are accounted for above. Verdict: pass.
5. Checked the parent proof and new-node proof steps, their uses and union
proof_deps, proof origins, verbatim Lean signatures, sources, search records,
chapter/unit and creation metadata. No proof dependency returns to the parent.
Verdict: pass after replacing the erroneous node.

Changes made: removed the false universally quantified formula; proved canonical
ring compatibility; added a smaller existential generator calculation in its own
module; rebuilt the target proof with unchanged signature and definition; corrected
node records, docstring placement and the report's progress accounting.

## New nodes

`lem-pc-affine-spectrum-canonical-stalk-ring-coordinates` records the constructed
stalk ring equivalence and its proved compatibilities with the actual eA and eD.

`lem-pc-affine-spectrum-canonical-tensor-generator-formula` records the remaining
existence of a compatible q and the generator equation for the fixed additive
comparison. It asserts no ring-compatibility equations and does not restate the
parent theorem. No change records are required.

Verification: both new modules compiled locally in import order (ring coordinates
in 9 seconds, formula in 16 seconds). The repaired target compiled in 25 seconds.
A scratch copy with explicit `#print axioms` for all five public declarations
compiled in 25 seconds: the canonical ring equivalence, its compatibility theorem
and the unchanged additive comparison use only `propext`, `Classical.choice`,
`Quot.sound`; the generator theorem and the target additionally use `sorryAx`,
exactly as expected from the one remaining hole. The scratch-only probe lines
triggered line-length warnings; all delivered Lean lines are at most 100 characters.
No warnings remain in the delivered sources. LeanSearch returned an internal server
error for both new queries; this is recorded as unavailable, with independent
LeanFinder, Loogle and grep searches completed for each new node.

Delivery gate: `deliver3.py G1 Sheaf.AlgebraicGeometry.AffineSpectrumTensorGeneratorCoordinates --no-push`
printed OK: all three delivered modules compile and pass the preflight and complete
constant axiom probes. The class is CODEX (two new modules and nodes, one named
remaining sorry). This is a reviewed decomposition, not net hole reduction.
