## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.Morphisms.DepthThreeCompletedQuotientLift` by a complete
categorical assembly proof, preserving its signature and its existing docstring.
Added two proof imports, two new theorem modules, and their DAG nodes.

`CompletedQuotientCoverLift` supplies a finite etale completed cover whose restriction
agrees with the given cover only after the principal quotient. It assumes neither
puncturedness nor depth. `CompletedPuncturedQuotientFullyFaithful` states full
faithfulness of quotient restriction for arbitrary finite etale covers of the
punctured completion, with no quotient-extension assumption or specified cover.
These are strictly separate parts of the complete-case argument of Stacks 0BLS.

The proof constructs objects P and Q in the finite-etale morphism-property-over
category, packages the quotient scheme isomorphism with `Over.isoMk`, lifts it using
`FullyFaithful.preimageIso`, and maps the resulting isomorphism to schemes. The
projection equality follows from `MorphismProperty.Over.w`. Full faithfulness
verifies the inverse identities inside Mathlib's preimage-isomorphism construction.
No definition or existing declaration signature changed.

The three delivered modules compile together using lcompile.py. The final compile
has no warnings. The unit route remains unchanged: its `realized` lists contain no
nodes at this cut, and the reduction keeps the complete-case argument of 0BLS.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.exists_completed_etale_extension_of_depth_three_of_quotient_extension`
(node `lem-sbc-depth-three-completed-quotient-lift`). No sorry remains in the item.

Added two holes, each the entire proof of a named public theorem in its own module:

- `AlgebraicGeometry.Scheme.exists_completed_cover_with_quotient_iso`
  (`lem-sbc-completed-quotient-cover-lift`, module `CompletedQuotientCoverLift`).
- `AlgebraicGeometry.Scheme.fullyFaithful_completed_punctured_quotient`
  (`lem-sbc-completed-punctured-quotient-fully-faithful`, module
  `CompletedPuncturedQuotientFullyFaithful`).

This is a decomposition, not a sorry-free proof of the geometric inputs: one upper
hole closed and two lower holes added. Both lower statements include complete
source arguments in their docstrings and nodes. The first is true for arbitrary U;
the second applies to all finite etale covers independently of hquot. Their edge
cases were checked: f=0 gives quotient restriction by an isomorphism; empty U and
empty covers cause no exceptions. Nonconstant ranks are allowed. No data definition
chooses a witness from an unproved existence theorem.

## No longer needed

No original imports were removed and no entire modules are pruned. All four original
public imports remain required to express the unchanged signature. The two added
proof imports are used by the proof.

The original node's direct proof dependency list of five definitions
(`def-weil-pbc-depth`, `def-weil-pbc-adic-completion`,
`def-weil-pbc-henselian-terminology`, `def-weil-etale-morphism`,
`def-pc-fibre-product`) is replaced by the two new intermediate nodes. Those
notions remain needed in the intermediate arguments; this is not claimed as
pruning them out of the targets' dependency closure. No planned geometric step
was bypassed, and no unrelated module was imported.

## Where the brief, the DAG or earlier work was wrong

The original node's proof dependencies name definitions only. In particular none
states the geometric full-faithfulness input of 0BM6, so they do not suffice to
implement the two non-elementary steps without new intermediate statements.
Existing henselian proper-scheme lifting interfaces were inspected, but they do
not directly provide the combined quotient base-change comparison or punctured
full faithfulness used here.

The original docstring and node cite 0A02 for local cohomology base change. That tag
is henselization of pairs. The correct citation is 0ALZ (47.9.3), explicitly cited
by 0BM6 and 0BLS. The new full-faithfulness node uses 0ALZ. Completeness implies
henselianness by 0ALJ (15.11.4); the new docstrings explain why maximal-ideal
completeness gives principal-ideal completeness here. The existing docstring and
immutable node source field were retained; the error is reported for correction.

Sources read online: Stacks 0BLS, 0BM6, 09ZL, 0AVY, 0ALZ and 0ALJ.
Mathlib searches were run by LeanFinder, Loogle and grep; LeanSearch returned
Internal Server Error and is recorded as unavailable, never as a negative result.
The imported blueprint was searched for 0BM6 and 09ZL, with no matching nodes.

## New nodes

`lem-sbc-completed-quotient-cover-lift` lives in
`dag/nodes/sec-smooth-base-change/lem-sbc-completed-quotient-cover-lift.json` and
states `CompletedQuotientCoverLift.exists_completed_cover_with_quotient_iso` (in
namespace `AlgebraicGeometry.Scheme`). It isolates henselian lifting and the
quotient base-change comparison, without depth or puncturedness.

`lem-sbc-completed-punctured-quotient-fully-faithful` lives in
`dag/nodes/sec-smooth-base-change/lem-sbc-completed-punctured-quotient-fully-faithful.json`
and states `AlgebraicGeometry.Scheme.fullyFaithful_completed_punctured_quotient`.
It isolates completion geometry, local-cohomology vanishing and the 0BM6
restriction theorem. Both nodes inherit the item's chapter, unit and blueprint
ancestor. No change record is needed because all existing interfaces are unchanged.

## Second reading by T3

1. Compared every delivered module with the repository version. Existing declaration signatures are byte-for-byte unchanged; the item adds only proof imports and proof text, while the two new modules and nodes are explicitly declared in this report.

2. Compiled all three modules with `lcompile.py --all`; compilation succeeds without warnings. The item has no remaining sorry. The two split-off theorem proofs intentionally remain named `sorry`s, with no sorry in definitions, and their declarations have the permitted source docstrings and DAG nodes.

3. Checked the split-off statements against the complete-case lifting and punctured restriction steps. Both are strictly smaller than the item, preserve all hypotheses needed by the use site, and cover edge cases such as f = 0 and empty covers. No duplicate declaration was found in the library search.

4. Reviewed the proof from the target downward. It uses the two split-off inputs, packages finite-etale morphisms in the over category, applies `FullyFaithful.preimageIso`, and obtains the projection equality from `MorphismProperty.Over.w`. No shorter existing library route was found; all original public imports remain needed for signatures.

5. Checked the DAG proof steps and unit metadata. The item node now depends exactly on the two intermediate nodes, whose proof dependencies record the geometric inputs. The unit route and `realized` entries are preserved; no target or existing definition was changed.

Changed only the report by adding this second-reading record; no Lean declarations or DAG statements were altered during review.
