## What changed

Replaced `AlgebraicGeometry.Scheme.smooth_connected_generic_geometry`'s sorry
with a composition of its normal-integrality core and its common-generic-stalk
part. The existing declaration's signature, docstring and public imports are
unchanged. The two helper modules are imported only for the proof.

The second reader proved `smooth_connected_generic_geometry_stalk_iso` using
Mathlib: openness gives dominance of the generic-fibre projection; base change
of a preimmersion gives surjectivity on stalks; the generic stalks are fields,
so their map is bijective. Stalk naturality gives the compatibility equation.
The new helper needs smoothness and the three integral structures, but neither
normality nor geometric connectedness. Its statement no longer includes those
unused hypotheses, and its geometric-connectedness import was removed.

## Proved and sorry left

Closed existing hole:
- `AlgebraicGeometry.Scheme.smooth_connected_generic_geometry`
  (node `lem-sbc-smooth-connected-generic-geometry`), by decomposition.

Proved new helper, with only propext, Classical.choice and Quot.sound:
- `AlgebraicGeometry.Scheme.smooth_connected_generic_geometry_stalk_iso`
  (node `lem-sbc-smooth-connected-generic-geometry-stalk-iso`).

Added and remaining hole:
- `AlgebraicGeometry.Scheme.smooth_connected_generic_geometry_core`
  (node `lem-sbc-smooth-connected-generic-geometry-core`). Its complete
  natural-language proof is in its docstring.

One original hole is replaced by one strictly smaller geometric hole: this is
a decomposition, not a sorry-free proof of the original theorem. The original
theorem still has sorryAx through the core. The stalk helper's former proposed
hole was closed by the second reader. No data definition or arbitrary witness
chosen from an unproved existence theorem was added. Local source-hole net
against the repository version is 0; the ledger determines closure figures
against its pinned baselines.

## No longer needed

No existing library import or old proof-dependency node is removed: the original
node had no proof_deps. No existing module is claimed pruned. The proposed
stalk helper's `Mathlib.AlgebraicGeometry.Geometrically.Connected` import and
normality/geometric-connectedness hypotheses are no longer needed. Its new
`UniversallyOpen` import is private to the proof. The parent now depends on the
core and the proved stalk helper; the unit route remains unchanged.

## Where the brief, the DAG or earlier work was wrong

The first report described both helper theorems as open and called the original
proved without distinguishing decomposition. The second helper has a short
Mathlib proof. The first submission also had two letI style warnings, empty
search histories, placeholder Lean signatures, incomplete helper proof
explanations, and no update of the parent's proof dependencies. These are fixed.

Existing source results were checked: `Sheaf.RingTheory.SmoothNormalRing`
proves affine normality ascent, and `WeilConjectures.AlgebraicGeometry.Regular`
contains connected regular locally noetherian integrality. Neither states the
full remaining geometry core over a possibly nonnoetherian base. No duplicate
of either was introduced. LeanSearch was unavailable; its actual failure is
recorded alongside successful LeanFinder, Loogle and source-grep searches.

## New nodes

`lem-sbc-smooth-connected-generic-geometry-core`: the normality/integrality part
of the original geometric argument, excluding the common function field.
It carries a self-contained statement, exact Lean signature, source, complete
proof explanation and actual search records. Its one named theorem is open.

`lem-sbc-smooth-connected-generic-geometry-stalk-iso`: the common-generic-stalk
part, now proved from Mathlib with fewer assumptions. Its node follows the
actual dominance/preimmersion/field-bijectivity/naturality proof. Both nodes
belong to the original chapter and unit. No change record is required because
no existing statement or definition changes.

## Second reading by G2

1. Compared every delivered module with the repository. Only the existing
   item's proof and two plain imports differ; its declaration signature is
   byte-for-byte unchanged. Both other modules are new, and no other module
   is adapted. Verdict: pass.
2. Compiled all three files locally in import order with lcompile.py, without
   errors or warnings. Scanned all delivered Lean for forbidden declarations
   and checked #print axioms in a scratch copy. The proved stalk helper uses
   only propext, Classical.choice and Quot.sound. The core and original item
   additionally use sorryAx, exactly through the reported one named theorem.
   No definition, axiom, unsafe, opaque, implemented_by or extern was added.
   Verdict: pass as a partial decomposition.
3. Checked the new statements and sources and searched Mathlib and the local
   library with alternate vocabulary. For the core, an empty generic fibre
   is excluded by nonempty C and openness; a disconnected smooth fibre cannot
   pass geometric connectedness; a nonnoetherian base does not affect local
   noetherianity of the field fibre. Connected normal locally noetherian
   schemes have disjoint open components, hence are integral when nonempty.
   The stalk helper assumes integrality already and is strictly the remaining
   function-field clause; its proof certifies its strengthened statement.
   Normality and connectedness assumptions unnecessary there were removed.
   Neither helper restates the whole original conclusion. Verdict: pass.
4. Read the parent node, its empty old proof_deps and
   dag/units/sk-prop-input-spreading.json (whose realized fields are currently
   empty). The decomposition stays inside this lower-level geometry argument
   of the extension step; no unit step or cited-unit route is bypassed. All
   original public imports serve the unchanged statement; both added imports
   serve the proof. The new stalk proof uses only Mathlib. No old dependency
   needs listing as pruned. Verdict: pass.
5. Updated the parent proof, proof_deps and proof_origin to the actual
   composition. Replaced placeholders by exact Lean signatures; made both
   new node statements self-contained; recorded actual searches, sources,
   blueprint origin and chapter/unit; updated the stalk node to its proof.
   The remaining core node explicitly describes the unformalized argument.
   Verdict: pass.

Second-reading repairs: closed the stalk-isomorphism hole, removed its unused
normality and geometric-connectedness hypotheses/import, fixed both letI
warnings, expanded the core's proof docstring, repaired node metadata and
search records, updated the parent's proof route, and corrected the report's
hole accounting. All edits are in the sandbox.
