## What changed

The original signature of
`AlgebraicGeometry.exists_basic_ideal_wedge_selfTor_coordinates` is unchanged. Its proof
now combines two strictly smaller intermediate statements, rather than assuming
compatibility of the fully conjugated chart maps.

Added `Sheaf.AlgebraicGeometry.SelfTorAffineSection`: its three constructions use the
actual ideal-sheaf inclusion, the exterior alternating map on cotangent classes, and
the tilde adjunction unit followed by chart restriction, open pushforward and the
canonical tensor-pullback unit. No object is chosen from an unproved existence claim.
Its `AlgebraicGeometry.selfTorAffineSection_map` is proved by composing the three
naturality equations.

Added `Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChart`: source coordinates on one
chart, with their top-component formula on actual ideal tuples. This contains no
derived category, Tor module, second chart or localization condition.

Added `Sheaf.AlgebraicGeometry.SelfTorTargetBasicLocalization`: target coordinates and
localization of explicit algebraic Tor elements. This contains no exterior sheaf
source coordinate and no equation on wedges of pulled-back ideal sections.

The original module proves restriction of exterior wedge sections and the coordinate
restriction formula using naturality of the original pullback unit and the source
coordinate. It rewrites both source coordinates, moves the algebraic comparison past
restriction by naturality, applies the proved affine-section map formula on both
charts, and finishes with the target localization equation. Thus the assembly,
including the original pullback unit rather than a substituted adjunction, is proved.
The DAG copy records this actual route. No existing definition, statement, signature,
visibility or unit route was changed.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.exists_basic_ideal_wedge_selfTor_coordinates`
(node `new-u4-self-tor-basic-ideal-wedge-coordinates`). Its proof is complete from the
two new intermediate theorems. This is a decomposition, not a proof free of sorry in
its dependency closure: one hole closed, two holes added.

The delivery adds exactly these two holes, each in its own new module and with proof
exactly `:= by sorry`:

- `AlgebraicGeometry.exists_selfTor_conormal_wedge_chart`
  (node `new-t2-self-tor-conormal-wedge-chart`).
- `AlgebraicGeometry.exists_selfTor_target_basic_localization`
  (node `new-t2-self-tor-target-basic-localization`).

`AlgebraicGeometry.selfTorAffineSection_map` is proved. The two private helpers in the
original module, `exterior_section_map` and `conormal_wedge_coordinate_restrict`, are
proved. No sorry remains in the original module or in any definition.

The explicit affine-section module, both remaining statements, and the assembly
compile through lcompile.py. The deliver3.py dry run printed OK: compilation and preflight passed, except for the
second reading reserved for the second reader. Nothing was pushed.

## No longer needed

Removed the original module's proof imports of:

- `Sheaf.AlgebraicGeometry.AffineOpenKernelConormalSections`, node
  `lem-sc-affine-open-kernel-conormal-sections`. The source construction instead uses
  `Scheme.Modules.affine_conormal_sections`, which directly treats i.ker.toModules
  with its original unit and supplies quasi-coherence. The open-kernel transport
  branch is unnecessary for this route. This is the actual pruning.
- `Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification`, node
  `lem-sc-affine-quotient-resolution-sheafification`. This is still required by the
  target intermediate statement's proof plan and is imported there; it is not
  pruned from the resulting dependency closure.
- `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso`, node
  `lem-sc-exterior-sheaf-restrict-iso`. This is still required by the source
  intermediate statement's proof plan and is imported there; it is not pruned
  from the resulting dependency closure.

The algebraic `selfTorConormalComparison` and its normalization are still needed.
No unit statement or realized step was bypassed. The new source node uses
`lem-weil-pbc-affine-conormal-sections` as a generic conormal tool, not as a replacement
for a step of another unit.

## Where the brief, the DAG or earlier work was wrong

The DAG's three imports do not themselves state a comparison of algebraic Tor with
the fixed derived self-tensor, nor a source exterior coordinate preserving explicit
associated sections. Their docstrings describe these constructions, but their Lean
signatures do not supply them. The two intermediate statements isolate exactly these
missing pieces. The stronger self-Tor coordinate modules cannot be used as shortcuts:
they import this module transitively.

Mathlib search was performed through msearch.py (LeanFinder, Loogle, grep and
LeanSearch), and the library and imported blueprint were searched. LeanFinder found
ideal-quotient localization and associated constant-section tools, not the required
normalized coordinate square. LeanSearch returned HTTP Internal Server Error and is
recorded as unavailable. The explicit section helper is constructed from the standard
adjunction units rather than an arbitrary witness. Stacks Tags 01R3, 09PQ, 06YH and
0096 were read online; the cited local blueprint/source trees are not present here.
The unit record itself was read. A further source-proof search found the exterior
stalk comparison and open-restriction comparison, but no general associated-exterior
module or exterior-localization interface. The existing free-chart comparisons require
local freeness, which this statement does not assume. Thus they do not close the
remaining source construction. No source statement was changed.

Edge cases were checked before stating the intermediates: n=0 is the empty wedge and
quotient unit; the zero ideal has zero positive exterior powers; I=A and empty charts
have zero sections; f=0 gives an empty smaller chart and f=1 the identity localization.
Neither new theorem requires regularity, finite generation of the ideal, or Koszul
acyclicity. The basic localization theorem only uses tuples defined on U.

## New nodes

`new-t2-self-tor-affine-section`, in
`dag/nodes/sec-picard-framework/new-t2-self-tor-affine-section.json`, records the
explicit affine section, ideal element and conormal wedge constructions and the
proved naturality theorem. No hole is added by this node.

`new-t2-self-tor-conormal-wedge-chart`, in
`dag/nodes/sec-picard-framework/new-t2-self-tor-conormal-wedge-chart.json`, records
only the normalized source coordinates on one affine chart. Its proof follows
01R3 and the exterior/associated-sheaf universal properties, using the existing
conormal sections and exterior restriction statements.

`new-t2-self-tor-target-basic-localization`, in
`dag/nodes/sec-picard-framework/new-t2-self-tor-target-basic-localization.json`,
records only the target-resolution construction and its principal-localization
identity on explicit algebraic comparison images. Its proof is the augmentation,
Koszul normalization and homotopy-independence calculation of the original steps
1 and 3. There is no source coordinate in this assertion.

No change record or forced adaptation is needed.

## Second reading by T2

1. **Visible declarations and statements.** Compared the delivered item with the
repository version and checked all new declarations and imports. The original target
signature is byte-for-byte unchanged; no existing declaration was weakened or given
additional hypotheses. The three added modules contain only the constructions and
intermediate statements described in this report.

2. **Compilation and proof status.** Compiled all four sandbox modules with
`lcompile.py --all`; they compile successfully. The original target, the affine
section naturality theorem, and both private helpers are proved. The only remaining
`sorry`s are the two explicitly named split-off intermediate theorems, each with a
matching DAG node and a complete source/proof docstring. No definition contains a
`sorry`, and no forbidden declaration form was introduced.

3. **Truth and strength of split statements.** Checked the edge cases recorded above
(empty wedge, zero ideal, empty and identity basic opens) and read each split statement
against its Lean type. The conormal chart statement contains only source coordinates;
the target localization statement contains only target algebraic Tor images. They are
strictly smaller than the original target and do not restate it.

4. **Proof route and pruning.** Read the proofs and DAG `proof_deps` against the actual
Lean route. The target proof uses the two split statements, exterior-section
naturality, and `selfTorAffineSection_map`; the removed open-kernel import is genuinely
unused. The remaining quotient-resolution and exterior-restriction dependencies are
retained in the split modules where their proof plans require them. The unit route and
realized path are unchanged.

5. **Search and duplication check.** Searched the repository and recorded Mathlib
searches for existing declarations with the same constructions; no duplicate theorem
or definition was found. Imports visible to downstream modules are intentional and
minimal for the new public statements.

I changed only this report, adding this second-reading record; no Lean proof or
statement required repair.
