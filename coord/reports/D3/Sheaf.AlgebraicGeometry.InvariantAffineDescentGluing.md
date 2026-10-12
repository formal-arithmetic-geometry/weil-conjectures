## What changed

Proved `CategoryTheory.Over.DescentDatum.isEffective_of_invariant_affine_neighbourhoods`
with its signature unchanged. The proof selects an invariant affine neighbourhood at each
point, constructs the restricted transport datum, proves its naturality, identity and
cocycle by the universal property of open immersions, and proves local effectiveness
using the existing `isEffective_of_isAffineHom_fpqc` declaration.

The affine-base part is completely formalized: factor through the affine preimage of B,
construct the transport over that base, apply affine effectiveness, paste the two
pullback squares, and prove compatibility with arbitrary original test-scheme points.
The private helpers `transport_left_congr`, `exists_datum_on_invariant_open`,
`exists_datum_over_mono_base`, and `isEffective_of_affine_above_affine_open` are all proved.

Added `Sheaf.AlgebraicGeometry.InvariantOpenEffectiveDescent` for the remaining gluing
step, Stacks [Tag 0AP4](https://stacks.math.columbia.edu/tag/0AP4). This is a general theorem
about a compatible open cover whose individual data are already effective. It assumes
neither affineness nor finiteness; proving its local-effectiveness hypotheses from the
original neighbourhood hypothesis is the substantive argument completed in this item.
The theorem is not a renamed or repackaged copy of the original criterion.

Updated the assigned node's proof and proof dependencies to reflect these constructions.
The unit route is preserved: the same affine-descent and open-gluing steps are retained;
the unit record's realized entries do not impose additional nodes at this level.

Both modules compile cleanly through lcompile.py in import order. The new gluing statement
was checked against Stacks 0AP4; Stacks 0245 and 0H8K were also read. Search used LeanFinder,
Loogle, repository and Mathlib ripgrep, and LeanSearch (service returned Internal Server Error).

## Proved and sorry left

This delivery is a decomposition, not a net proof: one original hole is closed and
one new hole is added, for net zero holes closed in the target import closure.
The four private helpers add no holes.

The original module has no remaining `sorry`: its sole original open declaration,
`CategoryTheory.Over.DescentDatum.isEffective_of_invariant_affine_neighbourhoods`, is proved
from the existing affine-descent declaration and the new general gluing declaration.
All four private helpers listed above are proved without `sorry`.

Exactly one new declaration is left with `sorry`:
`CategoryTheory.Over.DescentDatum.isEffective_of_effective_open_cover`, in
`Sheaf.AlgebraicGeometry.InvariantOpenEffectiveDescent`, node
`lem-pd-effective-invariant-open-cover`. Its whole proof is `by sorry`, with its source,
a complete proof in words and blueprint tag in its docstring. The existing affine-descent
branch still reaches its own already-recorded open dependencies; none is introduced here.

Edge cases checked: the original covering selection works for empty V without requiring a
point or an inhabited index type. The new theorem explicitly includes the empty-cover case
(empty V, empty scheme over Y). A singleton cover by all of V reduces to the given local
effectiveness. Repeated opens require only compatibility, not disjointness. No separation
or finite-subset affine-neighbourhood hypothesis has been added. The local affine helper
works also for an empty affine open B. Its final transport argument constructs lifts of
both maps using the original point and its transported point, so it assumes no unwarranted
factorization of an arbitrary test scheme through B.

## No longer needed

Removed direct imports from the original module:

- `Sheaf.AlgebraicGeometry.BaseChangeConventions`: not needed by any step of this reduction.
  Its recorded node `def-pc-base-change` is removed from this item's proof dependencies;
  pullback squares and pasting use the existing CategoryTheory/Mathlib interface directly.
- `Sheaf.AlgebraicGeometry.FpqcMorphismsDescend`: the main proof now delegates its use to
  the new gluing item. Its node `lem-galois-fpqc-morphisms-descend` remains needed there,
  and its import is in that new module; it is not globally pruned.
- `Sheaf.AlgebraicGeometry.FpqcOpenSubschemeDescent`: likewise transferred to the new
  gluing item. Its node `lem-weil-pbc-open-subscheme-fpqc-descent` remains needed there.

`Sheaf.AlgebraicGeometry.AffineFpqcDescent` stays imported and its theorem is used directly.
No other planned mathematical branch is claimed pruned. Reachability elsewhere in the
library may still require BaseChangeConventions; this report only prunes this item's route.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan's phrase "restrict D" conceals two separate
constructions: restrict its total space to an invariant open, and then replace the base by
X_B -> B. Those constructions and their transport-compatibility laws are now proved.

The statement of affine fpqc descent applies to an affine morphism. An affine open U of V
need not give an affine morphism U -> X for a general non-separated X. The existing affine
base hypothesis is essential to this proof: first pass to X_B, which is affine because p
is finite. The new proof makes this intermediate base change explicit.

The literature files named by some nodes are absent on this machine, so the cited Stacks
pages were read directly. No repository file was written during proof development.

## New nodes

`lem-pd-effective-invariant-open-cover` in
`dag/nodes/sec-picard-framework/lem-pd-effective-invariant-open-cover.json` records general
compatible-open gluing, Stacks 0AP4, with its statement, proof in steps, source, search
results and exact Lean signature. Its proof dependencies are existing fpqc descent of
opens and morphisms, existing Mathlib scheme and morphism gluing nodes, and the descent
datum definition. Its module is
`lean/Sheaf/AlgebraicGeometry/InvariantOpenEffectiveDescent.lean`.
There are no definition or statement changes and no change records.

## Second reading by D3

1. **Unchanged interface: PASS.** Compared the complete delivered item with the
repository version using diff, and compared its existing theorem signature byte for
byte. The signature is identical. No definitions, existing attributes, public imports
or target statements change. The only added declarations in the item are four private
proved helpers. No change record is required. Restored the original author line and
original theorem docstring, which the first worker had unnecessarily rewritten.

2. **Proof and axioms: PASS as a decomposition.** Compiled both modules in import order
with lcompile.py. Read every proof, including all three restricted transport laws and
the final arbitrary-test-scheme compatibility argument. There is no hollow definition
or forbidden declaration. Scratch copies with #print axioms check all four helpers,
the original theorem and the new theorem. Only the standard axioms and the documented
sorryAx from remaining dependencies occur. Exactly one new theorem has a whole-proof
sorry: isEffective_of_effective_open_cover. The original hole is closed conditionally
on that theorem and the existing affine-descent branch; net hole reduction is zero.

3. **Split statement: PASS.** Independently read Stacks Tag 0AP4
(https://stacks.math.columbia.edu/tag/0AP4) and Tag 0245. The new theorem isolates
compatible invariant-open gluing after local effectiveness is supplied. It does not
assert affine effectiveness or assume the original affine-neighbourhood criterion,
so it is a strict part of the argument rather than its restatement. Its transport
compatibility implies invariance by the inclusion factorization, and the reverse
invariance follows by inverse transport. Empty total space/empty index, singleton
whole-space cover, repeated opens and arbitrary index universes cause no exception:
one can reduce the index to one selected open per point. Its docstring and node give
the complete gluing proof, including overlaps, cocycles, cartesianness and invariance.
Independent searches used LeanFinder with a new open-subobject query, Loogle for
Scheme.GlueData, and rg for IsEffective and effective-cover/gluing declarations in
both library roots and Mathlib. LocalRepresentability is a possible lower-level
gluing ingredient, not an existing proof of this descent criterion. No duplicate was
found, and completing this gluing construction is not a short missing tactic proof.

4. **Route and pruning: PASS.** The proved code performs invariant restriction,
restriction to the affine base open, affine fpqc effectiveness, pullback pasting,
and general open gluing. The unit sk-prop-jacobian-descent has empty realized lists;
its effective-descent step is retained. The No longer needed section accounts for
all three removed old proof dependencies: def-pc-base-change is replaced by the
Mathlib pullback interface, and descent of opens and morphisms are delegated to the
new gluing node rather than globally pruned. All signature imports remain public;
all proof dependency imports remain plain imports. The open gluing module retains
its planned proof-dependency imports while its proof is open.

5. **DAG agreement: PASS.** Checked the old node's permitted-field changes, the new
node's full record and exact Lean signature, the union of proof-step uses, and the
unit record. The old proof_deps are exactly datum, affine effectiveness and the new
open-gluing node; the new node records datum, open descent, morphism descent and the
two scheme-gluing ingredients. Its source, creation, blueprint, chapter, unit,
searches and Lean record are present. No statement or statement dependency changed.

Second-reading changes: restored existing authorship and theorem documentation;
made the one-closed/one-added decomposition and net-zero count explicit; added this
review and the independent search evidence. No repair to the formal proof was needed.
