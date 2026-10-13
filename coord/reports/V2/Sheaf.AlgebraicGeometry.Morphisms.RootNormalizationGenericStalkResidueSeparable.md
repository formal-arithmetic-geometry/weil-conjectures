## What changed

Replaced the first worker's exact restatement with a genuine degree reduction. The existing
`AlgebraicGeometry.Scheme.root_normalization_generic_stalk_residue_separable` keeps its
signature and docstring byte for byte. Its proof now obtains residue-degree divisibility,
maps the invertible group order into the base residue field, and uses the separable/inseparable
degree formula to exclude a nontrivial inseparable degree.

Added `Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationGenericStalkResidueDegreeDvd`,
containing the geometric Galois residue-degree step. Unlike the target, this theorem does not
assume invertibility of the group order and concludes degree divisibility, not separability.
The target's new private `sep_of_degree_dvd` is fully proved from Mathlib. Its proof imports
are plain imports: `Mathlib.FieldTheory.PurelyInseparable.Basic` and the new degree module.
The degree module uses the existing normalization-stalk-base-change dependency for the
localization step of its documented proof.

Removed the sandbox-only `RootNormalizationGenericStalkFormallyUnramifiedCore` module and
node. Despite their names, their Lean conclusion was exactly the target conclusion. Removed
the unchanged sandbox copy of `RootNormalizationGenericStalkMaximalIdeal`; it was not a
repair or a dependency of this reduction. No existing module other than the item is delivered.

## Proved and sorry left

Hole closed by declaration name:
`AlgebraicGeometry.Scheme.root_normalization_generic_stalk_residue_separable`.

Hole added and left, with proof exactly `:= by sorry`:
`AlgebraicGeometry.Scheme.root_normalization_generic_stalk_residue_degree_dvd`, node
`lem-sbc-root-normalization-generic-stalk-residue-degree-dvd`.

The private `AlgebraicGeometry.Scheme.sep_of_degree_dvd` has a complete Lean proof and uses
only `propext`, `Classical.choice`, and `Quot.sound`. It handles characteristic zero and prime
characteristic separately through exponential characteristic; degree dividing a positive
integer first forces finite dimensionality. A zero finrank cannot divide a positive group order.

This is a decomposition: one original hole closed and one strictly different geometric hole
added, net zero holes in the target import closure. The target still depends on `sorryAx` through
the new degree theorem and is not fully proved under the project's permitted axioms.
The removed restatement is not counted as a closed baseline hole. No hollow definitions,
axioms, unsafe declarations, extern, implemented_by or opaque declarations are present.

Both delivered modules compiled together through `lcompile.py --all`, with no warnings or
errors. A scratch copy printed axioms for the target, degree theorem and private field lemma:
only the permitted three axioms plus `sorryAx` for the two public declarations, and only the
permitted three axioms for the field lemma. The scratch copy was removed before delivery.

## No longer needed

No existing library module is pruned. The old direct proof dependency
`lem-sbc-normalization-stalk-base-change` is now used through the new degree node, so remains
transitively needed. The target node's direct proof_deps now names the new degree node.

The unused first-worker proof imports `Mathlib.RingTheory.Unramified.LocalRing` and
`RootNormalizationGenericStalkFormallyUnramifiedCore` were removed from the sandbox version.
The exact-restatement node and its maximal-ideal dependency were never in the repository and
are not delivered; this is repair of the proposed delivery, not pruning of baseline modules.

## Where the brief, the DAG or earlier work was wrong

The first worker's report said the target remained sorry, but its Lean proof instead applied
a new sorry theorem with the identical hypotheses and conclusion. The new theorem's name,
docstring and node claimed formal unramifiedness, while its Lean signature asserted residue
separability. That was a restatement, not progress, and the node also lacked required searches
and its verbatim Lean statement. The proposed reduction was rejected and removed.

The existing unramified theorem imports this residue theorem, so importing it here would indeed
create a cycle. The repaired degree route avoids this cycle. For the separability clause alone,
one can apply the Galois degree formula over the fraction field of the root DVR directly;
Abhyankar's lemma is needed for the separate ramification-index calculation, not this field
argument. The existing target docstring is preserved as API; the DAG records the actual route.

## New nodes

`lem-sbc-root-normalization-generic-stalk-residue-degree-dvd` is the local geometric
residue-degree divisibility step. Its module is
`Sheaf.AlgebraicGeometry.Morphisms.RootNormalizationGenericStalkResidueDegreeDvd`. It drops
the target's unit hypothesis and concludes that the canonical residue degree divides |G|.
Its docstring gives the DVR, torsor factor, finite integral-closure, Galois degree formula,
and residue-map identifications, citing Stacks Tags 09EB and 0307. Searches were run through
msearch.py: LeanSearch was unavailable; LeanFinder found the algebraic Galois ramification
identity, and grep found inertia degrees and local-ring finrank ingredients. None states the
scheme normalization comparison. Direct searches of lean/Sheaf and lean/WeilConjectures found
no equivalent theorem. No change record is required: existing signatures and definitions did
not change, and every added import of the existing module is proof-only.

## Second reading by V2

1. Compared every proposed module with the repository. The unchanged maximal-ideal copy
was removed. The existing target signature and docstring are byte for byte unchanged; the
parser independently confirmed the declaration statement unchanged. Verdict: pass after repair.
2. Compiled the delivered set with lcompile.py. Inspected every declaration and checked the
axioms in a scratch copy. Exactly one named public theorem remains sorry; there is no sorry
in a definition or private helper and no forbidden declaration. The target retains sorryAx
through the documented degree theorem. Verdict: valid decomposition, not a completed proof.
3. Rejected the exact-restatement helper. Read the replacement degree statement and its full
proof: finite Galois field factors have degrees dividing |G|; the DVR degree formula makes their
residue degrees divisors too. The unit hypothesis is absent, so wild characteristic is included
in this intermediate step. Empty fibres are vacuous, |G|=1 forces degree one, and no residue
field is assumed perfect. Repeated searches using residue degree, Galois ramification and
inseparable degree vocabulary, including direct library searches. Verdict: true and a strictly
separate degree step, with a full docstring proof and matching node.
4. Checked the route from the target downwards and the unit
`dag/units/sk-prop-input-spreading.json`. Its trait/tame spreading steps are unchanged; only
this node's local residue argument is reduced. No unit or chapter step is bypassed. The
old normalization-stalk-base-change dependency remains through the new node. Imports used
only for the proof are private imports, and the unused unramified/core imports are removed.
Verdict: pass; no baseline pruning is claimed.
5. Checked the target and new node against Lean. The target proof and proof_deps name the
residue-degree theorem, followed by the proved field argument; the new node names the
normalization localization step and the sourced Galois degree calculation. Its Lean statement
is verbatim and its searches, source, origin, creation, blueprint, chapter and unit fields are
present. Verdict: pass after replacing the mismatched first-worker node.

Second reading changed: removed the exact-restatement core and unnecessary maximal-ideal
copy; added the genuine residue-degree step and proved field argument; preserved the target
interface; repaired the report and DAG metadata. One hole closed, one split off, net zero.
