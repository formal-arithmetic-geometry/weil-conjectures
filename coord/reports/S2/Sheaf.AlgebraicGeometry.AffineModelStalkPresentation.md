## What changed

Replaced the first worker's invalid two-hole split with a real reduction of
`AlgebraicGeometry.exists_affine_model_stalk_presentation`. Its statement and
original docstring are unchanged. The new proof constructs the additive stalk
transport from two Mathlib restriction-stalk isomorphisms and the stalk of the
supplied model inverse. It transfers the existing tilde module localization,
uses Mathlib's base-change equivalence, and proves naturality on pure tensors.

New module `Sheaf.AlgebraicGeometry.AffineModelStalkTransportLinear` contains the
explicit definition `AlgebraicGeometry.affineModelStalkAddEquiv` and the strictly
smaller scalar-compatibility obligation `AlgebraicGeometry.affineModelStalkAddEquiv_smul`.
The definition uses genuine isomorphisms and no unproved existence theorem or data hole.
Both added imports in the item's module are plain proof imports. Existing public imports
are needed by the unchanged signature.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.exists_affine_model_stalk_presentation`
(node `new-e3-affine-model-stalk-presentation`). The target's proof body is complete.
Hole added and left: `AlgebraicGeometry.affineModelStalkAddEquiv_smul`
(node `new-s2-affine-model-stalk-transport-linear`). Its proof is exactly `by sorry`
and its docstring gives the source and complete argument on germs.

This is a decomposition: one existing hole closed and one strictly smaller hole
added, net zero. The final result still depends on `sorryAx` through scalar
compatibility; it is not an axiom-free completion. The discarded worker-only
`affine_model_stalk_equivalences` and `affine_model_stalk_naturality` are not counted
as baseline holes. No data is chosen from a merely existential holed theorem.

## No longer needed

None of the original proof dependencies or imports was pruned. The old dependency
`lem-weil-pbc-spec-tilde-stalk-localization` is used through Mathlib's
`tilde.toStalk` localization instance. The new proof additionally uses
`new-s2-affine-model-stalk-transport-linear`. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first worker's `affine_model_stalk_naturality` asserted naturality for *every*
family of linear equivalences. This is false. Over a field of characteristic
zero, choose identity on one nonzero module model and its negative on an
isomorphic copy. For the compatible isomorphism between the two copies, the
naturality equation changes the sign on only one side and fails on a nonzero
vector. Even with one fixed F and M, one can vary the choice with e: a scalar
model automorphism and d equal to that scalar need not commute with these
arbitrary choices. The original existential theorem asks for a compatible
family and has no such defect.

The first worker also supplied no nodes for either new hole, no docstring for
its equivalence claim, and removed the target's natural-language proof. Its node
was unchanged despite the attempted new route. All of those defects are repaired.

## New nodes

`new-s2-affine-model-stalk-transport-linear`: only scalar compatibility of the
explicitly constructed additive chart/model transport. This contains no tensor
equivalence existence or naturality conclusion. It is strictly a part of the
original first step. Sources [01BH](https://stacks.math.columbia.edu/tag/01BH)
and [01HV](https://stacks.math.columbia.edu/tag/01HV) were read. Independent
LeanFinder, Loogle and grep searches found component identities only; LeanSearch
returned Internal Server Error and is recorded as unavailable. The affine-section
presentation and tilde tensor comparison already in lean/ require different
objects/hypotheses and do not state this explicit transport scalar identity.
No change record is needed: no existing signature, definition, visibility, or
public import was changed.

## Second reading by S2

1. Compared the sandbox with the repository module. The sole existing declaration's
   signature is byte-for-byte unchanged. Its original docstring is restored.
   There are no existing definitions changed and no changes to Challenge.lean.
2. Compiled both delivered modules in import order using lcompile.py. The only
   intentional hole is the public named scalar-compatibility theorem. No axiom,
   unsafe, opaque, extern, implemented_by, or data sorry is present. The additive
   equivalence is built explicitly; the tensor equivalence comes from a localization
   property determining the map. Axiom probes check the definition, helper theorem,
   and target: only the standard three axioms plus the expected sorryAx are allowed.
3. Rejected and removed the false arbitrary-family naturality statement. The remaining
   scalar statement follows from the section/germ scalar formulas and chart ring map;
   it works for zero modules, scalar zero and one, and arbitrary model isomorphisms.
   Empty affine opens admit no hx. Searches were rerun independently; no duplicate
   assembled scalar identity was found. The lemma's source, proof docstring and node
   now accompany it.
4. The proof proceeds from the target to the existing Mathlib localization and
   restriction-stalk APIs, leaving only scalar compatibility open. Naturality is
   proved rather than assumed. All original proof dependencies are retained.
   Inspected dag/units/sk-thm-picard-duality.json and its realized fields: this
   below-unit repair does not change the unit route or its realizations.
5. Updated the original node's proof steps, proof_deps and proof_origin to match
   the construction, localization/base-change reduction and naturality proof.
   Added the scalar node with source, searches, origin, creation record, unit,
   chapter and verbatim Lean statement. Its proof_deps is the union of step uses.

Second reading changed: removed two unsupported holes (one false), restored the
original docstring, constructed the actual additive transport, proved localization,
base change and naturality, and added one valid scalar-compatibility node. This
remains a one-for-one decomposition, not net proof progress.
