## What changed

The existing module `Sheaf.AlgebraicGeometry.DerivedOpenTensorTestObjects` retains its
original theorem signature, public import, and definitions verbatim. Its proof obtains
an ordinary test object and applies tensor stability to the ordinary Hom hypothesis.
Both new results now have their own modules, imported privately by the target module:
`Sheaf.AlgebraicGeometry.DerivedOpenTestObject` and
`Sheaf.AlgebraicGeometry.DerivedOpenTensorHomBijective`.

The ordinary test-object theorem is proved by constructing exact extension by zero,
composing with the inverse of `Modules.overEquiv`, localizing the homotopy adjunction,
and cancelling its invertible unit. Tensor stability has the necessary assumption
that restriction on Hom(B,E) is bijective for every E. Its complete natural-language
proof is in its docstring. No data definition or existing statement changes.

## Proved and sorry left

Closed the existing hole
`AlgebraicGeometry.Scheme.exists_derivedOpen_tensorTestObject`
(node `lem-sc-derived-open-tensor-test-objects`) by a reduction.
Proved the new theorem `AlgebraicGeometry.Scheme.exists_derivedOpen_testObject`
(node `lem-sc-derived-open-test-object`) without any sorry dependency:
its axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.

Added exactly one named hole:
`AlgebraicGeometry.Scheme.derivedOpen_tensorHom_bijective`
(node `lem-sc-derived-open-tensor-hom-bijective`), in
`Sheaf.AlgebraicGeometry.DerivedOpenTensorHomBijective`. Its proof is `by sorry`.
No sorry remains in the target or ordinary-test-object module, and none is in a
definition. The tensor theorem and target use `sorryAx` through this remaining hole,
with no other axiom beyond the three permitted ones.

This is a decomposition: one existing hole closed and one new hole added in the
delivered declarations, not a completed proof of the target. The maintainer's pinned
sorry ledger determines the net in the targets' full import closure. Relative to the
first worker's sandbox, the ordinary-test-object hole was additionally closed and
the false tensor statement was replaced before delivery.

## No longer needed

No repository import was removed; no module is claimed globally pruned. The first
worker's private target imports of `DerivedOpenShriekAdjunction` and
`OpenExtensionCounitStalk` were replaced by the two intermediate modules. The
ordinary proof uses `OpenExtensionRestrictionIso` and the generic localization
adjunction directly, avoiding `DerivedOpenShriekAdjunction`.

All six old target proof dependencies cease to be direct dependencies of its
combination proof:

- `lem-sc-derived-open-restriction-adjunction-exact`
- `lem-pc-open-extension-restriction-iso`
- `lem-sc-open-extension-counit-stalk`
- `lem-pc-kflat-resolution`
- `lem-pc-kflat-derived-tensor-comparison`
- `lem-sc-derived-tensor-stalk-vanishing`

They remain needed through the intermediate nodes and their proof-plan imports.
The target's new direct dependencies are `lem-sc-derived-open-test-object` and
`lem-sc-derived-open-tensor-hom-bijective`; no part of the unit's route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first worker's `derivedOpen_tensorHom_bijective` quantified over arbitrary B
without any extension or ordinary Hom hypothesis, contrary to its own node prose.
For U empty on a nonempty affine scheme, B the structure sheaf in degree zero and
L the derived tensor unit, restriction identifies distinct zero and identity
endomorphisms of B tensor L, so the asserted map is not injective. The repaired new
statement assumes precisely the ordinary Hom property supplied by the first lemma.
This changes no existing repository declaration and requires no change record.

Both new nodes originally cited their parent as a proof dependency, creating a
circular reduction, and their recorded Lean statements contained literal Unicode
escape text rather than verbatim signatures. Both are repaired: their proofs now
follow the lower extension, adjunction, stalk, and K-flat nodes, and their signatures
are copied exactly from the delivered Lean. The parent node now records the actual
combination proof. The original report overstated completion and supplied no
usable proof docstrings for the new holes; both faults are corrected.

## New nodes

`lem-sc-derived-open-test-object` states only existence and the ordinary Hom
property. Its module is `DerivedOpenTestObject`, and the theorem is proved. It
uses exact extension by zero and its restriction isomorphism, followed by the
generic derived localization and fully faithful adjunction tools.

`lem-sc-derived-open-tensor-hom-bijective` states tensor stability of an already
given ordinary test object, with that hypothesis explicit. Its module is
`DerivedOpenTensorHomBijective`; it is the sole remaining hole. Its docstring and
node spell out the counit/Yoneda characterization of extension objects, stalk
vanishing under K-flat tensor, and the stalkwise quasi-isomorphism of the counit.
This is strictly a part of the original argument: it neither constructs an object
for arbitrary A nor asserts the target's restriction isomorphism.

The searches were run through `msearch.py` and recorded in `searches.jsonl`:
LeanFinder on left orthogonality under derived tensor, Loogle on adjunction units,
and grep on `homEquiv_unit`, derived-adjunction units and tensor/stalk terminology.
LeanSearch returned HTTP 500 and is recorded as unavailable. Mathlib's generic
Hom-equivalence and fully faithful adjunction tools are used in the ordinary proof;
no exact tensor-stability theorem was found. Independent `rg` searches of the
repository and upstream Lean found no duplicate of either specialized statement.

No change record is needed: only the original target's proof and private imports
change; the corrected intermediate statements were not present in the repository.

## Second reading by H1

1. Compared the target module with its repository version using `diff -u`.
   Its only changes are two private proof imports and the replacement of `by sorry`
   by the four-line combination proof. The existing signature, universe binders,
   all three derived-category assumptions, functor expression, tensor expression,
   public import, and original docstring are byte for byte unchanged. No existing
   definition or other repository module is adapted. Verdict: pass.

2. Compiled all three files in import order using `lcompile.py --all`: tensor
   helper 9.2 seconds, ordinary helper 21.1 seconds, target 6.5 seconds, no errors
   or warnings. Scanned the delivered sources: the only sorry is the named tensor
   theorem; there is no axiom, unsafe, opaque, implemented_by, extern, or data hole.
   Compiled a scratch copy with `#print axioms` for all three declarations: ordinary
   helper has only the three standard axioms; tensor helper and target additionally
   have `sorryAx` from the listed remaining hole. The extension functor and its
   object are constructed explicitly; chosen adjunctions and isomorphisms supply
   proof structure, not an arbitrary object chosen from an unproved existence.
   Verdict: pass as a partial decomposition.

3. Found and repaired the false arbitrary-B tensor statement. Its new hypothesis
   is exactly hBE already proved for the chosen B. For U empty, this hypothesis
   forces B to be zero, making the tensor conclusion true. For U equal to X,
   restriction is an equivalence and both Hom statements hold for every B.
   For B zero or L zero the relevant Hom sets are singletons. The ordinary object
   for A zero is the extension of zero; the empty-open case uses the same exact
   functor and unit, without an extra nonemptiness assumption. Read the source
   [Stacks 00A7](https://stacks.math.columbia.edu/tag/00A7),
   [08BT](https://stacks.math.columbia.edu/tag/08BT), and
   [06YB](https://stacks.math.columbia.edu/tag/06YB): the stalk formula, derived
   adjunction and K-flat stalk criterion support the written reduction.
   Both new lemmas are strictly smaller than the target. The ordinary one is now
   closed; the remaining tensor theorem has a complete proof docstring and node.
   Searches described above found no specialized duplicate. Verdict: pass.

4. The ordinary proof follows the shorter existing route through exact extension,
   its restriction isomorphism, Mathlib localization and Hom equivalences.
   All proof-only imports are private. The tensor helper retains the six modules
   required by its unresolved proof plan. The parent has only the two helper
   dependencies, and the No longer needed section accounts for every former
   direct proof dependency. Read `dag/units/sk-thm-picard-duality.json`: its realized
   statement and step lists are empty; this delivery does not edit the unit or
   bypass any recorded realized node. Verdict: pass, no module pruned.

5. Checked all three node records against the final Lean: new signatures are
   verbatim, module/file/declaration fields match, every proof_deps is the union
   of the steps' uses, and proof_origin describes the actual reduction. New nodes
   have source, searches, created item/group/date, blueprint origin, chapter/unit,
   status and Lean records. Their former parent dependencies are removed, so the
   new dependency graph is acyclic. The parent statement and all non-stage-3
   fields remain unchanged. Verdict: pass.

Second reading changed the tensor hypothesis, moved both new statements to their
own modules, proved the ordinary helper, restored the original target docstring,
removed the unused derived-adjunction wrapper import, supplied the remaining
hole's complete proof, repaired all node signatures and circular dependencies,
and replaced the inaccurate report. The delivery dry run passed compilation and preflight (commit 478df69f82;
review class CODEX because of the new modules/nodes and remaining named hole).
The authorized delivery push follows this successful check.
