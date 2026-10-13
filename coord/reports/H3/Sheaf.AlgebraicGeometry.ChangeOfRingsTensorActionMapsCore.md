## What changed

`Sheaf.AlgebraicGeometry.ChangeOfRingsTensorActionMapsCore` now proves the original
existence theorem from two strictly smaller construction statements. The action
construction gives only a and d. The other construction gives only a morphism
from the presheaf tensor, before extending its source through sheafification.
The original definition and theorem signature are unchanged.

The core proof constructs g using the inverse hom-equivalence of the O_Y-module
sheafification adjunction, precomposed with tensorObjIsoSheafification.hom.
It proves the section formula by cancelling the comparison isomorphism against
its inverse in tmulSection and evaluating the hom-equivalence unit identity.
Thus the sheafification-extension part of the original plan is formalized,
not left in another existence hole. Both dependency imports are proof-only.

The two new modules contain one statement each, with the original source and a
complete construction argument in their docstrings. Their statements hold for
zero modules, empty schemes/opens, identity algebra morphisms, and non-injective
algebra morphisms: the construction uses balancing and universal properties,
not division, flatness, or injectivity. The two actions need not coincide;
no equality or additional compatibility is asserted here.

All three modules compile cleanly through lcompile.py --all. The DAG route
records the action construction, presheaf comparison, and formalized extension.
The item is below the unit's realized statements/steps; no unit route changes.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.exists_changeOfRings_tensor_action_maps_core`
(node `lem-weil-pbc-change-of-rings-tensor-action-maps-core`).
There is no sorry left in the item's module.

Added two named construction holes:

- `AlgebraicGeometry.Scheme.Modules.exists_changeOfRings_tensor_action_maps_actions`
  in `Sheaf.AlgebraicGeometry.ChangeOfRingsTensorActionMapsActions`, node
  `lem-weil-pbc-change-of-rings-tensor-action-maps-actions`.
- `AlgebraicGeometry.Scheme.Modules.exists_changeOfRings_tensor_presheaf_map`
  in `Sheaf.AlgebraicGeometry.ChangeOfRingsTensorActionMapsMap`, node
  `lem-weil-pbc-change-of-rings-tensor-action-maps-map`.

This is a decomposition (one upper hole closed, two lower holes added), not a
sorry-free proof or a net reduction in the hole count. The remaining work is
constructing and descending the B-actions, and constructing the balanced natural
presheaf comparison. The adjunction extension of the latter is proved here.

## No longer needed

None. No existing imports, nodes, or modules are removed. The tensor product
and module sheafification nodes remain necessary; the two new construction
nodes also use them. No unrelated blueprint unit is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The original plan's two steps expose
only definitions as dependencies; neither supplies the specialized construction
maps as an existing theorem. Those constructions are therefore separated into
new items. Mathlib search finds the tensor and sheafification infrastructure,
not the specialized action-map or presheaf comparison existence statements.
The local checkout does not contain the cited Stacks tex assets; the new
construction arguments retain the source and detailed proof provided by the
existing core node/docstring.

An attempted direct presheaf construction reached the two O_Y-linearity checks
for the pairing eta(c tensor_B p), but unfolding the nested restricted-scalar
instances timed out. No partial proof or raised limits from that attempt remain
in the delivery. The direct construction remains isolated in the named theorem
above, with its complete balancing and naturality argument.

## New nodes

`lem-weil-pbc-change-of-rings-tensor-action-maps-actions` states existence of
only the two action maps. It realizes the first original construction step.
Its proof describes the two B-module presheaves, their sheafifications, and the
transported bilinear pairings.

`lem-weil-pbc-change-of-rings-tensor-action-maps-map` states only the presheaf
comparison on the unsheafified tensor. It realizes the balancing and naturality
part of the second original step. The extension to the sheaf tensor and its
formula are proved in the original core module. No change records are needed.

## Second reading by H3

1. **Visible declarations unchanged — pass.** Read the full repository/sandbox
   diff of ChangeOfRingsTensorActionMapsCore. The only changes are the two plain
   imports and the body of exists_changeOfRings_tensor_action_maps_core.
   ChangeOfRingsTensorActionFormulas, its body, the theorem signature, visibility,
   and existing docstrings are byte for byte unchanged. Both additional modules
   are new, and no existing declaration is retired or adapted.

2. **Proof and trust — pass as a decomposition.** Independently compiled all
   three files in import order with lcompile.py --all: clean, 2.6, 3.2, and
   8.8 seconds. A scratch module printed axioms for the definition, the core
   theorem, and both new theorems. The definition has only propext,
   Classical.choice, Quot.sound; all three theorems additionally have sorryAx,
   as expected from the two reported construction holes. The only literal
   sorries are the two public named new theorems. No forbidden declarations,
   hidden definition hole, or arbitrary witness construction is present.
   The core's existential elimination uses only the action maps and presheaf
   map whose formulas are precisely the properties required of those maps.
   Read g's proof: the tensor comparison hom cancels the inverse used by
   tmulSection, and apply_symm_apply plus homEquiv_unit evaluates the extension
   on the sheafification unit. This proves the third formula without another
   hole. It does not claim the core is axiom-clean or count the decomposition
   as net hole reduction: one closed, two added, net minus one.

3. **Split statements — pass.** The Actions statement omits g entirely; Map
   supplies only the presheaf comparison, with no extension to the sheaf
   tensor. Neither restates the full core. For Actions, commutativity of B
   makes its action on P commute with O_Y; the Under-morphism identity
   phi composed with B.hom = C.hom makes the other action O_Y-linear.
   Both actions commute with restrictions and induce the same O_Y-action
   after additive sheafification. For Map, that identity is exactly the
   balancing relation needed for c tensor_O p to map to c tensor_B p;
   naturality of the tensor restriction and unit gives a presheaf morphism.
   No flatness, injectivity, or quasi-coherence is used. Checked the zero P,
   empty scheme/open, identity phi, and non-injective phi cases: the same
   balancing and universal properties apply. Each hole has its full
   construction docstring and matching node.

   Independently searched with msearch leanfinder (canonical comparison to
   extension of scalars along a morphism of algebra sheaves), loogle
   (TensorProduct.map), and grep (changeOfRings.*tensor|tensor.*changeOfRings).
   The former gives PresheafOfModules.Monoidal tensor constructions; the
   latter two give general maps or no match, not these specialized statements.
   Also searched the project's change-of-rings modules and upstream Modules
   sources. ChangeOfRingsTensorBalancingExists constructs a map in the reverse
   direction subject to balancing of an already given f, so it cannot close
   this hole. No short specialization found that closes either hole.

   Read the primary source pages [01SB](https://stacks.math.columbia.edu/tag/01SB)
   and [0089](https://stacks.math.columbia.edu/tag/0089). 01SB supplies the
   surrounding change-of-rings application, rather than these three formulas;
   0089 supplies the induced module structure and unique sheafification
   extension. The explicit balancing arguments in the docstrings supply the
   specialized constructions, not an unstated stronger assertion of 01SB.

4. **Route and pruning — pass.** All three existing public imports are needed
   by the signatures or unchanged definition; the two new core imports are
   proof-only. The new modules' public imports supply the algebra/sheaf,
   change-of-rings, tensor-section, and presheafMonoidalCategory signature
   infrastructure. No old proof dependency disappears: the original tensor
   and sheafification nodes remain used in the extension. Thus No longer
   needed is complete with none. Read dag/units/sk-thm-p1.json and its
   realized statement/steps: this construction is below those nodes and
   retains their route. No unit, chapter, or target changes.

5. **Nodes agree — pass.** Read all three node files and compared their Lean
   statement strings with the files: exact matches. For each node, proof_deps
   equals the union of proof-step uses. The core's steps describe the actual
   obtain/action, presheaf comparison, adjunction extension, and packaging.
   The two new nodes have source, construction proof, searches, creation,
   blueprint ancestry, chapter/unit, and Lean records. The old node differs
   only in proof, proof_deps, and proof_origin; its statement is unchanged.

**Second-reader changes:** appended this independent review and clarified the
scope of the source attribution and the net hole count here. No Lean proof,
statement, definition, import, or node repair was necessary.
