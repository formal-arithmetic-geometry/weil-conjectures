## What changed

Proved `affineLocalization_sheafification_unit_isIso` by applying
`isIso_sheafificationUnit_app_of_affine_localizing`, introducing the local
`Module` structure by restriction of scalars and passing `hlocal`. Added the
proof-only import `Sheaf.AlgebraicGeometry.AffineLocalizingPresheafSheafification`.

## Proved and sorry left

The declaration `affineLocalization_sheafification_unit_isIso` is proved. No
new sorries were added. Holes closed: one,
`AlgebraicGeometry.Scheme.Modules.affineLocalization_sheafification_unit_isIso`.
Holes added: zero. No holes remain in the item module. The existing dependency
`AlgebraicGeometry.Scheme.Modules.isIso_sheafificationUnit_app_of_affine_localizing`
(node `lem-pc-affine-localizing-presheaf-sheafification`) remains `sorry` in the
library: this delivery consolidates duplicate interfaces and does not establish
the localization-to-sheafification argument without `sorryAx`.

## No longer needed

Removed proof imports `Mathlib.AlgebraicGeometry.Modules.Tilde` and
`Sheaf.Topology.SheafOnBasisExtends`; the proof uses the existing localizing
presheaf theorem instead. The original proof dependencies
`lem-weil-pbc-spec-module-tilde-sections` and `lem-weil-pbc-sheaf-on-basis-extends`
are no longer needed directly.

## Where the brief, the DAG or earlier work was wrong

The planned two-step localization and basis-extension argument was already
packaged as `isIso_sheafificationUnit_app_of_affine_localizing`, whose hypothesis uses the same restricted-scalar Module structure, inferred
from the restriction map rather than explicitly let-bound. The two hypotheses
are definitionally compatible; there is no stronger mathematical assumption.

## New nodes

None.

## Second reading by Q3

1. Compared both sandbox modules with repository sources. The item's sole
   existing signature is byte for byte unchanged; its public imports and
   docstrings are unchanged. The dependency module is a byte-identical local
   compilation input, not an adaptation or a new statement, and deliver3.py
   omits it from the commit. No definitions or target statements change.
2. Both modules compile locally through lcompile.py, without errors or warnings.
   The item has no sorry or forbidden declarations. A scratch copy with
   #print axioms for the item and its dependency reports only propext,
   Classical.choice, Quot.sound and sorryAx. The latter comes from the existing
   dependency theorem, not a new hole or hidden data construction.
3. No statement was split off and no new node was added. Read the existing
   dependency's signature, docstring and node: its restriction-of-scalars
   hypothesis matches hlocal, and it proves exactly the requested unit
   component. Empty opens and a=0 force zero modules; a=1 gives identity
   localization. The basis argument needs no separatedness assumption.
   Reusing an existing duplicate is permitted; no duplicate has been created.
4. Read from the item's conclusion down to the existing dependency and checked
   repository alternatives with rg, including ModuleSheafificationAffineRestriction
   and SheafOnBasisExtends. The former requires an affine-basis identification
   with an already supplied sheaf; the latter supplies a basis extension but
   not this canonical unit. The existing exact theorem is the shortest route.
   All statement imports stay public; the new dependency import is proof-only.
   Both original proof_deps are listed under No longer needed. They remain
   dependencies of the reused theorem, so this does not claim those modules
   leave the targets' import closure. The unit sk-thm-picard-coherence has empty
   realized entries; both nodes are below that unit in the same chapter and
   unit, and the reused node retains the original localization/basis route.
5. Checked the node's proof, proof_deps and proof_origin against the actual
   application and local Module construction. All other JSON fields agree
   with the repository. No new-node requirements apply.

Changed: removed the duplicate proof import; normalized the node formatting
without changing non-proof fields; corrected the report's claim of a stronger
hypothesis and made the remaining dependency sorry explicit. The proof body
was correct and was retained.
