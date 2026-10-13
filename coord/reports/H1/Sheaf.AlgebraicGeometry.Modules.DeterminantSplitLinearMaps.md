## What changed

Replaced the hole in `AlgebraicGeometry.Scheme.Modules.determinant_split_linear_maps_exists`
with a Lean proof from a generic local exterior tensor pairing. The original signature, declaration docstring, and
public imports are unchanged. Added proof-only imports of `ExteriorTensorLocalPairing`,
`ExteriorSheafRankWedgeZero`, and `Mathlib.Data.Finset.Piecewise`.

Private proved helpers evaluate restricted morphisms on subopens using the open-restriction
adjunction unit. They establish evaluation naturality, identity, composition, and addition;
the biproduct splitting identity; and right-inverse and kernel identities on sections.
Finite-set induction and wedge multilinearity prove lift independence from the existing
rank wedge-zero statement. Uniqueness is proved by one general locally-surjective generated induction in each
exterior factor and the tensor factor, followed by separatedness and extensionality.

Repaired all four duplicate-helper findings in the return. Removed the private
`exterior_sheafification_unit_map` and `tensor_section_map` wrappers; their call sites
use `PresheafOfModules.naturality_apply` and `tmulSection_map` directly.
Replaced `generated_sheafification_induction` and `tensor_section_induction` by the
proved private `locally_surjective_generated_induction`, which applies to an arbitrary
presheaf Q, target module sheaf E, and locally surjective morphism Q → E.val, with any
sectionwise spanning generator sets. This is a genuine generalization: E need not be
the sheafification of Q and the map need not be its unit. Both exterior factors and the
tensor factor now use the same lemma; tensor generation is `TensorProduct.span_tmul_eq_top`.

Added `ExteriorTensorLocalPairing.lean`, isolating only the exterior/tensor construction
for a supplied natural **linear** family. It assumes no splitting, exactness, local freeness,
or rank, and asserts no uniqueness or independence of arbitrary lifts. Updated the item's
DAG proof route accordingly. No existing statement, definition, or interface is changed.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.determinant_split_linear_maps_exists`
(node `lem-sc-split-determinant-linear-maps`). Its proof is complete from its imported theorem.

Added one hole:
`AlgebraicGeometry.Scheme.Modules.exteriorTensor_local_pairing`
(node `lem-sc-exterior-tensor-local-pairing`, new module `ExteriorTensorLocalPairing`).
This is a decomposition: one original hole closed, one strictly smaller construction hole added;
net zero holes. The rank wedge-zero theorem is an existing dependency, not a hole added here.
Every private helper is proved. No definition chooses data from an unproved existence assertion.

Compiled both delivery modules together using `lcompile.py --all`; no compiler warnings.

## No longer needed

Removed the original proof-only imports of `ExteriorSheafWedgeMapExists` and
`ExteriorSheafRestrictIso`. All original public imports remain; they support the unchanged statement.
The original node no longer directly needs `lem-sc-exterior-sheaf-wedge-map` or
`lem-sc-exterior-sheaf-restrict-iso`. The new generic pairing construction
also avoids them: its proof plan uses explicit exterior-algebra multiplication and the
bilinear sheafification and tensor universal properties into an open pushforward. Thus
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafWedgeMapExists` and
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso` are unnecessary on this proof path.
Other determinant modules may still need them; no claim of global removal is made.
No blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The returned version duplicated four private helpers from `DeterminantWedgeMorphismSplit`.
They cannot be imported: they are private and that module already reaches this item's
module via `DeterminantSplitComparison`, so an import would close a cycle (confirmed by
`import_direction.py may`). The repair removes two wrappers in favor of existing library
lemmas and genuinely generalizes and unifies the two induction lemmas. No other module,
existing public signature, visibility, or import is changed. The old second-reading text
was removed because it reviews the superseded delivery; a new reader must review this repair.

The exterior restriction isomorphism's existing statement only asserts `Nonempty` and
supplies no formula on pure wedge sections. It cannot alone justify transporting the
formula from the restricted scheme. The new construction theorem includes the necessary
formula explicitly. Its proof plan avoids that comparison entirely by mapping into the
pushforward of the restricted target and then inverting the adjunction unit on subopens.

The rank vanishing statement fits: no rank or freeness of the third term is required.
The uniqueness argument must use **local** generation and separatedness; global generation
of sections by wedges was not assumed. Zero ranks, empty opens, and zero rings introduce
no positivity or nontriviality assumption in the proofs or the new statement.

Searches used LeanFinder, Loogle, Mathlib grep, and repository rg. LeanSearch returned
Internal Server Error, recorded as unavailable. The imported blueprint source file is absent
from this machine; a request for its pinned raw GitHub path returned 404. The source location
and the complete determinant argument in the existing node and declaration were read;
the new node expresses that same exterior/tensor construction using open pushforward
and the existing universal properties. The proof in words spells out the scalar and unit
identities, without assuming a characterization absent from an imported statement.

## New nodes

`lem-sc-exterior-tensor-local-pairing` states the generic local exterior tensor construction
from a restriction-compatible linear family. Its module is
`lean/Sheaf/AlgebraicGeometry/Modules/ExteriorTensorLocalPairing.lean`.
It is strictly the construction step; splitting algebra, arbitrary-lift independence,
and uniqueness remain proved in the original module. The source is the Riemann--Roch
blueprint determinant paragraph, construction before independence of lifts. The node carries
all searches, the full argument, and its Lean signature. No change record is required.

An attempted full proof of the new construction remains only in
`scratchpad/PairingProof.lean`, outside the delivery. It constructs the sectionwise bilinear
map into the open pushforward, with its scalar compatibility using
`Scheme.Hom.app_appIso_inv`; completing its naturality proof runs into costly elaboration
of the exterior-presheaf scalar structures. It is not validated and is not part of the
delivery. The new module contains only the named theorem with its complete proof in words.

## Second reading by H1

1. Compared both delivered modules with the repository: the only existing public
   declaration is `determinant_split_linear_maps_exists`, whose full signature is
   byte-identical. Its original docstring and all public imports are now unchanged.
   New helpers are private; the new module contains only its documented theorem.
   No target, existing definition, public visibility, or statement was changed. Pass.
2. Compiled the two modules in import order with `lcompile.py --all`: no errors or
   warnings. Inspected every helper and the final reduction. The sole textual hole
   is `exteriorTensor_local_pairing`, listed above with its node. There are no forbidden
   declarations or hollow definitions. `localEval` inverts a specified bijection proved
   by `unit_bijective`; its object is determined. The choices used for exterior restrictions
   come from their existing unique characterization. The construction witness is consumed
   inside a theorem proof, not installed as arbitrary data in a definition. Pass.
3. Read the generic pairing statement, complete docstring argument, node, existing
   exterior wedge-map theorem, restriction isomorphism, and sheafification/tensor universal
   properties. The new statement is true: exterior multiplication followed by bilinear
   sheafification into open pushforward supplies precisely the formula and naturality.
   It contains neither splitting nor rank nor arbitrary-lift independence nor uniqueness;
   those parts are proved in the original module. It is a genuine construction subproblem,
   not a restatement of the item. Checked r=0, s=0, both zero, the empty open, and zero rings:
   the same universal properties apply. Independent LeanFinder search for bilinear natural
   transformations extending to sheafification/tensor products, Loogle search for
   `"IsLocallySurjective", "ext"`, Mathlib grep for sheafification induction/extensionality
   and image sieves, and repository searches found general ingredients but no matching
   local exterior pairing. The existing global wedge-map theorem does not handle the
   second arbitrary local linear family; the restriction iso has no pure-wedge equation.
   The generalized induction helper uses spanning sets for an arbitrary locally
   surjective map, and does not recreate either superseded special-case helper. Pass.
4. Read the proof from the final theorem downward: evaluation of the supplied splitting,
   the construction lemma, finite replacement of quotient lifts using rank vanishing,
   then three applications of local generation and separatedness. Every added import is
   used. Corrected `No longer needed` to name the two removed original proof-only imports;
   their nodes are exactly the old proof dependencies omitted by the new route. The other
   old dependencies are retained. Inspected `dag/units/sk-thm-picard-rr.json`: its existing
   `realized` statement and step arrays are empty; this delivery does not edit or bypass
   a realized unit node, and keeps the determinant step used in its Riemann--Roch route.
   The single construction hole is not closeable by a short application of the searched
   results; the unfinished scratch proof is excluded from delivery. Pass.
5. Matched both node signatures to Lean, and compared the existing node field by field:
   only its allowed proof-route fields change. Its three steps follow the Lean construction,
   independence, and uniqueness. The new node has its source, full proof, exact signature,
   statement/proof dependencies, searches, origin, creation, blueprint, chapter and unit
   fields. Its proof dependencies describe the proposed exterior/sheafification/tensor
   construction. One original hole is closed and one smaller hole is added: decomposition,
   net zero, not a sorry-free proof of the target. Pass.

Second reading changed only the inaccurate import-pruning report and restored the existing
public theorem docstring. No Lean proof or signature needed repair. A scratch copy also
checks `#print axioms` for every private helper, the original theorem, and the split theorem.
The scratch axiom check passed: every private helper and `localEval` uses only
`propext`, `Classical.choice`, and `Quot.sound` (or a subset). The main theorem and
`exteriorTensor_local_pairing` additionally use `sorryAx`, as expected for the one
listed construction hole. No other axiom occurs.
