## What changed

Proved `AlgebraicGeometry.Etale.isIso_strictHenselization_exchangeCube_source_stalkComparison`
in `Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeSourceStalkIso` by applying the
existing theorem
`AlgebraicGeometry.Etale.isIso_strictHenselization_exchangeCube_stalkComparisons_source`.
Its entire signature, including the chosen canonical comparison map, agrees with this
item. This is reuse of an already proved library declaration, not a new restatement
with `sorry`. The reused proof performs the formal cube transport from the existing
strict-local base-change closed-stalk theorem.

Added one private proof import:
`Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsosSource`.
Kept the two public statement imports and every binder and let of the theorem unchanged.
Scoped `linter.unusedVariables false` to the theorem because its unchanged signature
contains unused lets `M₂` and `N₂`, as does the reused theorem. No definition, interface,
target, visibility, or other module is changed. Updated the item's node proof,
proof_deps and proof_origin to the single reused source component.

Validation: local single-file compilation passes without warnings. The import-direction
check permits the reused module and reports no cycle. Its dependency node has the same
unit `sk-thm-p1`; none of that unit's realized statements or steps is bypassed.
The second reader should also run the required delivery checks.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Etale.isIso_strictHenselization_exchangeCube_source_stalkComparison`
(node `lem-weil-pbc-strict-henselization-exchange-cube-source-stalk-iso`).
No `sorry` remains in the item's module. No new holes or declarations were added,
and no intermediate was split off.

The reused existing theorem still depends on the existing hole
`AlgebraicGeometry.Etale.isIso_strictHenselization_baseChange_closedStalk`
(node `lem-weil-pbc-strict-local-base-change-closed-stalk`, module
`Sheaf.AlgebraicGeometry.StrictLocalBaseChangeClosedStalk`). This is an existing
geometric subproblem, not added or modified by this delivery; no claim is made that
the result is independent of all downstream `sorry`s.

## No longer needed

Removed these six direct proof imports:

- `Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk`
- `Sheaf.AlgebraicGeometry.StrictlyHenselianSectionsStalk`
- `Sheaf.Paper.InverseImageStalkGerm`
- `Sheaf.AlgebraicGeometry.GeometricPointFieldExtension`
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `WeilConjectures.SixFunctors.BaseChange.Square`

The item's old direct proof edges are replaced by
`lem-weil-pbc-strict-henselization-exchange-cube-stalk-isos-source`. The following old
nodes are no longer directly used by this proof:
`def-weil-pbc-cartesian-square`, `def-weil-pbc-derived-inverse-image`,
`lem-weil-pbc-geometric-point-field-extension`,
`lem-weil-pbc-inverse-image-stalk-germ`,
`lem-weil-pbc-strictly-henselian-sections-stalk`, and
`lem-weil-pbc-unrestricted-strict-henselization-stalk`.

This is direct-import and direct-edge pruning. Some removed modules remain in the
transitive closure of the reused theorem or in other target branches; no assertion
is made that these modules can all leave the global queue. The two public imports
remain necessary for the statement.

## Where the brief, the DAG or earlier work was wrong

The item duplicates the already proved source theorem in
`Sheaf.AlgebraicGeometry.StrictHenselizationExchangeCubeStalkIsosSource`, restored by
P2 in `coord/changes/strict-henselization-source-component-restoration.md`.
The DAG plan did not mention this exact existing match. Its proof and signature were
read before reuse. The source-component module does not reach this item, so reuse
creates no import cycle. No mathematical error or disputed statement was found.
The literature files cited by the existing nodes are absent from this local clone;
this delivery introduces no new geometric argument or new source-dependent hole.

## Second reading by P3

1. **Interfaces: PASS.** Read the whole delivered module and compared its diff with
   the repository version. Programmatically compared the complete existing theorem
   signature, including its internal lets and proofs of point equations: byte for
   byte unchanged. The two public imports and exposed public section are unchanged.
   Only the proof, proof imports, docstring, and theorem-local linter setting change.
   No definitions, other modules, target statements, or change records are delivered.
2. **Proof and axioms: PASS, conditional on existing lower holes.** Single-file
   compilation through `lcompile.py` succeeded without warnings (8.1 seconds).
   A scratch copy with `#print axioms` for the item and the reused theorem compiled
   (5.8 seconds); both report exactly `propext`, `Classical.choice`, `Quot.sound`,
   and `sorryAx`. The existing closed-stalk theorem is still open, as reported above.
   Scanned the delivered Lean file: no `sorry`, forbidden declaration mechanism,
   hollow definition, or new data choice. Read the reused theorem's actual proof:
   it transports the closed-stalk mate through inverse-image/homology natural
   isomorphisms and the explicit cube comparison; it does not apply this item.
3. **Split statements: PASS (none).** No new declarations, nodes, or holes are
   introduced, so there is no split-off restatement or new edge-case claim to check.
   Compared the reused theorem's signature with the item's after replacing only
   its declaration name: identical. Its proof works uniformly for degree zero,
   the zero sheaf, and empty total spaces, using functorial maps and isomorphisms.
4. **Route and pruning: PASS.** The exact existing library match is already the
   shortest reuse route. Read both statement-import modules and the existing source
   component, and searched the cube modules for other source declarations. The
   only proof import is private; both public imports supply objects in the unchanged
   signature. All six removed direct imports and all six old proof dependencies
   are enumerated in `No longer needed`; transitive pruning is not claimed.
   Read `dag/units/sk-thm-p1.json`, including all `realized` entries. Neither this
   node nor its reused source-component node replaces a realized unit step; both
   remain within the same strict-local geometric-stalk argument. The source proof
   retains the existing lower strict-local base-change subproblem.
5. **DAG: PASS.** Compared the existing node diff. Only `proof`, `proof_deps`, and
   `proof_origin` change. The sole new proof edge names the existing source-component
   node and its actual declaration. The recorded one-step application agrees with
   the Lean term; statement, statement dependencies, Lean signature, chapter, unit,
   and blueprint records remain unchanged. No new-node metadata is required.

Second reading changed only this report by adding the independent review and concrete
signature/compile/axiom evidence. No Lean or DAG repair was needed. One existing hole
is closed, zero holes are added, and zero statements are split off; this is reuse of
an existing proof with an existing lower geometric hole, not an unconditional
sorry-free proof of the target closure.
