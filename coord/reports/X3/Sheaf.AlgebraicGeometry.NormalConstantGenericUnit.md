## What changed

Proved `AlgebraicGeometry.Etale.isIso_unit_constantSheaf_generic_unit` with its existing
signature unchanged. The proof shows that every strict generic fibre is integral: work in
an affine open chart, obtain an ind-etale local strict-henselization algebra, apply the
existing etale-colimit domain/injectivity theorem, and localize by the base domain's
nonzero elements. Pullback and stalk isomorphisms identify this chart calculation with
the desired generic fibre. Connected constant-section evaluation and geometric stalk
conservativity then prove the unit invertible.

Added the completely proved module
`Sheaf.AlgebraicGeometry.ConstantStrictFibreStalkComparison`. It specializes the existing,
proved `exists_qcqsStrictLocalModuleComparison` to constant inverse images and checks the
coefficient equation using two adjunction units. The proof imports
`Sheaf.AlgebraicGeometry.ConstantModulePushforwardFunctoriality` with `import all` to reuse
its proved private generator equation; no definitions or statements of that module change.
The isomorphism witness is used only inside a theorem proof, never to define arbitrary data.

The main module adds proof-only imports for this comparison, the normal etale-colimit
criterion, the two strict-henselization chart APIs, the function-field API, tensor-product
localization, constant sections, and preserved sheafification. Updated its node's proof,
proof dependencies, and proof origin to follow these actual arguments.

Both delivered modules compile without warnings (approximately 9 and 5 seconds).
Explicit `#print axioms` checks on both public theorems returned exactly `propext`,
`Classical.choice`, and `Quot.sound`; neither uses a postponed upstream proof.

## Proved and sorry left

Closed the original single hole:
`AlgebraicGeometry.Etale.isIso_unit_constantSheaf_generic_unit`
(node `lem-weil-pbc-normal-constant-generic-unit`).

Also proved, without adding a hole:
`AlgebraicGeometry.Etale.constant_strict_fibre_stalk_comparison`
(node `lem-weil-pbc-constant-strict-fibre-stalk-comparison`).

The private helpers `normal_indEtale_local_domain`, `normal_strict_generic_fibre_chart`,
`normal_strict_generic_fibre_integral`, `module_connected_sections`,
`isIso_constant_unit_stalk_of_connected_strict_fibre`, and `coefficient_two_pullbacks`
are all proved. No `sorry` remains in either delivered module. Holes closed: 1;
holes added: 0. This is a proof, not a decomposition.

## No longer needed

No import or proof dependency of the repository's original item was removed: it had only
its two public statement imports and an empty proof-dependency list. Thus no existing
module is asserted to become unreachable solely because of this delivery.

Removed the trial import `WeilConjectures.ConstructibleSheaf.Restriction` and the separate
constant-generic restriction-zero/kernel-monomorphism argument: the coefficient germ
is invertible, so the local proof gives IsIso directly. The delivered route does not need
`Sheaf.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk`,
`Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology`,
`Sheaf.CategoryTheory.RightDerivedBaseChangeZeroUnit`, or
`WeilConjectures.SixFunctors.BaseChange.DerivedComparison`. In particular, it does not use
`lem-weil-pbc-unrestricted-strict-henselization-stalk`,
`lem-weil-pbc-unrestricted-strict-henselization-stalk-comparison`, or
`lem-weil-pbc-strict-local-base-change-global-homology` as proof dependencies: the
existing underived module-valued comparison already supplies what is needed.
The separate `Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk` module and its node
`lem-weil-pbc-constant-sheaf-geometric-stalk` are also unnecessary as proof dependencies:
the generic coefficient-category Point constant-stalk API already proves the needed
coefficient-germ isomorphism. Scratch attempts at a derived degree-zero bridge are not delivered.

## Where the brief, the DAG or earlier work was wrong

The original node's one-step proof did not name its dependencies or explain why the
strict generic fibre is a domain; the delivered chart/localization proof supplies both.
There is no statement dispute, signature change, forced adaptation, or change record.
The unit `sk-thm-p1` and its realized nodes are preserved.

LeanSearch returned Internal Server Error on both attempts; its search records say
UNAVAILABLE without an absence verdict. LeanFinder, Loogle, and Mathlib source search
worked, and the existing library comparison was found and reused.

`blueprint_refs.py ancestor lem-weil-pbc-normal-constant-generic-unit` returned None
because this split node's created.item is a module name. The new node records the actual
nearest blueprint ancestor from the existing item's blueprint.from,
`lem-weil-pbc-normal-constant-generic`, with the item node in its via list.

The official Stacks pages for Tags 09Z5 and 03Q9 were consulted. The local literature
checkout lacks their full chapter text. WANTED: literature/stacks-project/etale-cohomology.tex,
Tags 09Z5 and 03Q9, for the two delivered nodes. Proof origins are recorded as agent-written
categorical realizations of these sources.

## New nodes

`lem-weil-pbc-constant-strict-fibre-stalk-comparison`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-constant-strict-fibre-stalk-comparison.json`,
states the canonical module-valued direct-image stalk comparison with its constant
coefficient equation. Its statement is valid for all qcqs morphisms, including empty
strict fibres, arbitrary modules, and the zero ring; it assumes neither normality nor
connectedness. Its Lean theorem is proved, and its proof uses the existing qcqs comparison,
constant-pullback comparison, and constant-generator equations. No further work remains
on this new statement. No change records were needed.

## Second reading by X3

1. **Interfaces: pass.** Read both delivered modules in full and diffed the main module
   against the repository version. The only existing declaration is
   `AlgebraicGeometry.Etale.isIso_unit_constantSheaf_generic_unit`; its signature and
   visibility are byte-for-byte unchanged. The declaration-table check reports no
   statement change and no public-import change in that module. The comparison module
   is new. No definition, target statement, or module held by another group changes.
   There is no forced adaptation or undeclared interface change.

2. **Proofs: pass.** Independently compiled the two modules together in import order
   through `lcompile.py`, with no errors or warnings. Searched the delivered Lean for
   `sorry` and forbidden declarations: none occur. A scratch module importing both
   compiled sandbox modules printed the axioms of both public theorems: exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The algebra
   argument transports a genuine filtered etale colimit presentation, then localizes
   a domain at nonzero elements whose images remain nonzero by injectivity. The
   categorical argument cancels actual invertible coefficient-germ and section maps.
   Existential comparisons and chart maps are eliminated inside theorem proofs only;
   no arbitrary witness is used to define public data.

3. **New statements and searches: pass.** There are no split-off holes. The new,
   proved comparison is strictly one part of the argument, not a renaming of the
   original theorem: it applies to arbitrary qcqs morphisms and establishes the
   coefficient compatibility equation without asserting the unit invertible.
   Checked its word proof against the two adjunction units, germ naturality, and
   the existing qcqs comparison. An empty strict fibre gives the zero section module;
   zero modules and the zero coefficient ring cause no exception. The connected-fibre
   lemma is used only after proving the strict generic fibre integral and nonempty.
   Repeated LeanFinder searches using different wording about restriction to the
   generic point and constant coefficient germs; the hits concern normalization or
   Zariski stalks and do not supply this theorem. Loogle finds the left-adjoint
   uniqueness unit equation already reused by the generator proof. Mathlib grep and
   repository searches found no duplicate strict-fibre coefficient comparison.
   The existing `exists_qcqsStrictLocalModuleComparison` is reused, and its construction
   is not duplicated. Checked the literature route against
   [Stacks 09Z5](https://stacks.math.columbia.edu/tag/09Z5) and the canonical restriction
   construction in [Stacks 03Q9](https://stacks.math.columbia.edu/tag/03Q9).

4. **Route and pruning: pass.** The proof proceeds from the generic-point unit to
   stalk invertibility, using the already proved comparison and constant-section API,
   then the affine-chart, ind-etale, and localization calculation. Each added proof
   import supplies the theorem/API used for its corresponding step; proof imports
   are private, including `import all` for the existing private generator equation.
   The two original public imports supply the existing signature. The old node had
   no proof dependencies, so the list of old dependencies removed is empty.
   Checked `dag/units/sk-thm-p1.json`: neither the item nor its new helper replaces
   any realized statement or step, and no realized node or unit route is removed.

5. **DAG: pass.** Compared both nodes with the Lean and read their dependency records.
   In each node `proof_deps` is exactly the union of the proof steps' `uses`.
   Every dependency names the existing declaration actually used, with the private
   generator proof accounted for by its owning functoriality node. The chart,
   localization, coefficient equation, and geometric-stalk steps match the code.
   The new node has its source, word proof, search records, blueprint provenance,
   chapter/unit, creation record, and verbatim Lean statement. The main node changes
   only its proof metadata; its mathematical statement and Lean signature stay fixed.

No mathematical or Lean repair was necessary. Added this independent reading and its
search evidence to the report. The axiom-check scratch file stays outside the delivered
`lean/` tree. Confirmed holes closed: 1; holes added: 0; no modules pruned.
