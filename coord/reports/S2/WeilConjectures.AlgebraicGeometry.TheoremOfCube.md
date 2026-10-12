## What changed

Replaced both placeholders in `WeilConjectures.AlgebraicGeometry.TheoremOfCube` by complete
Lean proofs from the existing Picard declarations. All existing declaration signatures,
definitions, globalization proof, and final cube proof are unchanged. The second reading
corrected two pre-existing proof-only public imports to plain imports.
The module adds proof-only imports of `Sheaf.AlgebraicGeometry.PicardFiberTrivialityClosed`
and `Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen`. The new source-module helpers are
private and proved: tensor-dual cancellation, restriction from an open to a fibre,
geometric integrality of the product, and factorization of the residue-field morphism
through a rational point.

Added three proved bridge modules, each with one public theorem:
`PicardLocusFiberRange`, `PicardFiberTrivialityClosed`, and `CubeFiberTrivialityOpen` under
`Sheaf.AlgebraicGeometry`. The first identifies the image of a universal Picard immersion
with the trivial-fibre locus using a section. The second applies the existing universal
Picard immersion and closedness results. The third transports `picard_product_open`
through the canonical product comparison and compares the two library pullback functors
by uniqueness of left adjoints. Thus this follows the existing Stacks 0BF4 route through
0E0L, 0BDP, 0BF0 and 0BF3; it does not bypass a blueprint unit.

Added five DAG records: three for the bridge theorems and two attaching the original
source declarations, which previously had no direct `lean.module` node. Their dependency
lists follow the checked proofs. No statement or definition change record is needed.

## Proved and sorry left

Both original sorries are closed:

- `AlgebraicGeometry.isClosed_setOf_exists_nonempty_iso_preimageSnd`.
- `AlgebraicGeometry.exists_mem_nonempty_iso_preimageSnd`.

The three new public theorems are proved with no placeholders:

- `AlgebraicGeometry.Scheme.range_eq_setOf_nonempty_pullback_fiber_iso_unit`
  (`lem-sc-picard-locus-fiber-range`).
- `AlgebraicGeometry.Scheme.isClosed_setOf_nonempty_pullback_fiber_iso_unit`
  (`lem-sc-picard-fiber-triviality-closed`).
- `AlgebraicGeometry.exists_mem_nonempty_pullback_iso_unit_of_cube_fiber`
  (`lem-sc-cube-fiber-triviality-open`).

No `sorry` remains in the item or any new module; zero gaps were split off. These are
proofs from the existing staged statements, not claims that their dependencies are
already axiom-free. The four direct unresolved Picard inputs, unchanged by this delivery, are
`AlgebraicGeometry.isIso_structureSheafMap_of_proper_flat_geometricallyReduced_connected_fibers`
(`lem-sc-proper-flat-global-sections`),
`AlgebraicGeometry.Scheme.picard_diagonal_locally_closed`
(`lem-sc-picard-diagonal-locally-closed`),
`AlgebraicGeometry.Scheme.picard_locus_closed` (`lem-sc-picard-locus-closed`), and
`AlgebraicGeometry.Scheme.picard_product_open` (`lem-sc-picard-product-open`).

All four delivered modules compile together without warnings via `lcompile.py --all`.
Edge cases checked in the statements and arguments: an empty base makes the range and
closedness assertions vacuous; the section is explicit in the range lemma and ensures
invertibility of the descended module even without a rank calculation; the open lemma
allows arbitrary residue-field points and does not assume the base is reduced or
connected. Only the final existing cube theorem uses connectedness.

## No longer needed

No existing imports, DAG nodes or modules are pruned. The second reading changes the
proof-only imports `GlobalSectionsBijective` and `Modules.Rigidification` from public to
plain imports; both remain necessary for the existing globalization proof. All four original Picard proof
inputs remain necessary for this implementation. No unused proof import is left in the
new modules: an exploratory `Modules.ProjectionFormula` import in `PicardLocusFiberRange`
was removed and that module recompiled successfully. The separate
`Sheaf.AlgebraicGeometry.GeneralTheoremOfCube` is not imported or changed: its arbitrary
residue-field statement is distinct from the original rational-point source statement.
This delivery does not establish that its other uses can be removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. A search by the source module name returned
many audit mentions but no node whose own `lean.module` names this item. The two original
source declarations are now attached to their own new nodes, rather than replacing the
existing general-cube node by a declaration with a different statement.

The Picard universal property supplies a finite locally free descended module, not
immediately an invertible one. The section is used explicitly to pull its comparison
isomorphism back and prove invertibility. Also, the Picard statements use
`tensorPullback`, whereas the source cube module uses `pullback`; the natural isomorphism
between their common left adjoints is constructed and used, rather than treating these
functors as definitionally equal. Leansearch was unavailable (Internal Server Error);
leanfinder, loogle and Mathlib text searches returned no theorem that closes either
original declaration directly. Existing stated Picard results are used as intended.

## New nodes

`lem-sc-picard-locus-fiber-range`: identifies the image of the representing immersion
with fibre triviality for an invertible module in a family with a section. The proof uses
residue-field lifting along immersions, pulls the descended module back along the section,
and trivializes an invertible module over a field. Its module is fully proved.

`lem-sc-picard-fiber-triviality-closed`: applies proper-flat universal global sections,
the finite locally free Picard immersion, its closedness, and the preceding image lemma.
Its module is fully proved.

`lem-sc-cube-fiber-triviality-open`: applies the existing product Picard openness theorem
to the two base-changed factors over Z, then transports its conclusion back to the
inverse-image open in the source product notation. Its module is fully proved.

`lem-sc-cube-local-isomorphism-closed`: records the original closedness theorem, with
its unchanged signature. The proof tensors with the dual, identifies the local locus
with the fibre-triviality locus, and applies the preceding closedness and openness lemmas.

`lem-sc-cube-rational-neighborhood`: records the original rational-neighbourhood theorem,
with its unchanged signature. The third rational slice gives triviality of the residue
fibre, then product openness and tensor-dual cancellation give the required isomorphism.

The second reading added `coord/changes/theorem-of-cube-proof-imports.md` for the
public-to-plain import correction. It records both old and new imports and all 129
downstream users; no mathematical statement or definition is changed.


## Earlier second reading (a previous round; superseded)

1. Compared the entire original cube module with the repository using `diff`, and
   compared each existing declaration's parsed statement byte for byte. All five existing
   signatures and the `preimageSnd` definition are identical. The existing globalization
   and final cube proof bodies are also identical. The new helpers are private; the only
   source docstring additions attach the two original gaps to their new node IDs. No
   statement or definition change record is needed. Verdict: unchanged mathematical API.

2. Compiled all four delivered modules in import order using `lcompile.py --all`, without
   errors or warnings. Searched every delivered Lean file for forbidden declarations and
   placeholders: none occur. Scratch copies with `#print axioms` checked the three new
   public bridge theorems, both repaired declarations, the globalization theorem, and the
   final cube theorem. Their only axioms are `propext`, `Classical.choice`, `Quot.sound`,
   and inherited `sorryAx`. Thus the original two proof holes are closed, but these are
   reductions to the still-open library, not axiom-free target proofs. In particular even
   the range bridge inherits `sorryAx` from existing pullback infrastructure; the four
   Picard inputs listed above are direct inputs, not an exhaustive list of transitive
   open support declarations. No new sorry or hollow definition is delivered.

3. Zero statements are split off with sorry. Read each of the three new bridge statements
   against its node and complete docstring argument. The range bridge assumes an actual
   section and immersion: lift Spec of the residue field using the existing
   `Scheme.exists_comp_eq_of_mem_range`, evaluate the universal property, and pull back
   along the section to show the descended finite locally free module is invertible.
   `IsInvertible.nonempty_iso_unit` trivializes it over the field. The converse uses the
   structure module. The closed bridge checks properness, flatness, local finite
   presentation, and geometric integrality before applying the existing universal Picard
   immersion and closedness theorems. The open bridge checks both base changes and both
   section identities, then verifies the product comparison on all projections and
   transports the two slices, fibre, and inverse-image open. These statements are true
   reductions, not renamed placeholders. Tested empty bases (vacuous range/closedness),
   X=Y=Spec K (the open claim reduces to local triviality), arbitrary non-rational fibre
   points, and nonreduced or disconnected Z (neither is excluded). The section prevents
   the descended module from having an incorrect rank. Fresh LeanFinder search for
   descent and trivial residue-field fibres found no matching theorem; a Loogle search
   confirmed `Adjunction.leftAdjointUniq`, already used. Searched the local Sheaf and
   source algebraic-geometry modules using fibre/triviality/range/adjunction vocabulary;
   no existing theorem replaces a bridge. The existing general cube theorem requires
   connected Z and is itself sorry, so cannot replace these local statements.

4. Read Stacks [0BDP](https://stacks.math.columbia.edu/tag/0BDP),
   [0BF0](https://stacks.math.columbia.edu/tag/0BF0),
   [0BF3](https://stacks.math.columbia.edu/tag/0BF3), and
   [0BF4](https://stacks.math.columbia.edu/tag/0BF4), and the imported Lean interfaces.
   The route remains universal Picard descent, closedness, product openness, and the
   unchanged globalization proof. No shorter proved library theorem was found. Every
   proof-only new import is plain. Corrected the two old proof-only public imports
   `GlobalSectionsBijective` and `Modules.Rigidification` to plain imports; their
   declarations occur only in proofs. Other public imports supply signature types or
   predicates. The required import-visibility change record lists all 129 downstream
   users. Compiled unchanged scratch copies of AbelianVariety.Cube, Isogeny, Torsion,
   TateModule, Final, and GeometricPoints in import order against the corrected delivery:
   all six pass without warnings, so no downstream adaptation is needed. ProjectionFormula in the closed bridge supplies the required conversion
   from source-module invertibility to sheaf invertibility. All four original Picard
   inputs are used, so no dependency is pruned. Read `dag/units/sk-prop-av-cube.json`:
   its existing `realized.statement` and step list are empty; this is pre-existing
   incomplete unit bookkeeping, reported here rather than edited outside delivery scope.
   The delivery keeps the unit's general-cube route and does not bypass another unit.

5. Read all five delivered node records. The closedness node uses the closed-fibre and
   open-fibre bridges; the rational-neighbourhood node uses the open-fibre bridge after
   constructing the residue-field factorization. The range node records the two
   inclusions and section argument; the closed bridge names the proper-flat global
   sections, invertibility conversion, universal immersion, closedness, and range
   dependencies; the open bridge names global sections and product openness, with its
   explicit transport steps. Each `proof_deps` is the union of its proof-step `uses`.
   Source origins, exact Lean statements, module paths, creation and blueprint fields
   match the delivered code. The five nodes add no dependency cycle. Their mathematics
   and route agree with the cited Stacks argument. Verdict: consistent.

Changes by the second reader: corrected two proof-only public imports to plain imports and added the required
`coord/changes/theorem-of-cube-proof-imports.md` record; added the missing blueprint IDs to the three new module docstrings; clarified the report
about inherited support sorries and pre-existing empty unit realization. No proof body,
statement, definition, or node was changed.

## Second reading by S2

1. Compared the source module with the repository by `diff` and checked the raw text
   from each existing declaration keyword to `:=`: all five signatures are byte for
   byte identical. The `preimageSnd` body and both previously completed proof bodies
   are unchanged. The public-to-plain import changes have their supplied change
   record. Verdict: no accidental statement or definition change.

2. Independently compiled all four delivered modules with `lcompile.py --all`, with
   no errors or warnings. Scanned their source for forbidden declarations, kernel
   bypasses and `sorry`: none occur. Compiled scratch copies with `#print axioms`
   for all three bridge theorems and all four original public theorems. Each uses
   only `propext`, `Classical.choice`, `Quot.sound` and inherited `sorryAx`.
   Verdict: both original proof holes are closed; no new gap is delivered, and the
   target closure is still conditional on open library support.

3. Read every new bridge statement, its proof and its node. There are zero split-off
   placeholders. Checked the two range inclusions, especially invertibility of N
   obtained by pulling back along the section; the product comparison on all three
   projections; the transfer from tensorPullback to pullback; and the factorization
   of the rational-point residue-field morphism. Empty bases give vacuous loci;
   X=Y=Spec K reduces the open assertion to local triviality of a line bundle;
   non-rational fibres and disconnected or nonreduced Z require no extra hypothesis.
   Fresh LeanFinder search using immersion/descent/residue-field vocabulary found
   no replacement; Loogle confirmed the left-adjoint uniqueness theorem already
   used. Searched Mathlib and local Sheaf/source modules for range, fibre triviality,
   closedness and cube declarations. The existing general-cube statement is still
   open and assumes connectedness, so cannot replace the local bridges. Verdict:
   true intermediate arguments, not renamed copies of the original gaps.

4. Read the imported Picard interfaces and the original globalization and final
   cube proofs. The delivery follows universal Picard descent, closedness, product
   openness and globalization. Imports needed only in proofs are plain, including
   the two corrections from the earlier reading; public imports provide statement
   types or predicates. No old direct Picard dependency is eliminated. The source
   module had no directly attached node on the base. The unit's `realized` arrays
   remain pre-existing empty bookkeeping; its general-cube route is retained.
   Verdict: no additional pruning or shorter proved route was found.

5. Independently checked all five node records: each recorded Lean signature
   matches its declaration, and each `proof_deps` is exactly the union of its proof
   steps' `uses`. Read the steps against the actual proof and checked source,
   origin, chapter/unit, creation, blueprint and Lean records. The three bridge
   modules and two original declarations are correctly attached. Verdict:
   consistent with the delivered Lean and no new dependency cycle.

Changes in this reading: appended this independent review only. No proof, signature,
definition, import or node needed further repair. The earlier import-visibility
correction and its change record are retained.
