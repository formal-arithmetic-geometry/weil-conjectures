## What changed

Replaced the sorry in `AlgebraicGeometry.exists_open_fibre_dense_of_generic_dense` by a
compiling proof. Added proof-only imports of
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` and
`Sheaf.AlgebraicGeometry.FlatClosedFibreInterior`; the public imports and theorem signature
are unchanged. Three private, fully proved helpers handle homeomorphism density transport,
fibre homeomorphisms, and restriction to smaller opens.

The proof constructs the nilradical subschemes of source and base and the reduced closed
complement. It proves finite type and quasi-compactness of the factor map, transports the
generic point and density, applies the existing generic-flat-finite-presentation theorem
twice, intersects the opens, transports both properties to the intersection, applies the
new flat closed-fibre interior lemma, and transports the resulting open and density back.
The nilradical subschemes, factor map and closed complement are existing explicit
constructions. No public definition chooses arbitrary data from an unproved existence
theorem; the theorem proof uses local witnesses of the generic-flatness existence results.

## Proved and sorry left

Closed: `AlgebraicGeometry.exists_open_fibre_dense_of_generic_dense`
(node `lem-sbc-generic-open-fibre-density`). No sorry remains in the assigned module.

Added: `AlgebraicGeometry.interior_fibre_closed_eq_empty_of_flat_restrict`
(node `lem-sbc-flat-closed-fibre-interior`), in its own new module, with proof exactly
`by sorry`. This is a decomposition: one upper hole closed, one lower hole added, net zero.
The new statement assumes an integral base and both flat locally finitely presented
restrictions on a supplied open. It isolates the dimension contradiction; it does not
assert the existence of the shrinking open, reduction, generic-flatness preparation,
or transport to an arbitrary nonreduced base.

Checked the statement against Tag 054X and its references 03HV and 054U. Empty sources,
empty fibres, empty closed subfamilies, the whole-base open, and zero-dimensional fibres
are included. For a whole-source closed subfamily the generic-empty-interior hypothesis
forces the generic fibre empty; flatness on the open rules out an isolated nonempty
special fibre. There is no noetherianity or separatedness assumption on the base.

Both delivered modules compile without warnings through lcompile.py --all.

## No longer needed

No existing imports or proof-dependency nodes were removed. Second reading removed the
redundant direct imports `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and
`Mathlib.AlgebraicGeometry.Properties` from the new `FlatClosedFibreInterior` module;
its remaining public imports already provide both. No module was pruned from the
target import closure. The generic flat finite
presentation node is still used twice. No component-spreading, geometric irreducibility,
field-extension density, or universal-homeomorphism base-change module is added to this
proof. The unit route is unchanged (sk-prop-normal-form has no realized binding on this node).

## Where the brief, the DAG or earlier work was wrong

The old DAG's dimension step had no named Lean dependency. The new node isolates exactly
that step. The new proof reduces the source as well as the base, and factors its map by
liftNilradical, instead of constructing the base change; the proved fibre homeomorphisms
justify this substitution. The ancestor tool returns None because created.item records a
module name. The existing explicit blueprint.from.node identifies sbc-lem-slicing and is
used for the new node. Blueprint searches for nowhere dense and fibre dimension found no
matching existing blueprint theorem. Searches of the library and Mathlib found no direct
replacement; LeanSearch returned Internal Server Error and is recorded unavailable.

## New nodes

`lem-sbc-flat-closed-fibre-interior`, module
`Sheaf.AlgebraicGeometry.FlatClosedFibreInterior`: the Tag 054X argument on a supplied open
where the ambient and closed-family maps are flat and locally finitely presented. Its
source, full proof in words, exact signature and three actual search kinds are recorded.
No statement, definition, public visibility or other existing module was changed; no
change record or forced adaptation is required.

## Second reading by V2

1. Interface comparison: read the full diff of the existing module and its node against
   the repository. The existing public theorem signature and docstring are byte for byte
   unchanged, as are its public imports. Only proof-only imports, three proved private
   helpers, and the theorem body were added. There are no definition or target changes,
   forced adaptations, or missing change records. Verdict: pass.

2. Proof and axioms: compiled both delivered files in dependency order through
   `lcompile.py --all`, including after the import cleanup, with no errors or warnings.
   Scratch copies with `#print axioms` checked all three private helpers and both public
   theorems. The helpers use only `propext`, `Classical.choice`, and `Quot.sound`; the
   upper theorem and the split theorem additionally use `sorryAx`, as expected from
   the explicitly open dependencies. The only textual sorry in this delivery is the
   whole proof of `interior_fibre_closed_eq_empty_of_flat_restrict`. No forbidden
   declarations, hollow definitions, or hidden partial-proof holes occur. In particular,
   the source/base reductions and closed complement are explicit constructions, not
   arbitrary subschemes chosen by an unproved existence statement. Verdict: pass as a
   decomposition, not an axiom-free proof of the target.

3. Split statement: independently read Stacks Tags
   [054X](https://stacks.math.columbia.edu/tag/054X),
   [03HV](https://stacks.math.columbia.edu/tag/03HV), and
   [054U](https://stacks.math.columbia.edu/tag/054U).
   After restriction to U, both morphisms have exactly the flatness and local finite
   presentation required for lifting the generic generalization and comparing fibre
   dimensions. The closed immersion gives a closed fibre subset; finite type over
   residue fields gives Noetherian finite-dimensional fibres. A generic component point
   in a nonempty interior is generic in both fibres. Its lift forces equal dimensions
   in the generic fibres, contrary to the closed subset containing no ambient component.
   Here dimension at a point is the dimension of components through that point, as in
   054U, rather than the dimension of its local ring. Checked empty X, empty Z, empty
   fibres, Z = X, U = the whole base, a field base, and zero-dimensional fibres. For
   Z = X, the hypothesis forces the generic fibre empty and flatness rules out a
   nonempty fibre on U. The lemma is true and strictly a part of the original argument:
   it requires the prepared integral base and flat restrictions and supplies no shrinking
   or reduction. Its docstring and node contain the complete source argument.
   Independent searches used LeanFinder with “contains no irreducible component in any
   fibre”, Loogle `AlgebraicGeometry.Flat, interior`, and grep for fibre dimension and
   component terms; also searched both source roots with rg. No exact replacement was
   found. `Flat.generalizingMap` covers only lifting; the existing
   `Scheme.topologicalKrullDim_lt_of_isNowhereDense` covers only dimension drop and is
   itself open. Neither closes the missing flat fibre-dimension comparison in a few
   minutes. Verdict: pass; the one split hole remains.

4. Route and pruning: followed the Lean proof from the unchanged target downwards.
   The homeomorphisms identify ordinary fibres explicitly, so reducing the source as
   well as the base is valid without a base-change construction. The generic-flat
   finite-presentation declaration is used twice; restricting to the intersection is
   proved using locality and the restriction isomorphism. The range/complement identity
   converts density to precisely the new lemma's interior hypothesis and back.
   Existing proof_deps contained only `lem-sbc-generic-flat-finite-presentation`, which
   remains used; thus no old dependency belongs in the pruning list. The unit
   `sk-prop-normal-form` has empty realized statement/step lists; no realized route is
   bypassed. All added imports are proof-only in the existing module. Removed two
   redundant direct imports from the new module. Verdict: pass, no closure modules pruned.

5. DAG agreement: checked both nodes in full. The upper node's four steps follow the
   reduction/homeomorphism preparation, two generic-flatness applications, interior
   persistence, and image-open transport actually written in Lean. Its proof_deps are
   exactly the existing generic-flat node and the new flat-interior node. The new node's
   statement and verbatim Lean signature agree, its chapter/unit and blueprint ancestry
   agree with the parent, its source and recorded searches are present, and its status,
   created, lean_audit, and Lean record satisfy the stage-3 new-node fields. Its proof
   is the remaining dimension argument and has no falsely claimed proved dependency.
   Verdict: pass.

Changes in second reading: removed two redundant imports from the new module, clarified
that local existential witnesses are not hollow public definitions, and recorded this
independent review. No theorem signature, proof body, definition, or node was changed.
Hole accounting remains one upper hole closed and one lower hole added, net zero.
