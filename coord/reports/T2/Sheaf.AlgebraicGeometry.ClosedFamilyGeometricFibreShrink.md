## What changed

Proved `AlgebraicGeometry.exists_open_closed_family_geometric_fibre_shrink` from one
new geometric shrinking theorem. Constructed each closed subscheme explicitly as
`Scheme.IdealSheafData.vanishingIdeal` followed by `subscheme`, rather than choosing
scheme data from an existence theorem. Three proved private helpers identify the
geometric fibre of each closed subscheme with its inverse-image trace in the ambient
geometric fibre. The proof uses pullback pasting isomorphisms, the range formula for
a pullback projection, and an embedding's homeomorphism onto its range. It then
intersects the finitely many shrinking opens. The original public signature,
visibility, docstring, and public imports are unchanged. Added proof-only imports
of `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and
`Sheaf.AlgebraicGeometry.GenericGeometricIrreducibilityShrink`.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.exists_open_closed_family_geometric_fibre_shrink`
(node `lem-sbc-closed-family-geometric-fibre-shrink`). There are no sorries left in
the item's module or in its three private helpers.

Added exactly one hole:
`AlgebraicGeometry.exists_open_generic_geometric_irreducibility_shrink`
in `Sheaf.AlgebraicGeometry.GenericGeometricIrreducibilityShrink`
(node `lem-sbc-generic-geometric-irreducibility-shrink`). Its whole proof is
`by sorry`; its docstring and node carry the source argument. This is a
decomposition with net holes closed minus added equal to zero, not a sorry-free
proof of generic geometric irreducibility. The new theorem is the one-scheme
shrinking step: it has no closed subsets, ambient trace tests, or finite family.
The closed-subscheme comparison and simultaneous intersection are proved here.

Edge cases checked: an empty index family gives top as its finite infimum;
a closed subset with empty generic trace cannot satisfy the generic irreducibility
hypothesis; a generic point binder excludes an empty base. The comparison holds
for every field extension, including inseparable ones, and carries nonemptiness
because `IsIrreducible` and `IrreducibleSpace` both include it.

## No longer needed

None. No existing import, node, or module was removed. The node previously had no
proof dependencies. The new dependency isolates its geometric shrinking step;
the finite-family and closed-subscheme glue now depend only on Mathlib.

## Where the brief, the DAG or earlier work was wrong

The parent node supplied no named Lean dependencies for its substantial geometric
shrinking argument, so the least delivery cannot be a direct assembly of existing
planned declarations. The new node makes this missing step explicit. No statement
was changed or disputed. The unit's route is preserved.

The proved upstream ring theorem
`exists_ne_zero_forall_isIrreducible_fiber` requires a noetherian domain and concludes
ordinary irreducibility; it is not a direct replacement for arbitrary-base geometric
shrinking. LeanSearch was unavailable, and the public Loogle service did not know
the geometric irreducibility identifier. These outcomes are recorded honestly in
the search metadata. Stacks Tag 0559 was read directly and confirms the new
statement without a noetherian hypothesis.

## New nodes

`lem-sbc-generic-geometric-irreducibility-shrink`, in
`dag/nodes/sec-smooth-base-change/`, states the geometric shrinking portion of
Tag 0559 for one finite type morphism. Its module is
`Sheaf.AlgebraicGeometry.GenericGeometricIrreducibilityShrink`. It inherits the
parent's chapter, unit, and blueprint ancestor. No change record is needed:
existing signatures and externally visible imports were not changed.

## Second reading by T2

1. Compared every delivered existing module and node with the repository using
   `diff`. The existing theorem signature, visibility, docstring, and public imports
   are byte-for-byte unchanged. Only its proof, private proved helpers, proof-only
   imports, and the permitted node proof fields change. There are no definitions
   added or altered and no change record is required. Verdict: pass.
2. Compiled both modules in import order with `lcompile.py --all`; both compile
   without errors or warnings (2.4 and 3.3 seconds). Read every proof and scanned
   the files for forbidden declarations. A scratch copy with `#print axioms` shows
   only `propext`, `Classical.choice`, and `Quot.sound` in all three private helpers;
   the item and its one new dependency additionally use `sorryAx`, exactly for the
   reported named hole. No hidden sorry or hollow definition occurs. Verdict: pass.
3. Read Stacks Tag 0559 directly: its finite-type theorem over an irreducible base
   with a generic point is exactly the new statement, with no noetherian assumption.
   Checked the source argument against the new docstring and node. Empty source
   fibres cannot meet geometric irreducibility; over a field base the statement
   specializes to the assumed generic fibre; nilpotents and inseparable field
   extensions are handled by universal homeomorphisms. For the parent, an empty
   family gives top and an empty closed trace violates its hypothesis. Repeated
   LeanFinder, Loogle, and grep searches using fibre irreducibility and dense-open
   wording, and searched the project and upstream sources. No direct replacement
   was found. The proved upstream ring theorem needs a noetherian domain and
   asserts ordinary fibre irreducibility, so it cannot directly discharge this
   arbitrary-base geometric statement. The new hole isolates the geometric
   shrinking step; the closed-subscheme comparison and finite intersection are
   independently proved and constitute a genuine reduction. Verdict: pass as a
   decomposition, with net zero holes closed.
4. Read the proof from the target downward. The constructed vanishing-ideal
   subschemes avoid arbitrary scheme witnesses from unproved existence. Pullback
   pasting and range identities transfer exactly the ambient trace condition,
   including nonemptiness, for every field map. Both proof-only imports are used;
   the public imports supply the existing signature. The old node had empty
   `proof_deps`, so `No longer needed: None` is complete. Read
   `dag/units/sk-prop-normal-form.json`: its realized fields are unchanged and no
   unit statement or step is bypassed. Verdict: pass.
5. Checked both JSON nodes against the Lean declarations and proof. The parent
   dependency union is exactly the new shrinking node; its remaining steps match
   the proved helpers and intersection. The new node has the required source,
   natural-language proof, search records, creation and blueprint provenance,
   chapter/unit, and verbatim Lean signature. Verdict: pass.

Second reading changed only this report by adding the independent review. No
Lean or DAG repair was necessary; the remaining geometric shrinking theorem is
substantial and cannot be closed in a few minutes by the available declarations.
