## What changed

Replaced the sole proof hole in
`lean/Sheaf/AlgebraicGeometry/EtaleSectionsRestrictionSquare.lean`, in
`AlgebraicGeometry.Etale.sectionsComparison_restriction_square`, by a complete proof.
The statement, visibility, docstring and imports are unchanged.

The proof follows the existing node's three steps. It factors the derived adjunction unit
using `Adjunction.derivedη_fac_app`, identifies the composite right-derived unit with the
sections unit using the defining factorization identities for
`Functor.rightDerivedFunctorCompIso'`, and uses naturality to prove the homotopy-category
restriction square. The termwise restriction is identified using
`Adjunction.mapHomotopyCategory_unit_app_quotient` and
`Functor.mapHomotopyCategory_map`. Finally,
`Functor.mapDerivedCategoryFactorsh_hom_app` and the quotient comparison transport the
square to complexes. Cancellation is applied only to the image of the exact inverse-image
localization isomorphism. Neither sections comparison is assumed invertible.

The original proof plan and proof dependencies still describe this proof, so no node edit
is necessary. No definitions, statements, other modules or public imports were changed.

## Proved and sorry left

Closed one of one existing holes:
`AlgebraicGeometry.Etale.sectionsComparison_restriction_square`
(node `lem-weil-pbc-sections-comparison-restriction-square`).
There are no remaining holes in the module and no holes added elsewhere; zero split off.
This is a full proof, not a decomposition.

The final single-file compile through `lcompile.py` succeeded without warnings.
A temporary `#print axioms` check reported exactly `propext`, `Classical.choice`, and
`Quot.sound`; the check command was removed from the delivered file.
All Lean lines are at most 100 characters. The proof makes no boundedness, injectivity,
nonemptiness or etaleness assumptions, and applies to zero and unbounded complexes and
arbitrary morphisms as stated.

## No longer needed

None. No imports were removed, and no planned dependency nodes or modules were bypassed.
The sole existing import
`WeilConjectures.SixFunctors.Etale.Derived.GlobalSections` remains necessary for the
statement and supplies all categorical infrastructure used by the proof.
No new proof imports were added. The unit record `sk-prop-h2` realizes no statement or
step through this node; its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error was found. The existing categorical infrastructure
suffices for all three planned steps. Broad simplification after unfolding quotient
comparisons did not consistently normalize category endpoints; explicit `erw` steps
resolve the definitional equalities without changing any interfaces or library definitions.

## Second reading by N1

1. **Interface unchanged: pass.** Compared the sole delivered Lean module against the
   repository with `diff -u`. Only the body of
   `AlgebraicGeometry.Etale.sectionsComparison_restriction_square` changes; the signature,
   visibility, docstring, definitions in its statement, and public import are byte for byte
   unchanged. There are no other delivered modules or change records.
2. **Proof and axioms: pass.** Independently compiled the edited module with `lcompile.py`
   without errors or warnings. Compiled a scratch copy with `#print axioms` for the theorem:
   exactly `propext`, `Classical.choice`, and `Quot.sound`. Searched the delivered Lean for
   `sorry`, forbidden declaration forms, foreign implementations and kernel-check bypasses;
   none occur. Read the factorization, composition-unit identity, naturality square and final
   transport. Both cancellations concern isomorphisms; no sections unit is cancelled.
3. **Split statements: pass (none).** No declarations, definitions, nodes or proof holes are
   added. The proof works for arbitrary scheme morphisms and arbitrary cochain complexes:
   no step requires a complex to be nonzero, bounded or injective, or a scheme to be nonempty.
4. **Route and pruning: pass.** Searched the library for restriction-square, derived
   comparison and composition-unit identities, and read Mathlib's derived adjunction
   factorization and the library's right-derived composition definitions. The proof already
   uses these generic results directly. No shorter existing replacement was found; related
   triangle naturality imports this item and cannot be used here. The sole public import
   supplies objects in the statement and remains necessary. All three old dependency nodes
   remain used through their inverse-image, derived-sections and adjunction infrastructure;
   no nodes or modules are pruned. Checked `dag/units/sk-prop-h2.json`: this node realizes
   none of its statement or steps, and no unit route is bypassed or changed.
5. **DAG agreement: pass.** Read the item's node and its three dependency records. The
   existing three proof steps and `proof_origin` describe exactly the Lean factorization,
   naturality and quotient transport used here; `proof_deps` remains appropriate. No node
   edit or new node is needed.

Second-reading change: removed the unused local abbreviation `FC` from the proof. No
mathematical repair was needed. Independently confirmed one hole closed, zero holes added,
zero statements split off, and no imports or dependency modules pruned.
