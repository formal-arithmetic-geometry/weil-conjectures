## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.galoisStalkActionFunctor_full`
with a complete Lean assembly proof. The public signature and both public imports
are unchanged. The private, proved `field_section_germ_ext` adapts the existing
faithfulness proof's covering-equalizer argument to individual sections. The proof
transports an equivariant morphism to a stalk function, reconstructs sections,
proves their uniqueness, proves naturality under restriction, constructs the sheaf
morphism, and verifies its image using stalk-colimit extensionality and naturality
of the given isomorphism. `ExistsUnique` is proved before choosing section values;
the choice is determined up to equality, rather than arbitrary unproved data.

Added `Sheaf.AlgebraicGeometry.FieldEquivariantGermFamilySection`, isolating local
existence for one sheaf, one etale object, and one covariant family of stalk values.
Its statement contains no functor T, isomorphism j, sheaf morphism, naturality
conclusion, or fullness conclusion. The actual combination into a global natural
transformation is proved in the item, rather than moved into the new hole.
Updated the item's proof route and added the matching new node.

Scoped backward definitional-equality options allow the stalk colimit types to
match through the module boundary. The unused-variable linter is disabled only
for the original theorem to retain its original named but nondependent proof
binders `hτ` and `hx` in the canonical-formula hypothesis; changing their names
would change the textual signature. Both delivered files compile without warnings.

Read Stacks 03QW, 03QT, and the direct proof of 04JM in the local source copy
`/home/ubuntu/c1-stacks-review/etale-cohomology.tex`. The fixed unit record
`dag/units/sk-prop-h2.json` has no realized node identifying this helper with the
unit's statement or a proof step. Its Kummer/Brauer route is unchanged.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.Scheme.galoisStalkActionFunctor_full`
(node `lem-exc-galois-stalk-action-full`). The item contains no sorry.
The private `field_section_germ_ext` is also proved directly from Mathlib.

Added exactly one hole:
`AlgebraicGeometry.Scheme.field_equivariant_germ_family_section`
(node `lem-exc-field-equivariant-germ-family-section`), in its own new module.
It has exactly `:= by sorry`, with the source and complete proof in its docstring.
This delivery is a decomposition: one upper hole closed, one local existence hole
added, net zero holes. It does not claim an axiom-free proof of the theorem.
No existing dependency theorem is modified.

Edge cases checked against the reconstruction argument: empty X has one section
by its empty cover; each finite separable component gives the usual fixing-subgroup
invariants; over separably closed K each such component is Spec K and the stalk
values are unrestricted; infinitely many components are allowed, with the sheaf
axiom giving a product and requiring no quasi-compactness. The proof allows an
arbitrary algebraically closed Omega, without an algebraicity hypothesis.
The function rho needs no additional action-law assumptions, because the canonical
formula and extension of automorphisms determine its value on every represented
germ. The assembly is compiled at the original universe max(u+1,v).

## No longer needed

Removed the direct proof imports
`Sheaf.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints` and
`Sheaf.AlgebraicGeometry.Sites.FieldSectionsStalkInvariants` from the item.
They remain planned proof imports of the new local reconstruction module, matching
its node and docstring. Their nodes
`lem-weil-pbc-etale-fibre-discrete-separable-points` and
`lem-exc-field-sections-stalk-invariants` therefore remain needed downstream.
No module or node is pruned from the full dependency closure. The new reconstruction
module is the item's only proof-dependency import. The two original public imports
stay, including the Type/TopCat action instances in EtaleFieldGsets.

## Where the brief, the DAG or earlier work was wrong

The old one-step proof plan combined local existence with the naturality and
fullness assembly. FieldSectionsStalkInvariants requires algebraic Omega whereas
the item's Omega may be transcendental; it cannot be applied directly. The new
local lemma records the algebraic-subfield and automorphism-extension argument
explicitly. The compiled assembly needs no embedding-naturality clause from that
theorem: section uniqueness and Mathlib germ restriction naturality suffice.

No statement is disputed or changed. The blueprint-ancestor helper returned None
for this created module's node, because its creation chain contains module names;
the existing node explicitly records `lem-exc-field-discrete-modules` as its
blueprint ancestor, which is retained for the new node. Searches of all blueprint
chapters for equivariant germ/section reconstruction found no duplicate statement.
LeanFinder, Loogle and grep returned supporting germ tools, no exact reconstruction
lemma; LeanSearch returned Internal Server Error, recorded as unavailable.

## New nodes

`lem-exc-field-equivariant-germ-family-section`:
`lean/Sheaf/AlgebraicGeometry/FieldEquivariantGermFamilySection.lean`.
This is only existence of a section with a specified covariant germ family.
Its proof has three parts: transport invariant-section descriptions to general
Omega, reconstruct on finite separable singleton components, and glue over the
disjoint-component cover. It preserves the existing unit and source route.
No definition, public interface, target statement, or change record is changed.

## Second reading by F2

1. I compared both delivered modules against the repository versions. The target
   theorem signature is byte-for-byte unchanged; the only existing declaration
   change is its proof and its proof-only import. The added declaration is in a
   new module and has a matching split node.
2. I compiled the added module and the item with `lcompile.py --all`; both compile
   without errors or warnings. The item has no `sorry`, unsafe feature, or hollow
   definition. The sole remaining `sorry` is the explicitly named reconstruction
   theorem, with its source and proof plan documented above and in its node.
3. The helper statement is a strict local existence result: it does not mention
   the functor, comparison isomorphism, morphism, naturality, or fullness. Its
   hypotheses and conclusion match the intended equivariant germ reconstruction,
   including the empty etale object. Searches and repository grep found no
   duplicate declaration.
4. The proof follows the node route: the item uses only the reconstruction helper;
   the helper imports the two invariant-section and discrete-fibre modules it
   needs. The removed direct imports are therefore genuinely unused by the item.
   The unit route is preserved: the helper realizes the local reconstruction step
   below the existing unit statement and does not alter the unit record.
5. The DAG proof, proof dependencies, source, and Lean declarations agree with
   the delivered code. The added node records the complete natural-language
   argument and the exact theorem statement. No target or existing public
   statement was weakened or strengthened.

I changed only the proof assembly, pruned the two now-unused direct imports from
the item, added the local reconstruction module/node, and added this second-reading
record. No statement or definition was changed.
