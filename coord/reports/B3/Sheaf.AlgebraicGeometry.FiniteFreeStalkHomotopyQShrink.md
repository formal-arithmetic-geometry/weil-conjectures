## What changed

Replaced the first worker's complex-level `exists_restrict_eq_of_stalk` helper:
it carried essentially the whole original argument and its docstring omitted the
proof. The delivered new module `Sheaf.AlgebraicGeometry.FiniteFreeStalkMapEquality`
states `AlgebraicGeometry.Scheme.Modules.exists_restrict_eq_of_pullback_eq` for
ordinary sheaf-module morphisms with finite free source and arbitrary target.
Its docstring gives the finite-generator argument and the closed-point stalk
comparison. No object is chosen from an unproved existence theorem.

The original theorem now unpacks `Homotopy.comm` in degree i, simplifies the two
zero differentials, identifies its source with the restricted free sheaf by
`singleObjXSelf`, and applies the ordinary map-equality lemma. It then proves
chain-map equality with `hom_ext`: the degree-i component is the local equality;
every other component has zero source by `isZero_single_obj_X` and `map_isZero`.
Finally it constructs `Homotopy.ofEq`. The existing signature and docstring are
unchanged. The new module is imported privately, since only the proof needs it.

Removed `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` and replaced it
with the smaller Mathlib imports `AlgebraicGeometry.Modules.Sheaf` and
`Algebra.Category.ModuleCat.Sheaf.Free`, which provide the actual signature API.
Updated the original DAG proof and the new node to agree with this reduction.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.exists_shrink_homotopy_Q_inside_of_stalk`
(node `lem-pc-finite-free-stalk-homotopy-q-inside`).

Hole added: `AlgebraicGeometry.Scheme.Modules.exists_restrict_eq_of_pullback_eq`
(node `lem-pc-finite-free-stalk-map-eq-shrink`, new module
`Sheaf.AlgebraicGeometry.FiniteFreeStalkMapEquality`). This is the only textual
sorry in the delivery, in a named public theorem with a complete proof docstring.

This is a decomposition: one original hole closed, one lower hole added, net zero.
The original theorem still depends on sorryAx through this lower theorem and is
not axiom-closed. Both declarations' explicit #print axioms checks show exactly
propext, Classical.choice, Quot.sound and sorryAx. No other new holes are added.
The rejected first worker helper is absent from the delivered modules.

## No longer needed

Removed imports: `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` and `Sheaf.Topology.PresheafModuleStalkFunctor`.
This is an import pruned from this module, not a claim that it is globally unreached.

All three old direct proof_deps are accounted for:
`def-weil-pbc-free-module` and `def-weil-pbc-module-stalk` move below the ordinary
sheaf-map equality helper; they remain mathematically needed there.
`lem-weil-pbc-open-immersion-module-pullback-restriction` is no longer needed by
this reduction: restriction is handled directly by the additive functor API.
The original node now directly uses only `lem-pc-finite-free-stalk-map-eq-shrink`.
No unit or chapter route is bypassed; no global module-pruning claim is made.

## Where the brief, the DAG or earlier work was wrong

The first worker's equality helper had the original homotopy hypotheses, all
complex parameters and essentially the entire local conclusion. Merely applying
Homotopy.ofEq to it was not an adequate split. Its node also referred back to
the parent in stmt_deps, and the parent DAG had not been updated to cite the helper.
The replacement is an ordinary morphism lemma without a complex or homotopy;
the complex-specific reduction is now proved explicitly, and the circular
statement dependency has been removed.

## New nodes

`lem-pc-finite-free-stalk-map-eq-shrink`: equality near a stalk for ordinary
sheaf maps whose source is isomorphic to a restricted finite free sheaf. Its
statement is self-contained, its Lean signature is recorded verbatim, and its
proof cites the existing free-module, module-stalk and pullback-stalk nodes.
Its origin is the finite germ calculation of lem-pc-perfect-locus already
recorded in the parent. The original declaration is unchanged, and this helper did not exist on the base.
Public import removal is recorded in
`coord/changes/finite-free-stalk-q-imports.md`; the unchanged direct importer
PairShrink compiles against the delivered module and already exports the removed
upstream API through its own public import. The record lists all 684 transitive users.

## Earlier second reading (a previous round; superseded)

1. Compared the original module with the repository using diff and checked the
   declaration signature byte for byte through :=. The existing theorem's
   binders, all hypotheses, conclusion, visibility and docstring are unchanged.
   The first worker's unlanded helper was replaced; no existing definition changed.
2. Compiled both delivered modules locally in import order with lcompile.py.
   No errors or warnings. Explicit scratch #print axioms for both public
   declarations showed only the three permitted axioms and the single remaining
   sorryAx dependency. Searched for prohibited declarations and hollow definitions:
   none. There are no definitions in the new module.
3. Checked the lower lemma with rank zero (zero source, W=U), rank one (one
   generator germ), arbitrary target N, and U=V. Equality on the local-scheme
   pullback implies equality on the closed-point stalk, because its local ring
   map is an isomorphism; finite many source generators give a common open.
   No target finiteness or quasi-coherence hypothesis is used. Repeated searches
   with different words: LeanFinder's eight hits give global hom_ext or generator
   data, not this theorem; Loogle's germ query and local Mathlib source give the
   elementwise germ_eq ingredient only. Searched lean/Sheaf and the upstream
   module API; no duplicate local morphism theorem found. LeanSearch returned
   Internal Server Error; this is recorded as unavailable, not as no match.
4. Read the proof from its top: Mathlib's zero-differential and zero-object lemmas
   perform the complex reduction, then the strictly lower sheaf-map statement.
   Checked negative and arbitrary i: no nonnegativity or bounded interval is
   introduced, and n≠i is covered by isZero_single_obj_X. The new import is
   proof-only. The unused upstream import was removed and all old proof_deps
   are listed above. dag/units/sk-thm-picard-perfect.json has empty realized
   lists and is unchanged; the finite local calculation stays in that unit.
5. Read both DAG nodes alongside Lean. The original node now records the three
   actual proof steps and only its new direct dependency. The new node records
   the ordinary sheaf-map statement, correct module/declaration and verbatim
   signature, source, complete argument, searches, creation and blueprint origin.
   Its stmt_deps no longer cites the parent, so it creates no back-edge.

Changed during this reading: replaced the restatement by a strictly lower
sheaf-map lemma in its own module; proved the chain-level reduction; removed
an unused upstream import; repaired both nodes and the hole accounting.

Dry-run repair: added the required public-import change record after preflight
requested it. Checked the unchanged direct importer against the revised overlay;
it compiles without error or warning. No downstream source is delivered.

## Second reading by B3

1. Compared the delivered Q-shrink module with the repository version. The theorem
   signature and docstring are unchanged byte for byte; only its proof and imports
   differ. The added map-equality declaration is a separate, strictly lower node.

2. Compiled both modules in import order with `lcompile.py --all`; both compile with
   no errors or warnings. There are no prohibited declarations or hollow definitions.
   The only remaining `sorry` is the named lower theorem
   `exists_restrict_eq_of_pullback_eq`, recorded by node
   `lem-pc-finite-free-stalk-map-eq-shrink`.

3. Checked the new statement on rank zero, rank one, arbitrary targets, and U = V.
   It uses only finite-free source data and is exactly the local finite-germ equality
   needed by the parent proof; no target finiteness or extra hypothesis was added.
   Searches found no existing theorem with this statement.

4. Read the proof top down. The parent first extracts the degree-i equality from the
   homotopy commutator, applies the lower sheaf-map lemma, and then rebuilds chain-map
   equality using zero source components and `Homotopy.ofEq`. The single-object unit
   route is preserved. The unused upstream and stalk-functor imports were pruned.

5. Checked both DAG nodes against the Lean declarations, including signatures,
   proof dependencies, origins, and the new node metadata. The parent now depends
   directly on the lower map-equality node, with no circular dependency.

Changed during this reading: repaired this report heading, retained the lower split
as the only remaining hole, and kept the import change record required by preflight.
