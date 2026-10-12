## What changed

Completed `AlgebraicGeometry.Scheme.Modules.canonicalSinglePullbackComposition` with its
original statement unchanged. The proof evaluates `Functor.leftDerived_fac_app` for the
selected composition comparison, applies naturality of the selected counit, and combines
functoriality and associativity.

Added the proved module `Sheaf.AlgebraicGeometry.Picard.HomotopySinglePullbackComposition`.
Its public theorem proves the underived/homotopy part of the original plan: uniqueness of
left adjoints identifies the tensor-to-ordinary comparisons under composition; a
componentwise chain-map calculation and the homotopy quotient give the single-complex
identity. Four proved private generic helpers implement the adjunction calculation and
the componentwise calculation. There are no new definitions or choices of data.

Removed the inherited expensive unfolding helper `canonicalSinglePullbackMap_eq`; the
final proof unfolds the comparison only once. The homotopy quotient rewrite is proved generically before specialization, avoiding
repeated kernel reduction of the large chosen adjunctions. Both modules compile under the
single-file limit. The new helper is a mathematical statement from steps 2–3 of the plan,
not a replacement for the derived universal-property/naturality argument.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.canonicalSinglePullbackComposition`
(node `lem-pc-canonical-single-pullback-composition`).

Also proved `AlgebraicGeometry.Scheme.Modules.homotopySinglePullbackComposition`
(node `lem-pc-homotopy-single-pullback-composition`) and its four private helpers.
No sorry remains in either delivered module. No holes were added or split off.
Existing upstream dependencies retain their own proof status; none were modified.

## No longer needed

Removed the redundant direct proof imports
`Sheaf.AlgebraicGeometry.DerivedPullbackComposition` and
`Sheaf.AlgebraicGeometry.TensorPullbackAdjunction` from the item's module. Their results
are still used through the public statement import and the new homotopy helper,
respectively: neither module nor its node is pruned from the transitive proof closure.
The old direct proof dependency `lem-pc-module-pullback-adjunction` is now used through
`lem-pc-homotopy-single-pullback-composition`, rather than directly by the item. It is
retained in the helper's `proof_deps`; no mathematical node or module from the original
plan becomes unnecessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the original statement or plan was found. The inherited report
was stale: it described a remaining sorry, while the inherited files attempted a complete
proof but contained an unregistered helper module and failed to compile within the limit.
The recovered proof now compiles and its helper has a matching DAG node.

The new homotopy statement covers arbitrary modules and morphisms. Its proof does not
invert the derived single comparison or assume flatness, a nonzero module, or a nonempty
scheme. In degree zero the compatibility is the adjunction mate identity; other degrees
are handled by extensionality into a single complex. Thus identity maps, zero modules,
and empty schemes require no additional hypothesis. The unit record's realized arrays
are empty for this item; the delivery retains the original route and its derived
composition and adjunction ingredients.

Searches used LeanFinder, Loogle, and source grep (recorded in the new node); LeanSearch
returned Internal Server Error, recorded as unavailable. The hits supply generic
adjunction and single-complex tools rather than the exact pinned scheme comparison.

## New nodes

`lem-pc-homotopy-single-pullback-composition`, in
`dag/nodes/sec-picard-framework/lem-pc-homotopy-single-pullback-composition.json`, records
the proved compatibility of tensor-to-ordinary pullback comparisons on homotopy single
complexes. It isolates steps 2–3 of the original plan, requires no derived-category
instances, and is used in the real derived factorization/naturality proof of the item.
No change record is needed: no existing statement, definition, or visibility changed.


## Second reading by K3

1. **Interfaces — pass.** Compared the item with the repository using `diff`, then
   compared its complete theorem signature byte for byte: identical. The existing
   docstring, public section, universe parameters, and shared derived-category
   assumption are preserved. The only existing node fields changed are `proof`,
   `proof_deps`, and `proof_origin`. The second delivered module is new. There are no
   changes to definitions, target statements, or other modules and no change records.

2. **Proofs and axioms — pass, conditional on existing upstream holes.** Independently
   compiled both modules in import order with `lcompile.py --all`: the helper took
   5.9 seconds and the item 49.9 seconds, with no warnings or errors. Neither delivered
   module contains `sorry` or forbidden declarations, and neither introduces a
   definition or arbitrary existence witness. A scratch import with `#print axioms`
   shows `[propext, Classical.choice, Quot.sound]` for
   `AlgebraicGeometry.Scheme.Modules.homotopySinglePullbackComposition` and for
   `exists_tensorPullbackAdjunction`. The item's theorem also has `sorryAx`, as does
   the unchanged `AlgebraicGeometry.exists_derivedPullbackComposition` on which its
   pinned comparison depends. Thus the original local hole is closed, but this is
   not a claim that its whole upstream closure is sorry-free. The scratch file was
   removed before delivery.

3. **New statement — pass.** No statements are left split off with `sorry`. Read the
   new homotopy theorem, all four private proofs, and its node. Its additive instances
   are exactly those required for termwise maps; it has no derived-category, flatness,
   invertibility, or nonemptiness assumptions. Its `t`, `r`, and conjugate-composition
   expressions match the node verbatim. In `compat`, `hp'` correctly derives the
   inverse pushforward mate from `conjugateEquiv_pullbackComp_inv`; injectivity then
   proves the two underived paths equal. `single_compat` uses extensionality into a
   single complex, and `homotopy_single_compat` maps the equality through the quotient.
   For identity morphisms this is the adjunction unit/composition law; for zero modules
   the single target is zero; empty schemes require no objects or sections to be
   nonzero. The helper is strictly the underived part of the original argument, not a
   renaming of the derived conclusion. Its source and full prose proof are recorded.

4. **Route and pruning — pass.** Read the selected counit/composition statement and
   `canonicalSinglePullbackMap`, and checked Mathlib's `leftDerived_fac_app` and
   `conjugateEquiv_pullbackComp_inv`. The main proof evaluates the chosen factorization,
   substitutes the genuinely proved homotopy identity, and uses counit naturality;
   no single comparison is inverted. Independent Loogle search for
   `CategoryTheory.Adjunction.leftAdjointUniq`, LeanFinder search for compatibility of
   uniqueness with composing adjunctions and mates, and source searches in Mathlib,
   `lean/Sheaf`, and upstream found generic tools, not the pinned theorem. Read the
   candidate `Adjunction.leftAdjointCompIso` API: it constructs the mate but does not
   replace the comparison between the two different chosen left-adjoint families.
   The related single-composition calculations in `EtalePullbackSingleComp` are
   private and their derived results require exact functors, unlike this item.
   The two public helper imports are needed by its signature; the item imports the
   helper privately. Removed direct imports remain available transitively. The report
   now explicitly accounts for all old direct `proof_deps`, including the adjunction
   node moved behind the helper. The unit `sk-thm-picard-f-representable` has
   `realized = {statement: [], steps: [[]]}`; no realized node or unit step is bypassed.

5. **DAG agreement — pass.** The item's two new proof steps record `hfacC` and the
   `ht`/`hn` substitution, with their dependency union matching `proof_deps`. The
   helper's three steps describe precisely the mate, chain-map, and quotient proofs.
   Its `lean.statement` matches its complete Lean signature, and its source, creation,
   chapter, unit, blueprint provenance, and recorded searches are present. The
   existing adjunction node remains a dependency of the helper, so no old mathematical
   ingredient is falsely reported as pruned.

**Changes by the second reader:** clarified the old adjunction dependency's placement
under `## No longer needed` and added this independent review with the axiom limitation.
No Lean proof, statement, import, or node required repair.
