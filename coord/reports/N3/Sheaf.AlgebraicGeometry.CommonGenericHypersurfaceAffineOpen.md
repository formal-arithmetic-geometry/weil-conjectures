## What changed

`Sheaf.AlgebraicGeometry.CommonGenericHypersurfaceAffineOpen` now proves
`AlgebraicGeometry.exists_common_generic_hypersurface_affine_open` from two separate
steps of the original plan. The existing signature and public imports are unchanged.
Two proof-only imports were added: `GenericFibreBirationalHypersurfaceModel` and
`GenericFibrePartialIsoSpreadOpen`. The main proof proves finite presentation of the
hypersurface map, obtains nonemptiness from generic geometric irreducibility, spreads
the generic partial isomorphism, chooses an affine neighbourhood of a point above eta,
and checks the composite open immersion and its equation over the base.

All three modules compile locally through lcompile.py. The new statements were
checked against Stacks Tags 0559, 0552, and (for general affine spreading) 01ZM.
LeanFinder, Loogle, and source grep found no exact existing theorem; LeanSearch
returned HTTP 500 and is recorded as unavailable. The original node has no named
proof dependencies. The unit record `sk-prop-normal-form` has no realized nodes;
the original slicing ancestry and both field-model/common-open steps are retained.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_common_generic_hypersurface_affine_open`
(node `lem-sbc-common-generic-hypersurface-affine-open`). No sorry remains in the item.

Added two named holes, each in its own public module:

- `AlgebraicGeometry.exists_generic_fibre_birational_hypersurface_model`
  (`lem-sbc-generic-fibre-birational-hypersurface-model`): the polynomial construction
  and common opens ONLY on the generic fibres; it supplies no open in the original X.
- `AlgebraicGeometry.exists_open_of_generic_fibre_partial_iso`
  (`lem-sbc-generic-fibre-partial-iso-spread-open`): spreading an already supplied
  generic partial isomorphism for arbitrary affine finitely presented families;
  it constructs no polynomial and asserts no geometric properties.

This is a decomposition: one upper hole closed, two lower holes added, net -1.
The complete Lean combination and affine-neighbourhood step are proved. The final
declaration still depends on sorryAx through these two named dependencies.

## No longer needed

No pre-existing imports, named dependencies, nodes, or modules were removed: the
original node has an empty proof_deps list and all original public imports occur in
the statement. The route no longer requires proving integrality of the full source
or arranging a monic hypersurface with integral total space before spreading.
The generic model permits vertical components of the original hypersurface;
finite-presentation descent discards them where necessary by a base localization.
These unused preliminaries had no separate node or imported module to prune.
Flatness and reducedness remain hypotheses of the unchanged original statement.

## Where the brief, the DAG or earlier work was wrong

The original node's single non-elementary proof step had uses=[]: it provided no
Lean declarations for the field-model or common-localization arguments. The two
new statements fill that gap without changing the original statement.

The original proof's monic/integral-total-space preparation is not needed by this
route. The new generic model makes no assertion about the special fibres. Spreading
uses finite presentation, with all inverse and structure-map equations descended
and cleared simultaneously, so it needs no reducedness or flatness of the ambient
special fibres. The original full theorem is not restated under another name.

The blueprint_refs ancestor command cannot follow created.item records that name
Lean modules, and returned None here. The new nodes instead inherit the parent's
explicit sbc-lem-slicing ancestry and exact source paragraph, prepending the parent
to via. Blueprint searches for hypersurface and birational found no duplicate.

Edge cases checked: the model uses a linear equation in an additional variable for
purely transcendental extensions, including dimension zero. Empty generic fibres
are excluded by geometric irreducibility in the model, and by the explicit Nonempty
hypothesis in the spreading theorem. A dense source open cannot be empty in that
case. The spreading theorem allows vertical components and special-fibre nilpotents;
finite presentation is retained to descend finitely many relations and inverse
identities. No Noetherian hypothesis is added.

## New nodes

`lem-sbc-generic-fibre-birational-hypersurface-model` states the generic-only polynomial
and birationality step of Tag 0559, with the separating-basis, primitive-element,
absolute-irreducibility, denominator-clearing, and function-field/common-open proof.
Its module is `Sheaf.AlgebraicGeometry.GenericFibreBirationalHypersurfaceModel`.

`lem-sbc-generic-fibre-partial-iso-spread-open` states the general finite-presentation
spreading step, with explicit dense generic partial isomorphism and nonemptiness
hypotheses. Its module is `Sheaf.AlgebraicGeometry.GenericFibrePartialIsoSpreadOpen`.
Its proof details how both inverse maps, their identities, and the equation over
S descend after one nonzero base localization, as in Tags 0559 and 01ZM.

No statement or definition changes, forced adaptations, or change records.

## Second reading by N3

1. **Interfaces: pass.** Diffed the delivered item against the repository version.
   Its only original declaration has exactly the same signature, visibility and
   hypotheses; all original public imports are unchanged. The two added imports
   are proof-only. Both other modules are new; no definitions or existing
   statements are altered and no change record or forced adaptation is needed.
2. **Proof and axioms: pass as a decomposition.** Compiled all three modules in
   import order with lcompile.py, without errors or warnings. A separate scratch
   module printed axioms for all three declarations: only propext, Classical.choice,
   Quot.sound and sorryAx. The two documented split theorems are the only remaining
   sorries. There is no axiom, unsafe, opaque, implemented_by, extern, holed
   definition, or data definition choosing an arbitrary unproved witness. The
   model and opens are eliminated inside a proof of an existential proposition.
3. **Split statements: pass.** Read both full statements and natural-language
   proofs against [Tag 0559](https://stacks.math.columbia.edu/tag/0559),
   [Tag 0552](https://stacks.math.columbia.edu/tag/0552) and
   [Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM). The model is only over
   the generic residue field and does not spread opens. Geometric integrality
   makes its function field regular; a separating basis and primitive numerator
   give the required absolutely irreducible polynomial. A linear extra variable
   covers purely transcendental and dimension-zero cases. The spreading statement
   assumes an actual partial isomorphism, whose source and target are dense by
   Mathlib's definition; source nonemptiness is explicit. It needs no ambient
   integrality, flatness, reducedness or Noetherian base. Finite presentation
   descends the maps and inverse equations after a common nonzero localization.
   Neither statement restates the item. Renewed LeanFinder queries used
   separably generated function fields and extending generic open isomorphisms;
   Loogle queried PartialIso with fiber; grep queried generic isomorphisms,
   open/isomorphism descent and separablyGenerated. Source rg also checked
   lean/Sheaf and lean/WeilConjectures. No exact replacement was found. Neither
   substantial field construction nor general spreading closes in a few minutes.
4. **Route, imports and pruning: pass.** The proof combines the two genuine
   lower steps, proves finite presentation and nonemptiness, then constructs the
   affine neighbourhood and checks the composite equation. Imports introduce
   notions used by statements or the two proof steps; no proof-only public import
   was added. The old proof_deps was empty, so No longer needed is complete.
   Read sk-prop-normal-form's statement, steps and realized record (empty lists).
   This item is below its slicing step; the field-model and common-open route
   is retained, and no realized unit node is bypassed. One hole closed and two
   added is a decomposition, net -1, with no module pruned.
5. **Nodes: pass.** Each node's lean.statement matches its module signature
   byte for byte. The existing node changes only proof, proof_deps and
   proof_origin, and its dependency union is precisely the two used split nodes.
   New nodes contain source, full proof, searches, split status, creation record,
   inherited chapter/unit and blueprint ancestry, and complete Lean records.

Second reading changed the main theorem's stale proof docstring to describe the
actual generic-model/spreading/affine-neighbourhood reduction. It clarified the
spreading theorem's proof and its node: intersect compatible affine neighbourhoods
inside the separated generic affine scheme, descend their quasi-compact opens,
then descend the inverse maps and identities using finite presentation. This
avoids suggesting that the same intersection must be principal on both sides.
No Lean proof term, declaration signature, imports or dependency list changed.
The scratch axiom-check module was removed before delivery.
