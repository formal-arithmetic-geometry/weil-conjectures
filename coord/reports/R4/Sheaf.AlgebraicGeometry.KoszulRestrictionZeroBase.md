## What changed

Replaced the saved attempt's unique-morphism restatement by a genuine two-step
reduction. The unchanged theorem `AlgebraicGeometry.isZero_restrict_koszul_base`
now proves the result from local exactness on each generator basic open and a
separate, generic exactness-gluing theorem for an open cover. The Lean proof
assembles acyclicity degree by degree, proves that the zero-complex map is a
quasi-isomorphism, uses derived localization to invert it, and transports the
zero-object property through `mapDerivedCategoryFactors`.

Added proof-only imports of `Sheaf.AlgebraicGeometry.KoszulBasicOpenExact` and
`Sheaf.AlgebraicGeometry.OpenCoverRestrictionExact`. Existing signatures and
public imports are unchanged. The existing node's proof and proof dependencies
now follow the Lean argument. The retry repaired the statement syntax of the two new lemmas: parenthesized
`.ExactAt n` replaces a top-level pipeline, which the delivery parser mistook
for the start of a proof. Their node records now contain their full signatures.
The zero-object instance is introduced locally inside the existing theorem's
proof, so the item's file-level commands remain unchanged. The earlier SSH timeout
has cleared. All three modules compile without unexpected warnings, and the
local axiom probes pass. `deliver3.py --no-push` printed OK: preflight passes
except for the second reading, which the second reader writes. Nothing was pushed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.isZero_restrict_koszul_base`
(node `lem-pc-koszul-restriction-zero-base`).

Added two strictly smaller named holes, one in each new module:

- `AlgebraicGeometry.koszul_basicOpen_exact`
  (node `lem-r4-koszul-basic-open-exact`): exactness in one degree on one basic open,
  without any derived-category assumptions or a cover-gluing assertion.
- `AlgebraicGeometry.exactAt_over_of_open_cover`
  (node `lem-r4-open-cover-restriction-exact`): generic sheaf exactness gluing in
  one degree, conditional on local exactness; it contains no Koszul or derived
  category content.

This is a decomposition, not a sorry-free proof: one hole closed, two holes added,
net minus one. No sorry remains in the item's module. Both new theorem proofs
are exactly `by sorry`, with sources and complete informal proofs in docstrings.

## No longer needed

No existing module was pruned. The old proof-dependency entries
`def-weil-pbc-koszul-complex` and `def-pc-derived-category` are replaced by the
two new lemma nodes in the main node: they are no longer separate proof steps,
but remain statement dependencies and their modules remain public imports.
All original public imports remain necessary to express the unchanged statement. The saved attempt's
`KoszulRestrictionZeroIso` module and its nodes
`new-koszul-restriction-zero-iso` and `new-koszul-restriction-zero-object` were
removed from the sandbox: they merely repackaged the original conclusion and
are not part of this delivery. No analogous convenience definition is introduced.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt's unique incoming/outgoing morphisms are equivalent to
`IsZero` with the same hypotheses. Packaging that statement as `IsZero` was not
a reduction. It also lacked complete proof docstrings and all three search kinds.
The replacement isolates the local contraction and the generic gluing step.

The original node compressed local contraction, sheaf gluing, and derived
localization into one sentence. Its mathematical claim and signature are kept.
The unit record has no realized statement or step nodes; the source route through
local contraction and gluing is preserved. Searches found no exact available
library theorem for either new statement. LeanSearch returned Internal Server
Error and is recorded as unavailable, not as a successful no-match search.

Sources checked: Stacks Tags 0663, 09IR and 01AG. The source files named by the
DAG are not installed in this checkout; the corresponding Stacks pages were read.
Edge cases: r=0 has no basic-open indices and gives U empty; an empty basic open
has a zero category of module sheaves; nilpotent generators cause no exception;
no regular-sequence or global-section surjectivity assumption is used. The generic
gluing statement allows any cover index universe, including an empty index type.

## New nodes

`lem-r4-koszul-basic-open-exact`, stated in
`lean/Sheaf/AlgebraicGeometry/KoszulBasicOpenExact.lean`, isolates the contraction
argument from Tags 0663 and 09IR.

`lem-r4-open-cover-restriction-exact`, stated in
`lean/Sheaf/AlgebraicGeometry/OpenCoverRestrictionExact.lean`, isolates stalkwise
exactness gluing from Tag 01AG.

There are no definition changes, forced adaptations, or change records.


## Second reading by R4

1. **Existing interface: PASS.** Read the repository and sandbox files and their
   diff. The sole existing signature, `isZero_restrict_koszul_base`, is byte for
   byte identical, including both `HasDerivedCategory` instances, the arbitrary
   ring, `Fin r` family, open U and the exact union equality. No existing
   definition, visibility, public import, or file-level instance changed. There
   are no change records or forced adaptations.

2. **Kernel proof and holes: PASS as a decomposition.** Independently compiled
   all three modules in import order using `lcompile.py --all`, then compiled
   scratch copies with `#print axioms` for each of the three declarations. Each
   printed exactly `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The main theorem contains no sorry. Each new module has exactly one named
   theorem whose whole proof is `by sorry`; these are precisely the two holes
   listed above. There are no definitions in the delivery, arbitrary data
   witnesses, forbidden axioms, unsafe declarations or kernel bypasses.
   The zero-complex map is genuinely shown quasi-isomorphic using exactness in
   every degree. Its image is inverted by Q; the orientation of both zero-object
   transports agrees with `asIso` and `mapDerivedCategoryFactors.app K`.

3. **New statements: PASS.** Read both complete signatures, docstrings and node
   proofs against Stacks [0663](https://stacks.math.columbia.edu/tag/0663),
   [09IR](https://stacks.math.columbia.edu/tag/09IR), and
   [01AG](https://stacks.math.columbia.edu/tag/01AG).
   `koszul_basicOpen_exact` isolates the exterior-multiplication contraction on
   D(f_i), with no derived-category or cover assumption. The homotopy identity
   uses the actual contraction differential of `KoszulComplex`; multiplication
   by the inverse of f_i on that open gives identity homotopic to zero.
   `exactAt_over_of_open_cover` is conditional generic exactness in one degree,
   with no Koszul content. At every point of U the union equality supplies a
   V_i containing it, so restriction identifies stalk complexes and 01AG applies.
   Neither theorem restates the item. Checked r=0 (no i, U empty), f_i=0 or
   nilpotent (D(f_i) empty), a unit generator (D(f_i)=X), degrees outside the
   Koszul range, empty covers and arbitrary cover-index universes. No regularity,
   finiteness of the cover or global-section lifting is silently assumed.
   Independent searches used LeanFinder for contracting homotopies with a unit
   coordinate, Loogle for `SheafOfModules.overFunctor`, msearch grep for stalk
   exactness and restricted homology, and rg in both library roots and Mathlib.
   `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact` concerns ordinary sheaves;
   `Scheme.Modules.isZero_of_iSup_eq_top` and `overFunctorEquiv` are relevant
   tools but require additional restriction/homology and category comparisons.
   `CechSheafResolution` has a private quasi-isomorphism cover argument for
   `Scheme.Modules`, not the new statement. No direct duplicate was found.
   Closing either new hole was not a few-minute specialization.

4. **Route and pruning: PASS.** The proof proceeds from the original target
   through local contraction and exactness gluing, and implements the final
   localization step rather than moving its conclusion to another sorry.
   Read `dag/units/sk-thm-picard-duality.json`: its realized statement is empty
   and its only realized step list is empty. No realized node or unit step is
   bypassed; the source Koszul-vanishing route is retained. Both proof-only
   imports in the main module are plain imports. Removed the redundant direct
   `ShortComplex.HomologicalComplex` import from `KoszulBasicOpenExact` (already
   public through `KoszulComplex`) and the redundant `Homology.Additive` import
   from `OpenCoverRestrictionExact`. Their other public imports support the
   statements, including the restriction additivity instances. Recompiled cleanly.
   The No longer needed section now explicitly accounts for the two old
   proof-dependency entries, retained as statement dependencies; no existing
   module is claimed pruned. This closes one original hole and adds two, net -1;
   it is a decomposition, not a sorry-free proof or positive ledger progress.

5. **DAG agreement: PASS.** The existing node differs only in `proof`,
   `proof_deps`, and `proof_origin`. Its two steps match hL and the Q/isomorphism
   argument in Lean. Checked every node's `lean.statement` against its actual
   signature and every `proof_deps` against the union of its steps' `uses`.
   Both new nodes have their source, full signatures, statement dependencies,
   creation/blueprint/chapter/unit records and three search kinds; the unavailable
   LeanSearch service is honestly recorded. Each named hole has a matching node
   and the docstring provides the argument needed to take it over.

Second reading changed only the two redundant imports, added blueprint tags to
both new module docstrings, corrected overescaped TeX in both new node statements,
and made the old proof-dependency accounting explicit in this report. The main
Lean proof and all theorem signatures were left as read. Axiom scratch files
were removed before delivery.
