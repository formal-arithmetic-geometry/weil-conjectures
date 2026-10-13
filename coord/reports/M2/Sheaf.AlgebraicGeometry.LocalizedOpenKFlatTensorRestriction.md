## What changed

Replaced the single hole in `AlgebraicGeometry.localizedOpen_kFlat_tensor_restriction`
by a proof using the existing `openRestriction_isKFlat` and
`openRestriction_totalTensor_iso` statements. The proof constructs the total tensor
comparison for the localized-site equivalence from natural module tensor comparisons,
reflects exactness through that equivalence, lifts the complex isomorphism through
its fully faithful complex functor, and applies the exact-functor quotient comparison.
All existing public signatures and public imports stay unchanged. Added proof imports
of LocalizedOpenTensorEquivalence, OpenRestrictionKFlatModel,
OpenRestrictionTotalTensor and TotalComplexMap.

The missing natural tensor comparison for `Scheme.Modules.overEquiv U` is isolated
in a new module. This is a comparison of module sheaves, with no complex, K-flatness
or derived-category assumptions; it is strictly below the original theorem. The
bicomplex and derived-category glue is proved in the original module.

## Proved and sorry left

Closed: `AlgebraicGeometry.localizedOpen_kFlat_tensor_restriction`
(node `lem-sc-localized-open-kflat-tensor-restriction`). No sorry remains in the item.

Added: `AlgebraicGeometry.exists_localizedOpen_tensor_equivalence`
(node `lem-sc-localized-open-tensor-equivalence`) in
`Sheaf.AlgebraicGeometry.LocalizedOpenTensorEquivalence`. Its proof is exactly
`by sorry`, with the local pure-tensor/sheafification argument in its docstring.
This is a decomposition (one upper hole closed, one smaller hole added), rather
than an unconditional proof of the entire assertion. The private totalization
helper is fully proved. Both modules compiled locally; the final dry run checks
the warning-free versions and their axiom probes.

Edge cases: the tensor equivalence uses neither nonemptiness of U nor nonzero
modules; the construction identifies the empty sites and sends zero modules to
zero modules. Arbitrary complexes are allowed since totalization uses coproducts
preserved by the equivalence, with no boundedness assumption.

## No longer needed

No imports were removed from the original item, and no planned K-flat or
total-tensor module was pruned. In the new module, the second reader replaced
the broad KFlat import by the sheaf monoidal module needed by its statement.
The node no longer lists `lem-weil-pbc-module-restriction-open-immersion-colimits`
as a direct proof dependency: the equivalence, exactness, and colimit preservation
are supplied by the existing Mathlib equivalence and instances. That node remains
a statement dependency of the original node, so it
is not globally pruned.

## Where the brief, the DAG or earlier work was wrong

The original two steps hid the tensor compatibility of the localized-site
equivalence: the recorded open-restriction lemmas have conclusions on U.toScheme,
not on the localized carrier. Neither supplies that comparison. The new node
states precisely the missing module-level fact, and the original node now records
the complete Lean transport route. The unit's realized statement/step lists are
empty, and no unit route is bypassed.

Read the Stacks pages [01CD](https://stacks.math.columbia.edu/tag/01CD),
[06YC](https://stacks.math.columbia.edu/tag/06YC), and
[08DX](https://stacks.math.columbia.edu/tag/08DX). Tag 01CD states naturality of
pullback with tensor (its proof is omitted); the new docstring spells out the
localized-site version on sections. The checked-in literature tex files are not
present on this machine, so the public source pages were used.

## New nodes

`lem-sc-localized-open-tensor-equivalence` in
`dag/nodes/sec-picard-framework/lem-sc-localized-open-tensor-equivalence.json`:
the natural tensor comparison for the canonical localized-open equivalence.
Its module contains one public theorem. Its construction is the module-tensor
portion of step 1 of the original node, not a restatement of any complex or
derived conclusion. No definition, existing statement, or target was changed;
no forced adaptation is required. The change record
`coord/changes/localizedOpenKFlatTensorRestriction-proof-context.md` documents the
local proof elaboration commands conservatively flagged by the interface checker.

The blueprint ancestor helper returns None for the item because its created.item
is a module name. The new node follows the existing explicit blueprint.from links
to `lem-sc-finite-duality` through the local-perfect tensor argument. The original
blueprint metadata is preserved.

## Second reading by M2

1. Compared the delivered item with the repository using `diff -u`. The complete
   signature of `localizedOpen_kFlat_tensor_restriction`, its existing docstring,
   definitions and existing public imports are unchanged. The added private tensor
   structure is the actual `SheafOfModules.monoidalCategory (X.sheaf.over U)`;
   it contains no postponed data. The proof-context change record explains the
   local attributes and namespace opening. Verdict: no accidental interface change.
2. Read both Lean modules and the existing `openRestriction_isKFlat` and
   `openRestriction_totalTensor_iso` proofs. The helper applies naturality separately
   to each differential, then `mapTotalIso` and `total.mapIso`. The main proof maps
   acyclicity forward, reflects exactness through the faithful equivalence, lifts
   the complex comparison with `preimageIso`, and composes the quotient comparison.
   There is precisely one named `sorry`, in the reported new theorem; no forbidden
   declaration or hollow definition. Local compilation and delivery axiom probes
   are the validation checks. Verdict: a genuine conditional proof/decomposition.
3. Read [Tag 01CD](https://stacks.math.columbia.edu/tag/01CD), which states tensor
   compatibility functorially, and the definition of `Scheme.Modules.overEquiv`
   in Mathlib, including `Opens.sheafOfModulesEquivOver`. The new theorem uses the
   actual site equivalence and coefficient identifications. Its pure-tensor maps
   respect balanced relations and restriction maps; sheafification preserves the
   inverse maps, and applying f and g in either order proves the displayed equation.
   Empty U, U = top, either zero factor and zero/identity module maps satisfy this
   argument without extra hypotheses. This statement concerns only modules, and
   leaves all complex and derived transport to the proved helper and item. Searches
   with “equivalence of sites with isomorphic coefficient sheaves”,
   `SheafOfModules, CategoryTheory.Equivalence`, and tensor/congruence terms in
   Mathlib and the project found site equivalences and pullback comparisons but
   no existing natural tensor comparison for arbitrary localized module sheaves.
   Closing it needs a sheafification/coefficient transport construction, rather
   than a short application of a found lemma. Verdict: true, needed, strictly simpler,
   sourced, documented and represented by its new node; retain its single hole.
4. Read [Tag 06YC](https://stacks.math.columbia.edu/tag/06YC) and
   [Tag 08DX](https://stacks.math.columbia.edu/tag/08DX). The existing K-flat and
   total tensor declarations have the required conclusions after composition with
   overEquiv, so neither alone closes the localized statement. The proof uses both
   planned lemmas and no perfectness or boundedness assumption. The unit
   `sk-thm-picard-duality` has `realized.statement = []` and `realized.steps = [[]]`;
   no realized unit node is bypassed. The removed direct proof dependency is fully
   listed under No longer needed. Verdict: top-down reduction and route preserved.
5. Compared the item node with its repository version: only `proof`, `proof_deps`
   and `proof_origin` changed. Their steps match the tensor transport, K-flatness,
   total-complex comparison and derived quotient used in Lean. Checked the new
   node's complete statement, source, searches, creation metadata, blueprint links,
   chapter/unit, dependency union and verbatim Lean signature. Verdict: DAG and Lean
   agree; no statement was weakened.

Second-reading change: replaced the new comparison module's broad public import
`Sheaf.Algebra.Homology.KFlat` by
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`, which supplies exactly
its sheaf tensor structures. No proof or statement was rewritten. The original
item's imports and proof are retained. One original hole closed, one smaller hole
added: net zero, a decomposition, with no globally pruned module.

Validation completed by the second reader: both delivered modules compiled locally.
A scratch copy of the full item with `#print axioms` for both public theorems
compiled and printed exactly `propext`, `sorryAx`, `Classical.choice`, `Quot.sound`
for each. The `sorryAx` is expected from the explicitly reported remaining hole
and open imported statements; no additional axiom was found.
