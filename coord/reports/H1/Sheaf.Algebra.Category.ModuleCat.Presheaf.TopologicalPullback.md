## What changed

Proved `PresheafOfModules.topologicalPullbackAdjunction`, preserving its statement and both existing definitions. Added proof-only imports of `TopologicalPullbackComparison` and `TopologicalPullbackRepresentatives`; both new modules are fully proved. Mathlib supplies the abstract module adjunction and the concrete varying-ring filtered-colimit module structure (`IsColimit.module` and `IsColimit.ι_smul`).

The comparison proof constructs the concrete module presheaf, proves restrictions and the unit are linear, bundles the canonical abelian adjunct as a module map, and builds its inverse with the module adjunction. The main proof constructs the natural isomorphism, proves the coprojection action formula, transports the scalar action, proves uniqueness using common representatives, and verifies the precise underlying Hom formula.

## Proved and sorry left

- `PresheafOfModules.topologicalPullbackAdjunction`, original node `lem-pc-presheaf-module-inverse-image-adjunction`: proved.
- `PresheafOfModules.topologicalModulePullbackComparison`, new node `lem-pc-topological-module-pullback-comparison`: proved.
- `PresheafOfModules.topologicalPullbackCommonRepresentatives`, new node `lem-pc-topological-pullback-common-representatives`: proved.
- No `sorry` remains in any delivered Lean module. No unfinished statement is introduced.

The proofs cover empty opens, empty spaces, zero rings and zero groups without extra assumptions. All three modules compile locally without warnings. The delivery dry run supplies the server compile and axiom checks.

## No longer needed

`lem-weil-pbc-filtered-colimit-modules-elementwise` is no longer needed on this proof route: abelian representatives use `Concrete.isColimit_exists_rep` and preservation of filtered colimits by `forget Ab`, without converting to integer modules. `Mathlib.Algebra.Category.ModuleCat.FilteredColimits` is not needed by these proofs.

No existing public import was removed: each supports unchanged public definitions or statements. In the new representative module, the redundant explicit `Mathlib.Algebra.Category.Grp.FilteredColimits` import was removed because `Mathlib.Algebra.Category.Ring.FilteredColimits` already imports it. The filtered-colimit and concrete-colimit proof imports there are private.

The other old direct dependencies removed from the item node are `def-weil-pbc-category-colimit` and `lem-pc-filtered-colimit-commrings-elementwise`; both remain needed transitively through the proved comparison/representative helpers and are not globally pruned. The old topological inverse-image and presheaf-module definition dependencies remain direct. Only `lem-weil-pbc-filtered-colimit-modules-elementwise` is eliminated from this proof route. No blueprint unit route is changed: `sk-def-av-jacobian` has empty `realized.statement` and `realized.steps`.

## Where the brief, the DAG or earlier work was wrong

The old searches missed the generic varying-ring module structure and coprojection formula in Mathlib's module stalk file. These declarations apply to every small filtered semilinear diagram, so the module axioms need no new proof.

LeanSearch was attempted for all new nodes but returned an internal server error; it is recorded as unavailable without a negative verdict. LeanFinder/Loogle and source grep worked. The clone omits fetched Stacks sources, so Tags 008T, 008S and 008U were read on the official Stacks website. No definition, statement or target was changed.

## New nodes

`lem-pc-topological-module-pullback-comparison`: proved canonical comparison isomorphism, in `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackComparison`.

`lem-pc-topological-pullback-common-representatives`: proved common-neighbourhood representative lemma for arbitrary ring and abelian presheaves, in `Sheaf.Algebra.Category.ModuleCat.Presheaf.TopologicalPullbackRepresentatives`.

`lem-pc-filtered-colimit-varying-ring-modules`: exact Mathlib leaf for `IsColimit.module` and `IsColimit.ι_smul`, with no new Lean module. Every new node inherits the original chapter and unit. No change record is required.

## Second reading by H1

1. **Interface preservation: PASS.** Read the full repository/sandbox diff of
   `TopologicalPullback.lean`. All three existing declaration signatures are unchanged;
   the bodies of `topologicalPullbackSectionMap` and `topologicalPullbackAdjunctionSpec`
   are identical. The only existing theorem receives a proof and an explanatory
   docstring update; the two added imports are proof-only. The new modules introduce
   only their named helper theorems. No statement, definition or target is adapted,
   so no change record is required.
2. **Proof and trust: PASS.** Compiled all three modules in import order through
   `lcompile.py --all`, without errors or warnings. Scanned every delivered module:
   no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern` or `sorryAx`.
   In a scratch module, explicitly printed axioms of the existing two definitions,
   the main theorem and both helper theorems: each lists exactly `propext`,
   `Classical.choice`, `Quot.sound`. No unfinished statement is introduced.
   Read the comparison proof from the filtered diagram through `hsmul`, `hsemi`,
   `unitM`, `hcLinear`, and the two inverse identities. `hcd` uses the abelian Hom
   bijection and `hdc` uses the module Hom bijection, so neither inverse identity
   assumes the comparison already invertible. The main proof then establishes
   naturality, the coprojection action, uniqueness and the exact underlying Hom formula.
3. **New intermediate statements: PASS.** Neither helper merely renames the item:
   common representatives concerns two independent colimits, while the comparison
   asserts invertibility of a specific adjunct and does not assert the item's natural
   isomorphism, multiplication uniqueness or Hom formula. Both are fully proved and
   have source/proof docstrings and matching nodes. For an empty open the top open
   still gives an index, and intersections remain valid; the same argument applies
   to empty spaces, a zero ring and a zero abelian presheaf. No nontriviality or
   nonempty-space hypothesis enters the proof. Read the generic `IsColimit.module`
   and `IsColimit.ι_smul` declarations in Mathlib's `ModuleCat/Stalk.lean`: they
   accept varying-ring semilinear diagrams, exactly the structure used here.
   Independently searched with LeanFinder for "left adjoint on modules along the
   inverse image ring has underlying left Kan extension of abelian groups", with
   Loogle for `Concrete.isColimit_exists_rep`, and with `rg` for underlying/abelian
   pullbacks and common representatives throughout both library roots. Returned
   change-of-rings adjunctions and the existing constant-coefficient étale sheaf
   comparison do not give either helper's statement. The existing Mathlib
   representative lemma is already used directly. No shorter matching result found.
4. **Top-down route and pruning: PASS after report correction.** The item uses
   Mathlib's existing abstract module adjunction; the only extra work is identifying
   its canonical underlying abelian comparison, computing the action and proving
   uniqueness. Public imports support signatures or unchanged definitions; stalk,
   filtered-colimit and concrete-colimit imports are proof-only. The direct import
   of Representatives in the main module is needed because Comparison's import of
   it is private. All three old dependencies removed from the item's `proof_deps`
   are now named in `## No longer needed`: category-colimit and commutative-ring
   representatives remain transitively used; integer-module colimit representatives
   are eliminated. Checked `dag/units/sk-def-av-jacobian.json`: both realized lists
   and the unit's step list are empty; no fixed unit route is bypassed.
5. **DAG and sources: PASS.** Read all four delivered nodes. Each `proof_deps`
   equals the union of its step `uses`; comparison's varying-ring-colimit leaf,
   representative helper and definition dependencies match the Lean construction.
   The main node changes only `proof`, `proof_deps`, `proof_origin`; the new nodes
   carry source, search, creation, ancestry, chapter/unit and Lean records, and the
   Mathlib leaf records the existing declarations rather than introducing duplicates.
   Independently read [Tag 008T](https://stacks.math.columbia.edu/tag/008T),
   [Tag 008S](https://stacks.math.columbia.edu/tag/008S), and
   [Tag 008U](https://stacks.math.columbia.edu/tag/008U): the filtered-colimit action,
   restricted-scalar direct image and unit-based Hom formula agree with the supplied
   proof. The comparison proof fills in the linearity checks left to the reader there.

**Changes by the second reader:** clarified the complete old-dependency accounting in
`## No longer needed`, distinguishing removal from the main node's direct dependencies
from elimination of a transitive dependency. Added this independent review and explicit
axiom verification. No Lean proof or node repair was needed.
