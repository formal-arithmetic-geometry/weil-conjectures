## What changed

The main declaration `AlgebraicGeometry.module_extensionByZero_stalk_maps` is reduced,
without changing its signature, to the three displayed conjunct groups. Added three
modules for outside vanishing, the inside natural comparison, and transition/counit laws.
The second reader proved `AlgebraicGeometry.ModuleExtensionByZeroStalkOutside` directly
from empty direct sums and Mathlib's sheafification stalk isomorphism. The other two
clauses remain named theorem holes. No definitions or existing statement signatures changed.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.module_extensionByZero_stalk_maps` by
conjunction assembly. Also proved the new intermediate declaration
`AlgebraicGeometry.ModuleExtensionByZeroStalkOutside`; it has no reachable `sorryAx`.

Added two holes:
- `AlgebraicGeometry.ModuleExtensionByZeroStalkInside`, node
  `lem-sc-module-extension-by-zero-stalk-maps-inside`.
- `AlgebraicGeometry.ModuleExtensionByZeroStalkTransitions`, node
  `lem-sc-module-extension-by-zero-stalk-maps-transitions`.

This is a decomposition, not a completed proof of the original theorem: one original
hole closed and two new holes added (syntactic net -1). The main declaration still
uses `sorryAx` through the two open lower theorems. The outside result uses only
`propext`, `Classical.choice`, and `Quot.sound`. No ledger-wide progress figure is claimed.

## No longer needed

Removed the main module's direct proof imports
`Sheaf.Topology.AbelianOpenExtensionByZeroStalks` and
`Sheaf.Topology.PresheafModuleStalkFunctor`. The abelian comparison remains a planned
proof dependency imported by the open inside lemma; its module is not globally pruned.
Removed the presheaf-stalk import from all three new modules: the statements and outside
proof use the existing `RingedSpace.moduleStalkFunctor`, not a new stalk construction.

The parent's old direct `proof_deps` were
`lem-sc-derived-open-restriction-adjunction-exact`,
`def-weil-presheaf-modules-sheafification`,
`lem-sc-topological-extension-by-zero-stalks`, and `def-weil-pbc-module-stalk`.
They are replaced as direct dependencies by the three new conjunct nodes. Adjunction,
sheafification, and abelian stalk comparison remain dependencies of the lower proof
plans, so they are not declared globally unnecessary. The module-stalk construction is
recorded under its actual node `def-pc-module-stalk-functor`; the duplicate presheaf-stalk
node is not used by these delivered declarations. No globally unreachable module is claimed.

## Where the brief, the DAG or earlier work was wrong

The first delivery's new node proofs cited the parent they were supposed to reduce,
which would create circular proof dependencies. Its node statements were placeholders,
its searches were absent, and its sorry docstrings had neither the new node tags nor
complete proofs. Its report did not disclose the negative hole net. The second reader
repaired these faults, and closed the outside lemma instead of leaving another hole.
The chosen adjunction is arbitrary; proofs of the inside/unit and transition/counit
clauses must use adjunction comparison or triangle identities, not assume its unit
is definitionally the usual direct-sum injection.

## New nodes

`lem-sc-module-extension-by-zero-stalk-maps-outside` states outside vanishing; its Lean
proof represents every germ over a neighborhood, uses the empty direct sum, and
transfers vanishing through sheafification. It has no remaining hole.

`lem-sc-module-extension-by-zero-stalk-maps-inside` states exactly the inside conjunct,
including scalar transport, naturality, and the germ-of-chosen-unit formula. Its proof
plan compares the canonical construction's adjunction with the chosen adjunction.

`lem-sc-module-extension-by-zero-stalk-maps-transitions` states exactly the transition
conjunct, including the top counit and inside stalk compatibilities. Its proof plan uses
the inside comparison and adjunction identities. Neither lower node cites the parent.
No change record is needed: existing signatures and definitions are unchanged.

## Second reading by R3

1. PASS: diffed the existing main module against the repository. Its declaration signature
   is byte-for-byte unchanged. All new modules state strict conjuncts; no definition changed.
2. PASS: compiled the four delivered modules in import order with `lcompile.py --all`.
   No errors or style warnings. Sorries occur only in the two named lower theorems.
   Explicit scratch `#print axioms` checks confirm the outside lemma has only allowed
   axioms; the main, inside and transitions declarations additionally use `sorryAx`.
   No axiom, unsafe, opaque, extern, implemented_by, or hollow definition is present.
3. PASS: checked each clause against the target and Stacks 00A7/00A5. Outside W=empty
   still gives the empty-sum argument; W=top makes outside vacuous. Inside W=empty is
   vacuous. For W=W' and W'=top, the transition claims are the adjunction identities,
   including the top counit identification. Zero modules and the empty space introduce
   no exception. Searched Mathlib using the recorded launcher searches and searched
   `lean/Sheaf` and upstream with alternative words. Mathlib supplies sheafification
   stalk preservation, used in the proved outside clause; the scheme-only extension
   theorem does not cover an arbitrary ringed space. LeanSearch was unavailable and
   is recorded as unavailable, not a negative mathematical result.
4. PASS: parent proof is the exact three-way assembly; its dependencies are the three
   new nodes. The lower plans contain no parent edge, preserve the original construction
   and unit route, and keep the existing `sk-thm-picard-duality` realized record unchanged
   (the item is a subordinate tool node, not a realized unit statement or step).
   Removed unused imports as listed above; no globally pruned module is asserted.
5. PASS: updated the parent proof/proof_deps/proof_origin, replaced placeholder statements,
   synchronized every new lean.statement to its actual full signature, supplied true search
   records, sources and complete proof docstrings, and removed circular dependencies.

Second reading changed: proved outside vanishing; repaired new node metadata and proof
docstrings; removed unused direct imports; shortened the assembly line; corrected the
report's decomposition accounting. No existing signature changed.

Sources checked: [Stacks 00A7](https://stacks.math.columbia.edu/tag/00A7) and
[Stacks 00A5](https://stacks.math.columbia.edu/tag/00A5).
