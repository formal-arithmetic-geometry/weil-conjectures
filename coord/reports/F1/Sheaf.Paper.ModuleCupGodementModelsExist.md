## What changed

Replaced the proof of `moduleCup_godement_models_exist` without changing its signature
or docstring. Added `Sheaf.Paper.ModuleCupGodementCosimplicialExists` and
`Sheaf.Paper.ModuleCupGodementAugmentation`. Both are proof-only imports of the item;
the latter publicly imports only ModuleCupGodementModel, which its statement needs.
The augmentation is proved using concrete unit naturality and Mathlib's
`HomologicalComplex.mkHomFromSingle`; the cosimplicial realization remains open.
No definition or existing public interface changed; no change record is needed.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Scheme.Modules.moduleCup_godement_models_exist`.
Added one hole: `AlgebraicGeometry.Scheme.Modules.moduleCup_godement_cosimplicial_exists`
(node `lem-sc-module-cup-godement-cosimplicial-exists`).
Proved `AlgebraicGeometry.Scheme.Modules.moduleCup_godement_augmentation_exists`
(node `lem-sc-module-cup-godement-augmentation-exists`), closing the first worker's
proposed additional hole before delivery. The private `unit_naturality` helper is
proved and is used by the augmentation proof.
The original item is reduced to a strictly smaller construction: this is a
decomposition, not an axiom-complete proof of the original item. Relative to the
repository, one hole is closed and one is added, net zero. No sorry in a definition.

## No longer needed

No original import is removed and no module is pruned. The original direct proof
nodes `def-sc-module-cup-godement-model` and
`def-sc-module-cup-godement-codegeneracies` are replaced by the two construction
nodes as direct proof dependencies; both definitions remain needed transitively
and by the target signature. The augmentation no longer imports the cosimplicial
existence module or the codegeneracy module. Removed the unused helper from the
item, moving it to the augmentation where it is used.

## Where the brief, the DAG or earlier work was wrong

The first worker left the augmentation sorry despite already proving the essential
naturality helper. The target's DAG record was not updated to its actual proof;
the augmentation node described an entire monad construction instead of its own
argument. Both records now follow the code. The first worker's interface change
record was unnecessary: new statements in proof-only imports change no existing
public signature.

## New nodes

`lem-sc-module-cup-godement-cosimplicial-exists` states realization of the prescribed
terms, cofaces and codegeneracies, without the augmentation. Its source and full
monad/normal-form argument are in its docstring and node. It remains open.

`lem-sc-module-cup-godement-augmentation-exists` states and proves extension of the
germ to the alternating complex for any object with the prescribed terms and
cofaces. It requires no codegeneracy hypothesis and is strictly part of the target.
There are no change records.

## Second reading by F1

1. Compared the item with the repository by diff: the existing theorem signature
   and docstring are byte-for-byte identical. Changes are proof bodies, private
   helper placement and proof-only imports. New modules contain no altered existing
   declarations or definitions.
2. Compiled all three modules locally in import order without errors or warnings.
   Only the named cosimplicial realization has sorry. No axiom, unsafe, opaque,
   implemented_by or extern occurs, and no definition contains sorry. Axiom probes
   are checked in the delivery dry run; explicit print-axioms checks are recorded
   below. No data definition chooses witnesses from unproved mere existence.
3. Checked both lower statements: realization specifies only the cosimplicial
   operators; augmentation applies to any such cofaces and needs no degeneracies.
   At degree zero the two insertions compose equally by proved unit naturality;
   the degree-zero augmentation is constructed explicitly. Empty schemes and zero
   sheaves impose no nonempty or nonzero hypotheses. Searched Lean sources and
   Mathlib with grep, LeanFinder and Loogle using alternative queries. Generic
   from-single constructors exist and are used; no duplicate Godement theorem was
   found. The remaining sorry has a source, complete proof docstring and node.
4. The route separates cosimplicial realization from augmentation; neither lower
   statement restates the target. Imports are limited to statements' dependencies
   and the item's two proof lemmas. The original unit sk-prop-av-cube and its
   realized record are unchanged; the item realizes none of its steps and no unit
   route is bypassed. The No longer needed section lists the old direct proof
   dependencies and explains why they remain needed transitively.
5. Updated the original node's proof, proof_deps and proof_origin. Checked new node
   signatures against Lean, chapter/unit inheritance, creation and blueprint data,
   sources and search records. Replaced the inaccurate augmentation plan by the
   actual naturality/alternating-differential/from-single proof.

Changes by second reader: proved augmentation; moved and used naturality helper;
removed unnecessary public dependency and change record; updated DAG proof plans;
corrected hole accounting and pruning report.
