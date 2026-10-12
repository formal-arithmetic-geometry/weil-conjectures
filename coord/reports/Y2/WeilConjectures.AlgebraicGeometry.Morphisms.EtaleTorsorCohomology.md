## What changed

Proved `AlgebraicGeometry.Scheme.EtaleTorsor.exists_forall_cohomologyMap_eq_zero_iff`
without changing its signature. Added proof-only imports of
`WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent`, and
`Sheaf.CategoryTheory.Sites.EtaleTorsorH1Functoriality`.

Choose a torsor using the existing canonical class map's surjectivity. Apply the existing
inverse-image clause of torsor-H¹ functoriality, then its zero-class/section criterion.
Mathlib's Kan extension comparison identifies the inverse-image representable with the
representable of the base-changed total space. The last two implications are proved directly
by composing with pullback projections and constructing `pullback.lift s id`.

The unit's classification and finite-etale representability route stays in use through
`bijective_classH1`; no unit step is bypassed. The functoriality theorem from the curve
chapter is used as a generic site-theoretic tool, not a replacement for the unit's route.

## Proved and sorry left

Proved the module's only original sorry:
`AlgebraicGeometry.Scheme.EtaleTorsor.exists_forall_cohomologyMap_eq_zero_iff`.
No sorry remains in this module; no new sorry or new Lean module is introduced.
The imported `CategoryTheory.Sheaf.Torsor.etale_torsor_h1_functoriality` is still a stated
sorry in its existing module/node `lem-sc-etale-torsor-h1-functoriality`; this delivery uses
its first clause. Existing dependencies of `bijective_classH1` are likewise unchanged.

Local compilation succeeds. The delivery dry run checks the server and preflight.
The statement covers arbitrary f and arbitrary finite abelian M: no connectedness, nonempty
base, or étaleness of f is assumed. On an empty source the terminal section and lift are both
unique; for the trivial group the argument specializes without any extra instance or choice
of a nonzero element. For f=id the criterion is the original zero-class/section criterion.

## No longer needed

No original import is removed: both public imports are needed by the theorem's signature.
The second reader removed the redundant proof-only import
`Mathlib.CategoryTheory.Limits.Presheaf`: its comparison lemma is already available
through the remaining imports. This does not prune that module from the target closure.
No previously imported dependency node or module is pruned.
A separate construction of scheme-level pullback torsors and a separate naturality theorem
for their scheme-level class maps are unnecessary: set inverse image and the Mathlib
representable comparison already supply the needed argument. No such new modules or nodes
are introduced. No global pruning claim is made for dependencies used by other modules.

## Where the brief, the DAG or earlier work was wrong

There was no node whose `lean.module` recorded this module, and the audit lists the theorem
with `nodes: []`. Added `lem-sbc-torsor-cohomology-lift-criterion` to record the existing
statement and the actual proof route, rather than modifying the broader
`sbc-prop-torsors-h1` statement or erasing its connectedness clauses.
The original docstring's claim that naturality was unavailable is stale: the existing
`etale_torsor_h1_functoriality` states exactly the sheaf-level pullback compatibility needed.
LeanSearch returned HTTP Internal Server Error; recorded as unavailable, not a negative
search. LeanFinder/Loogle/grep and blueprint searches were also performed.
The literature blueprint file is absent on this clone; its full proof is recorded in the
existing DAG node and was read there. No new unproved result relies on an invented source.

## New nodes

`lem-sbc-torsor-cohomology-lift-criterion` records the module's existing theorem, now proved,
as the precise vanishing/lifting consequence of the unit's naturality clause. It does not
add a new Lean statement or move a sorry. Its four proof steps record representative choice,
existing sheaf-torsor functoriality, the Mathlib representable comparison, and the explicit
pullback projection/lift argument. Blueprint searches for `torsor pullback` and `torsors`
found the broader classification statements but no node for this exact criterion.
No change records are needed: no definition, signature, or public import changes.

## Second reading by Y2

1. Compared the sole delivered Lean module with the repository using `diff` and the
   declaration parser. The existing theorem signature is byte for byte unchanged;
   no definition, hypothesis, conclusion, or public import changes. Verdict: passes.
2. Compiled the file locally without errors or warnings. No sorry, forbidden declaration,
   or hollow definition occurs in this module. A scratch copy with `#print axioms` reports
   only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter comes from
   existing open dependencies, including torsor functoriality and finite locally constant
   representability, as disclosed above. This closes the local proof, not its entire
   transitive axiom closure. Verdict: passes the stage-3 reduction requirement.
3. No statement is split off and no new Lean declaration is added. The new node records
   the existing theorem rather than a renamed restatement. Independently searched
   LeanFinder for sections of pulled-back representables, Loogle for the Kan extension
   comparison, and the local library/Mathlib with section, vanishing, and class-map terms.
   The existing Mathlib comparison is already used; no shorter complete proof was found.
   Checked the empty source, identity morphism, trivial coefficient group, and zero class:
   the section/lift argument uses no nonemptiness or connectedness assumptions.
   Verdict: passes.
4. Read the reduction from the target downward: classification chooses the representative,
   existing functoriality supplies its pulled-back class, the representable comparison
   identifies sections, and the pullback projections/lift prove both implications.
   Both remaining proof imports supply declarations used in this argument. Removed the
   redundant Mathlib import after a scratch compilation without it succeeded. No old
   proof dependency is pruned. Read `dag/units/sk-prop-input-torsors.json` and its imported
   section text: classification and finite-etale representability remain in use; the
   connectedness clause is outside this criterion. The unit's `realized` arrays were
   already empty in the repository; this delivery neither changes them nor bypasses a
   unit step. This pre-existing bookkeeping gap remains for the maintainer.
   Verdict: proof route preserved; existing unit-record gap reported.
5. Read the new node and the three cited dependency nodes alongside their Lean modules.
   Its four steps and `proof_deps` describe the proof, including the non-elementary
   functoriality dependency; the declaration text agrees with Lean. Source, origin,
   creation, searches, chapter/unit, and blueprint provenance are present. No existing
   node is changed. Verdict: passes.

Second-reading changes: removed the redundant proof-only Mathlib import and corrected
this report to record the removal, axiom closure, and existing empty unit realization.
The mathematical proof and theorem signature needed no repair.
