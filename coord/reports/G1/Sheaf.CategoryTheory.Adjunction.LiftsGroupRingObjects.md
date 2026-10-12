## Worker report

Second-reader repair of the returned delivery. The original theorem's signature
is byte-for-byte unchanged. Its group conjunct is now proved from Mathlib; its ring
conjunct is reduced to two distinct construction steps. This is a partial proof:
`liftsGroupRingObjects` still has `sorryAx` through the two ring obligations.

## What changed

`LiftsGroupRingObjects.lean` now installs Mathlib's right-adjoint limit-preservation
instance directly and combines the two branch assemblies. Its existing public
imports are unchanged; all added imports are private proof imports.

Four new modules each carry their own statement and DAG node:
`LiftedCommGrpBranch`, `LiftedCommRingBranch`, `FiniteProductRingFunctor`, and
`RingHomEquivCore`, under `Sheaf.CategoryTheory.Adjunction`.

The group branch uses `Functor.mapCommGrp` and `Adjunction.mapCommGrp`, proves the
operation equations by rewriting the canonical comparisons, computes the underlying
unit/counit and hom-equivalence, and proves the adjunct criterion using the inverse
equivalence. The ring assembly applies transport separately to L and R, obtains a
restricted `CoreHomEquiv`, constructs the adjunction with `mkOfHomEquiv`, and proves
the final adjunct criterion by forward/inverse equivalence and injectivity.

The two open statements are strictly smaller steps: transport for a single functor
(with no adjunction hypothesis or conclusion), and restriction of a natural
hom-bijection for already supplied ring lifts (with no assertion constructing the
lifts). The original open branch restatements have been eliminated.

The redundant `rightPreservesFiniteProducts` wrapper and its new node were removed.
The obsolete change record was removed: no existing statement or definition changes.

## Proved and sorry left

Sorry-free declarations: `CategoryTheory.Adjunction.liftedCommGrpBranch`,
`CategoryTheory.Adjunction.liftedCommRingBranch`, and the existing
`CategoryTheory.Adjunction.liftsGroupRingObjects`. Only the first is independent of
open obligations; it uses exactly `propext`, `Classical.choice`, and `Quot.sound`.
The latter two also use `sorryAx` through the following two named obligations:

- `CategoryTheory.Adjunction.finiteProductRingFunctor`, node
  `lem-weil-pbc-finite-product-ring-functor`, in `FiniteProductRingFunctor.lean`.
- `CategoryTheory.Adjunction.ringHomEquivCore`, node
  `lem-weil-pbc-ring-hom-equiv-core`, in `RingHomEquivCore.lean`.

These are the only two literal `sorry`s. Each is exactly `:= by sorry`, has a source
and complete natural-language construction proof, and has a matching node.
All five modules compiled locally in import order without warnings. Scratch copies
with `#print axioms` verified every delivered theorem individually; no axiom beyond
the permitted three and the explicitly accounted-for `sorryAx` occurs.

## No longer needed

No existing import was removed: the two original public Mathlib imports are needed
by the existing signature. The four old direct parent proof dependencies below
are replaced by the new branch nodes, and remain used in the support route:

- `lem-weil-pbc-adjunction-lifts-abelian-group-objects`: used by the proved group branch.
- `def-weil-category-product`: used by single-functor ring transport and restriction.
- `lem-weil-pbc-adjunct-counit-identity`: used in the restriction construction.
- `lem-weil-pbc-adjunction-of-natural-bijection`: used by ring assembly's `mkOfHomEquiv`.

`lem-weil-pbc-right-adjoint-preserves-limits` remains a direct parent dependency.
No old dependency module is globally pruned. The unused newly proposed
`lem-weil-pbc-right-preserves-finite-products` and its wrapper declaration are
removed rather than duplicating the existing Mathlib leaf.

## Where the brief, the DAG or earlier work was wrong

The earlier repair did not address the substantive return: it left both complete
parent conjuncts as unproved branch restatements. The group branch is now actually
proved. The ring proof is now an assembly from single-functor transport and
hom-bijection restriction, matching the original transport-then-adjunct route.

The earlier searches were fabricated exact-name searches and missed an existing
Mathlib group lift. Real searches through msearch.py used different terminology,
Loogle patterns, and source grep; their queries and digests are recorded in the
new nodes and searches.jsonl. LeanSearch returned an HTTP internal-server error;
this is recorded as unavailable, without a mathematical verdict. LeanFinder,
Loogle, and source grep found the group API and ring object definitions but no
existing general ring transport functor or ring hom-bijection restriction.

The previous DAG statements referred to displayed Lean conclusions instead of
stating those conclusions. They now introduce the categories, functors,
preservation assumptions, operations, comparisons, and all concluding equations.
The proof fields now describe the actual proofs or the precise remaining step.
There are no circular statement dependencies on the parent.

The local Stacks source file is absent on this machine. Source verification used
[Stacks Project Proposition 00YV](https://stacks.math.columbia.edu/tag/00YV), which
supplies the transport construction and restriction argument for algebraic
structures. The detailed comparison and naturality arguments are supplied here.

## New nodes

`lem-weil-pbc-lifted-comm-group-branch` in `LiftedCommGrpBranch.lean` is proved from
Mathlib's existing group-lifting leaf, including all comparison and adjunct clauses.

`lem-weil-pbc-lifted-comm-ring-branch` in `LiftedCommRingBranch.lean` is proved by
combining the following two strictly smaller construction statements and
Mathlib's natural-hom-bijection constructor.

`lem-weil-pbc-finite-product-ring-functor` in `FiniteProductRingFunctor.lean` states
single-functor transport, including strict forgetting and all five operations.
Its documented proof transports all ring laws by induction on algebraic terms.

`lem-weil-pbc-ring-hom-equiv-core` in `RingHomEquivCore.lean` states restriction of
the natural hom-bijection for supplied transported functors, with the forward and
identity formulas. Its documented proof uses comparison compatibility of unit and
counit, functoriality, and the original adjunct inverse identities.

No change record is needed: existing signatures, definitions, and public imports
are unchanged. The unit `sk-def-exchange` and all its `realized` fields are unchanged.

## Review by G1

Source, hypothesis/clause, dependency, edge-case, and repair checks were repeated
independently during the second reading, as recorded below.

## Second reading by G1

1. Compared every delivered module with the repository. The existing
   `liftsGroupRingObjects` signature is byte-for-byte unchanged. There are no
   definition changes or added public imports in the existing module. The other
   four modules are new and each has its own node. Verdict: pass.
2. Compiled all five modules through lcompile.py, without errors or warnings, and
   printed the axioms of every declaration in scratch copies. The group branch
   uses only the permitted three axioms; the two open ring obligations and their
   consumers additionally use `sorryAx`. No forbidden declaration, hollow
   definition, or anonymous sorry remains. Verdict: pass for the stated partial scope.
3. Examined both new open statements mathematically and searched Mathlib and the
   upstream/project sources by concepts, rather than new declaration names. A
   single functor's transport has neither an adjunction assumption nor conclusion;
   hom-bijection restriction assumes the lifts already exist. Neither restates the
   parent or an entire parent conjunct. Identity functors reduce the comparison
   equations to the original operations; the terminal one-object category permits
   the zero ring, so no nontriviality hypothesis is silently required. The core's
   unit/counit argument uses only the supplied operation equations and works even
   with arbitrary supplied braidings. Verdict: true, exactly sufficient, and smaller.
4. Took the Mathlib route for groups and right-adjoint preservation. All added
   imports in the existing module and the ring assembly are proof-only; public
   imports in the new statements are needed for their types. Listed every old
   parent dependency no longer used directly, and where it is still used below.
   Checked `dag/units/sk-def-exchange.json`: the item is below the unit's route and
   no realized statement or step is bypassed. Verdict: pass.
5. Checked all Lean records against their exact declaration signatures and checked
   that each node's proof_deps is the union of proof-step uses. Parent metadata
   follows its actual preservation/group/ring composition; group and ring nodes
   follow the Mathlib and transport/restriction proofs respectively. New statements
   are self-contained and have source, proof, searches, creation, unit, chapter and
   blueprint-ancestor records. Verdict: pass.

Changes made in this reading: proved the group branch; replaced the ring branch
restatement by transport/core restriction and a proved assembly; moved every new
statement into its own module; removed the duplicate preservation wrapper;
replaced fabricated searches and incomplete statements/proof metadata; corrected
pruning and axiom accounting; removed the inapplicable change record.
