## What changed

Proved `AlgebraicGeometry.kInjective_of_restrict_open` in
`lean/Sheaf/Algebra/Homology/KInjectiveRestrictOpen.lean`, without changing its
statement or imports. The proof follows the existing two-step DAG plan and
Stacks Tag 08BS: unpack `open_restriction_adjunction_exact X U`, install the
finite-limit and finite-colimit preservation instances for extension by zero,
and use its adjunction to obtain preservation of zero morphisms. Mathlib's
`Functor.additive_of_preserves_binary_products` then gives additivity, and
`Functor.preservesHomologyOfExact` supplies homology preservation by instance
synthesis. Apply the already proved
`CategoryTheory.Adjunction.preservesKInjectiveComplexes` and infer the
K-injectivity of the termwise restriction of `I`.

Searches through the launcher used LeanFinder (restriction of a K-injective
complex to an open), Loogle (`CochainComplex.IsKInjective`), and grep
(`IsKInjective.*restrict|restrict.*IsKInjective`). Mathlib has general
K-injective results, but no open-restriction specialization. Source-library
search found the generic right-adjoint preservation theorem already named by
the node. The unchanged DAG correctly describes the delivered argument, so
no node edit is needed. The unit's realized statement and step lists are empty;
this proof retains both planned dependencies and bypasses no unit step.

## Proved and sorry left

Proved the module's only former sorry:
`AlgebraicGeometry.kInjective_of_restrict_open`
(node `lem-sc-derived-k-injective-restrict-open`). No sorry remains in the
item's module, and no new sorry or helper declaration is introduced.

The existing imported theorem
`AlgebraicGeometry.open_restriction_adjunction_exact`
(node `lem-sc-derived-open-restriction-adjunction-exact`) is now proved in the
repository, using the still-open
`CategoryTheory.SheafOfModules.localizedModule_adjunction_exact`. This delivery
proves the requested theorem from the existing exact-adjunction dependency;
it does not claim that the whole transitive proof is closed. The generic
preservation theorem in the source library is already proved.

## No longer needed

None. Both existing proof dependencies remain necessary:
`lem-sc-derived-open-restriction-adjunction-exact` and
`lem-weil-pbc-right-adjoint-preserves-kinjective`. No import, node, or module
was removed. The Mathlib import supplies the K-injectivity notion appearing
in the statement; the open-restriction import supplies the ringed-space and
module-category interfaces as well as the exact adjunction.

## Where the brief, the DAG or earlier work was wrong

No mathematical or signature discrepancy was found. The Lean glue requires
registering `G.IsLeftAdjoint` from `adj.isLeftAdjoint` before deducing
additivity; finite-limit and finite-colimit preservation alone did not let
instance synthesis find `G.PreservesZeroMorphisms` at that point. The
adjunction supplies it without any additional statement or hypothesis.


## Second reading by T2

1. PASS: compared the only delivered module against the repository with `diff`.
   The sole change replaces the theorem's `sorry` with its proof. The existing
   declaration signature is byte for byte unchanged; there are no definitions,
   new declarations, adapted modules, node files, or change records.
2. PASS: compiled the module locally through `lcompile.py`, without errors or
   warnings (3.0 s). Searched the delivered Lean for forbidden constructs and
   sorries; none occur. Compiled a scratch copy with
   `#print axioms AlgebraicGeometry.kInjective_of_restrict_open`: exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The latter is from
   existing open dependencies, not a new or residual sorry in this delivery.
3. PASS: no statement is split off and no new statement requires a node or
   duplicate search. Read the exact-adjunction theorem and the upstream generic
   preservation proof. Extension by zero is the left adjoint and restriction
   the right adjoint, with exactness supplying homology preservation. The
   argument applies also to the empty and full opens and to the zero complex;
   no nonemptiness or boundedness assumption is introduced.
4. PASS: the proof applies the existing generic preservation theorem directly,
   after installing the exactness and additivity instances. Checked Mathlib's
   K-injective declarations and searched both Lean roots for restriction
   specializations; no shorter existing specialization was found. Both planned
   proof dependencies are used, so `No longer needed: None` is complete. The
   upstream import is proof-only and already plain `import`; both public imports
   provide statement interfaces. The unit `sk-thm-picard-duality` has empty
   realized statement and step lists, and the original two-step route is kept.
5. PASS: read node `lem-sc-derived-k-injective-restrict-open`, its `proof`,
   `proof_deps`, `proof_origin`, Lean record, and its unit's `realized` fields.
   The unchanged node describes exactly the exact-left-adjoint reduction and
   application of the generic K-injective preservation theorem in the proof.
   No DAG edit is necessary.

Second reading changed only this report: corrected the outdated claim that
`open_restriction_adjunction_exact` itself still contains sorry, distinguishing
its proved body from the open localized-adjunction dependency. The Lean proof
was retained unchanged.
