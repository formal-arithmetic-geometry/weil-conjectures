## What changed

Proved `CategoryTheory.exists_ext_rightDerived_cocycle_comparison` with its signature and
existing docstring unchanged. Added three fully proved private helpers in the same module:
`representedHomComplexIso`, `exists_ext_resolution_cocycle_iso`, and
`resolution_comparison_naturality`. The local comparison is constructed from explicit
isomorphisms, and its normalization determines every component by `extMk_surjective`.
Naturality follows on cocycle representatives; comparison maps lifting the identity
transfer normalization to every injective resolution.

Added proof-only imports of `Mathlib.Algebra.Homology.ConcreteCategory` (cycle constructors)
and `WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap` (application of an
additive functor commutes with extension by zero). The latter import is acyclic according
to `tools/import_direction.py may`. Updated the item's DAG proof to match the Lean proof.
No public signatures or definitions were changed, and no other module was adapted.

## Proved and sorry left

Closed the single original hole:
`CategoryTheory.exists_ext_rightDerived_cocycle_comparison`
(node `lem-sc-ext-right-derived-cocycle-comparison`). No holes added; no `sorry` remains
in the delivered module or its new private helpers. This is a complete proof, not a
decomposition. The theorem applies to degree zero, zero objects and zero cocycles with
no extra assumptions. Single-file compilation is clean. The delivery axiom probe accepts every declaration
with only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

No original import removed. No planned node or module pruned: the proof still uses
`lem-sp-derived-well-defined` through its Mathlib match `InjectiveResolution.isoRightDerivedObj`
and its naturality API. The public existence theorem in
`Sheaf.CategoryTheory.Abelian.ExtRightDerivedHom` is not imported: its API does not specify
normalization. No dependency on that module was present in the original item, so this is
not counted as pruning. No additional Sheaf dependency or new node is needed.

## Where the brief, the DAG or earlier work was wrong

The resumed sandbox already contained the complete proof. Checked its construction,
naturality, arbitrary-resolution normalization, unchanged public signature, dependency
node and unit route. Scoped the added `open CochainComplex HomComplex` commands to
the two private helpers: the initial dry run classified the file-wide command as an
interface change. No mathematical discrepancy found. The plan is implemented with one simplification:
naturality is proved directly from normalization and surjectivity of `extMk`, rather than
by constructing a second Hom-complex postcomposition map. `HasForget₂ Ab Ab` is installed
locally as the identity only inside the proved naturality helper to use `cyclesMk`;
no instance is exported. The unit route is unchanged (`sk-thm-curveestimate` has no
realized proof step at this helper). Searches used LeanFinder, Loogle and Mathlib grep;
LeanFinder returned the Ext/cohomology-class API, Loogle did not recognize the queried
short identifier, and grep confirmed `extEquivCohomologyClass_extMk`. The existing
right-derived-Hom proof was read but its unnormalized existence theorem was insufficient.


## Second reading by Q3

1. Compared the sole delivered module against the repository with `diff -u` and
   checked the original theorem signature byte for byte with a script. The original
   signature and docstring are unchanged; the changes are three private helpers,
   two plain proof-only imports, declaration-scoped options and the proof body.
   No definition or public interface was altered. Verdict: pass.
2. Compiled the delivered file with `lcompile.py`: clean, 3.1 seconds. Read all three
   helpers and the final proof. A scratch copy with `#print axioms` for each helper
   and the public theorem reports only `propext`, `Classical.choice`, `Quot.sound`.
   A source scan finds no `sorry` or forbidden declaration mechanism. The complex
   isomorphism is constructed degreewise, not chosen from an unproved existence
   theorem. The `choose t` in the final proof uses the fully proved normalized
   local existence theorem. Verdict: pass.
3. No statement was split off and no new hole or node was added. Checked the local
   comparison on degree zero: extension and restriction use `extendHomologyIso`
   at `j = p` without a positive-degree premise. Zero cocycles and zero objects
   are covered by the same equations and monicity argument. The naturality helper
   has precisely the normalization hypotheses supplied by the local theorem;
   `extMk_surjective` supplies all representatives. Verdict: pass.
4. Read `ExtRightDerivedHom.lean`: its public `Nonempty` isomorphism does not assert
   cocycle normalization and cannot replace this proof. Independently searched
   Mathlib with `msearch.py grep` for `extMk_surjective|isoRightDerivedObj_inv_naturality`
   and read the injective Ext definitions and representative/naturality lemmas,
   as well as `RightDerived.lean` lines 114--149. No shorter public normalized
   comparison was found in the surrounding Sheaf modules. The three original
   public imports support the public signature; `ConcreteCategory` supplies
   `cyclesMk` and `ExtendMap` supplies `mapExtendIso`, both used only in proofs.
   No old proof dependency is unused. Checked `sk-thm-curveestimate.realized`:
   its statement is `thm-sc-proper-cohomology` and it has no realized proof steps;
   this helper bypasses no unit step. Verdict: pass.
5. Compared the node versions: only `proof` and `proof_origin` changed, while
   `proof_deps` remains `lem-sp-derived-well-defined`. Read that dependency's
   Mathlib match: `InjectiveResolution.isoRightDerivedObj` is exactly the
   resolution-computation API used here, including its inverse naturality lemma.
   The new three-step proof matches the local construction, naturality by
   representatives, and identity-lift comparison in the Lean code. The node's
   stored Lean statement still matches the unchanged theorem. Verdict: pass.

Second reading changed only this report by adding the independent checks above;
no Lean or DAG repair was needed. Closed: `CategoryTheory.exists_ext_rightDerived_cocycle_comparison`.
Added holes: none. Pruned modules: none.
