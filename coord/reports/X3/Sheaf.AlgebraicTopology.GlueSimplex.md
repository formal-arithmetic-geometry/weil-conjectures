## What changed

Proved `SSet.glue_simplex` in `lean/Sheaf/AlgebraicTopology/GlueSimplex.lean`, with its
signature and public imports unchanged. Added the proof-only import
`Mathlib.CategoryTheory.Limits.Types.Pushouts`.

The proof follows the degreewise argument of Stacks Project Lemma 018R
(https://stacks.math.columbia.edu/tag/018R, read online because the local source is absent).
The preimage of U under the simplex map is exactly the boundary: all boundary
nondegenerate generators have degree below n, and the preimage is proper since x is
outside U. Nondegenerate decomposition identifies every new simplex as an image of x;
uniqueness gives injectivity off the boundary. Mathlib's Types pushout criterion and
`CategoryTheory.IsPushout.of_forall_isPushout_app` assemble the square.

Updated the item's DAG proof, dependencies and proof origin to this route. The unit
`sk-prop-h2` has no realized entry involving this item; no unit statement or step changes.

## Proved and sorry left

Closed the one original hole: `SSet.glue_simplex`
(node `lem-weil-pbc-simplicial-set-glue-simplex`). No holes added; no sorries remain.
This is a complete proof, not a decomposition into unproved statements.

The module compiles through `lcompile.py`. A temporary `#print axioms SSet.glue_simplex`
reported exactly `[propext, Classical.choice, Quot.sound]`; the diagnostic was then removed.
The proof covers n = 0 without a separate case, using the boundary dimension bound.

## No longer needed

Removed the proof dependency `lem-weil-pbc-simplex-face-factorization` from this item's
node. Its explicit missing-face factorization is replaced by Mathlib's boundary dimension
and proper-subcomplex API. This is local pruning; other users of that node are unaffected.

No original import was removed: all three public imports support the existing signature
or its simplicial-set API. The candidate relative skeleton/coproduct attachment route
`Mathlib.AlgebraicTopology.SimplicialSet.Skeleton` is unnecessary and is not imported.
A temporary redundant proof import of `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`
was removed after checking that Types.Pushouts already supplies the required theorem.
No project dependency modules or new modules are needed by this proof.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original DAG's explicit construction of a natural extension
is unnecessary: the existing degreewise pushout criterion gives the universal property
from pullback, coverage, and injectivity off the boundary. The original docstring retains
its valid expanded mathematical argument; the updated node records the implemented route.
The local Stacks TeX path is absent, so Lemma 018R was checked at its canonical online tag.

## Second reading by X3

1. **Interface — pass.** Read the complete repository/sandbox diff and compared the
   bytes from `theorem glue_simplex` through its conclusion: the signature is identical.
   The only Lean changes are the proof and the plain, proof-only import of
   `Mathlib.CategoryTheory.Limits.Types.Pushouts`. No definitions, public imports, other
   modules, or change records were added or changed. Read [Stacks Lemma 018R,
   lemma-glue-simplex](https://stacks.math.columbia.edu/tag/018R): `hx`, `hbelow`, `hat`,
   and `habove` respectively express the missing simplex and its three hypotheses;
   the conclusion supplies its boundary restriction and pushout square. Presenting
   both simplicial sets as subcomplexes of `X` does not change this inclusion argument.

2. **Proof and axioms — pass.** Recompiled the delivered module with `lcompile.py`.
   Also compiled a scratch copy with `#print axioms SSet.glue_simplex`; it reports
   exactly `[propext, Classical.choice, Quot.sound]`. Scanned the whole delivered
   source: no `sorry`, prohibited axiom,
   execution escape hatch, or hollow definition. The local map `a` is the actual
   Yoneda map of `x`, and `b` is its explicit `Subcomplex.lift`, so no arbitrary data
   is selected from an unproved existence theorem. Read the Mathlib definitions and
   criteria used: `boundary`, `stdSimplex.eq_boundary_iff`, `exists_nonDegenerate`,
   `unique_nonDegenerate_map`, `Types.isPullback_iff`,
   `Types.isPushout_of_isPullback_of_mono'`, and `IsPushout.of_forall_isPushout_app`.
   The pullback check identifies membership in the boundary with membership of the
   image in `U`; coverage uses all three degree hypotheses; injectivity uses the
   nondegeneracy proved from `hbelow` and `hx`. The uniqueness lemma only requires
   the first operator to be epi, exactly what the proof supplies.

3. **Split statements and edge cases — pass.** No new statement or hole is split
   off. For `n = 0`, the boundary dimension bound gives no nondegenerate generators;
   the proper-preimage argument still applies, every map to `[0]` is surjective,
   and the square is the asserted coproduct. Empty `U` is allowed in this case.
   For `n = 1`, both endpoints lie in `U`, possibly with equal images; the argument
   only requires injectivity outside the boundary, so it also handles an attached
   loop. It assumes neither finiteness nor nonemptiness of `U`.

4. **Route, imports, and pruning — pass.** Searched Mathlib with the alternative
   terms `attach|attachment|pushout|adjoin` through `msearch.py`, and searched the
   library and upstream source for simplex gluing and tag 018R. Read the relative
   skeleton construction, including `Cell.preimage_map` and
   `relativeCellComplexOfMono.isPushout`: using it would additionally require
   identifying two relative skeleta and their singleton cell coproduct. The present
   direct argument already uses its simpler boundary and Types criteria. The added
   import is used only by the proof; the original public imports provide notions
   in the signature. The complete removed-dependency set is precisely
   `lem-weil-pbc-simplex-face-factorization`, already listed above; no original
   module import was removed. Read `dag/units/sk-prop-h2.json`: its `realized`
   statement and step lists are empty, and no unit route is changed.

5. **DAG — pass.** The only changed node fields are `proof`, `proof_deps`, and
   `proof_origin`. Checked that `proof_deps` is exactly the union of the proof
   steps' `uses`. Step 1 matches `hnd`, `hpre`, `hbound`, and `hw`; step 2 matches
   `hcover`; step 3 matches the degreewise pullback and uniqueness checks; step 4
   matches the two Mathlib pushout criteria. Read the decomposition dependency's
   Mathlib match and verified its existence and uniqueness declarations in
   `Degenerate.lean`. No new node fields require review.

Second-reading changes: added this independent audit and its search record; no
Lean or DAG repair was needed.
