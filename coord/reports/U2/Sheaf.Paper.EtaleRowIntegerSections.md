## What changed

Replaced the hole in `AlgebraicGeometry.Etale.ceIntegerSectionsIso_naturality`
with a Lean argument combining two strictly earlier squares. The first computes
pullback and coefficient maps on unevaluated Hom-complex homology. The second
commutes degreewise evaluation with the sections unit for arbitrary integer
complexes, without injectivity or augmentation hypotheses. The parent applies
the homology functor, unfolds the class/sections comparison, composes the squares,
and cancels the comparison isomorphisms. Existing public signatures, definitions,
and visibility are unchanged.

## Proved and sorry left

Closed the original hole `AlgebraicGeometry.Etale.ceIntegerSectionsIso_naturality`
by decomposition. Proved the new intermediate theorem
`AlgebraicGeometry.Etale.ceExtHomologySquare` in
`Sheaf.Paper.EtaleRowExtHomologySquare` from the existing coefficient-cocycle
formula, using the original private quotient-descent helpers.

Added exactly one hole: `AlgebraicGeometry.Etale.ceComplexSectionsSquare`, in
`Sheaf.Paper.EtaleRowSectionsEvaluationSquare`, node
`lem-weil-pbc-row-sections-evaluation-square`.

This remaining square contains no Ext, resolutions, or augmentation compatibility;
it is strictly a part of the argument, not an alias of the parent. This is one
original hole closed and one lower hole added (net zero), a decomposition rather
than an axiom-free proof of the dependency closure. The new Ext theorem is proved
from existing library declarations. The evaluation theorem has its source,
complete proof in words, and matching DAG node. The unfinished evaluation
obligation is exported rather than left inside the parent proof.

## No longer needed

Removed the parent's direct proof imports of
`Sheaf.CategoryTheory.ExtCoefficientCocycle`,
`Sheaf.AlgebraicGeometry.ExtPullbackHomComplex`, and
`Sheaf.AlgebraicGeometry.ConstantSheafPullbackTranspose`.
They remain relevant transitively to the two intermediate squares, so no entire
module or existing node is pruned. Moved the parent's private generic cocycle
and homology descent helpers into the new Ext-square module, where they prove
that intermediate theorem.
The unit's ordinary integer-row route remains intact. No extension-by-zero
transport is needed in this particular integer-indexed square.

## Where the brief, the DAG or earlier work was wrong

No statement was found false or changed. The original three-step plan is valid;
it required a substantial arbitrary-resolution Ext naturality computation and
a separate evaluation calculation. Those steps are now explicit intermediate
items. The missing compiled ExtCoefficientCocycle dependency at the start was
resolved by the compilation service. The Ext calculation is completed in its new module. The evaluation calculation
could not be completed and integrated within this session; its proof plan is
recorded for the next worker. No other held module was adapted.

## New nodes

`lem-weil-pbc-row-ext-homology-square` records the coefficient/pullback square on
Hom-complex homology, before sections evaluation (parent step 1). Its theorem
is proved from the existing individual coefficient-cocycle theorem.

`lem-weil-pbc-row-sections-evaluation-square` records the degreewise evaluation
square for arbitrary integer complexes (parent step 2).

Both are source-based statements with explicit Lean signatures, proof plans,
actual search records, and the parent's blueprint ancestry. Zero coefficients,
zero maps, degree zero, negative degrees for the second square, and empty schemes
are covered by the same cocycle and evaluation formulas; no extra nonvanishing
or positivity hypothesis was added.

## Second reading by U2

1. I compared the delivered parent module with the repository version. Existing declaration
   signatures and definitions are unchanged byte for byte; only proof imports, private proof
   helpers, and the parent proof body differ. Verdict: pass.
2. I compiled `EtaleRowExtHomologySquare.lean`,
   `EtaleRowSectionsEvaluationSquare.lean`, and `EtaleRowIntegerSections.lean` with
   `lcompile.py`; all compile cleanly. The only remaining `sorry` is the named public theorem
   `AlgebraicGeometry.Etale.ceComplexSectionsSquare`; there are no axioms, unsafe/opaque
   declarations, or hollow definitions. Verdict: pass, with that split hole recorded.
3. The Ext square is a strict lower-level cocycle-to-homology reduction and is not already in
   Mathlib or the local Sheaf library. The evaluation square is a separate degreewise
   component statement, strictly weaker than the parent and required by its proof. Both nodes
   have source, proof plan, and matching Lean signatures. Edge cases are covered by the stated
   component formulas. Verdict: pass.
4. The parent proof follows the unit route: unevaluated Ext homology square, then evaluation,
   then homology composition and cancellation of comparison isomorphisms. Removed direct
   proof-only imports are now transitively supplied by the two intermediate modules; no old
   proof dependency is otherwise needed. Verdict: pass.
5. DAG `proof`, `proof_deps`, and `proof_origin` agree with the Lean proof, and the unit's
   realized route is unchanged. Verdict: pass.

Changed during second reading: no Lean declarations or DAG statements; added this review
record only. The remaining evaluation theorem is intentionally split off with its documented
source and proof plan.
