## What changed

Replaced the sole sorry in `Sheaf.RepresentationTheory.LocallyConstantCochainsDegreewiseExact`
with a complete proof of `Rep.locallyConstantCochains_degreewise_exact`, preserving its
signature and visibility. Added proof-only imports of
`Sheaf.RepresentationTheory.OpenStabilizerAdjunction`,
`Mathlib.Algebra.Homology.ShortComplex.Ab` and
`Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`.
Updated the declaration docstring and its node's proof route.

The coefficient forgetful functor preserves finite colimits and monomorphisms, using the
existing `ModuleCat.openStabilizerAdjunction`. Mathlib's exact-functor criterion then gives
short exactness of the underlying coefficient sequence. The rest is proved here: injectivity
pointwise, kernel lifting by a set function extended by zero outside the kernel, and
surjectivity by a set-theoretic section. `LocallyConstant.map` preserves local constancy of
both lifts. No new construction takes data from an unproved existence theorem outside a proof.

## Proved and sorry left

Closed 1 original hole: `Rep.locallyConstantCochains_degreewise_exact`
(node `lem-sc-locally-constant-cochains-degreewise-exact`).
No sorry remains in the delivered module. Added 0 holes and split off 0 new statements.
This is a proof from an existing named dependency, not a decomposition into new holes.
The existing dependency `ModuleCat.openStabilizerAdjunction`
(node `lem-exc-rg-open-stabilizer-adjoint`) remains unproved in the shared library, so the
result's transitive axiom closure still contains `sorryAx` through that theorem.

## No longer needed

No original import or module is pruned. The old proof dependency
`def-exc-discrete-modules-category` is removed from `proof_deps` and retained in
`stmt_deps`: `DiscreteContinuousRep` remains needed by the statement. The proof now
uses `lem-exc-rg-open-stabilizer-adjoint`. Removed the temporary redundant proof imports
`Mathlib.CategoryTheory.Adjunction.Limits` and `Mathlib.CategoryTheory.Abelian.Exact`;
both are available through `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`.
No new module or node is introduced. No separate abelian-structure theorem for discrete
integer representations is needed: coefficient exactness is established directly for the
functor out of the given abelian category A.

## Where the brief, the DAG or earlier work was wrong

The plan's coefficient exactness argument had no matching Lean dependency beyond the
category definition. The existing discreteRep_abelian_structure theorem is restricted to
finite rings and profinite groups, so it does not apply to the integer coefficients and
arbitrary topological group here. The existing open-stabilizer adjunction gives the missing
route via Mathlib without any new statements or interface changes.

Searches were run with msearch.py: leanfinder for locally constant exactness, loogle for
LocallyConstant.map, and grep for locally constant exactness. None states the whole result.
The source library and representation modules were also searched with rg. Read Stacks
Tags 0DVG and 04JF directly online, because the local TeX files are absent on this machine.
The source's exactness assertion and adjunction agree with the proof used here.

The unit sk-thm-br has no realization attachment for this auxiliary node. Its statement
and route are unchanged. The new dependency is a generic categorical tool, not a bypass
of a unit step. Boundary cases (degree zero, zero coefficient groups, and a nondiscrete
or noncompact G) use the same pointwise proof and require no extra hypothesis.

The module compiles cleanly with lcompile.py. The delivery dry run performs the final
signature, axiom and preflight checks; no publication is requested.

## Second reading by M2

1. The delivered theorem signature is byte-for-byte unchanged from `sheaf-dag`; the diff contains only proof imports, the docstring proof explanation, and the proof body. No target or definition changes were found.

2. The sandbox module compiles cleanly with `lcompile.py`, with no remaining `sorry` in the delivered declaration and no forbidden declarations. The proof relies on the existing open-stabilizer adjunction, whose transitive theorem remains a documented open dependency and is not introduced here.

3. No statements were split off and no new nodes were added. The existing theorem is mathematically the required degreewise exactness statement; the pointwise kernel and surjectivity arguments are implemented directly. The node's updated proof and proof dependencies match the imports and proof.

4. The proof uses the adjunction plus Mathlib preservation and exactness APIs, then explicitly constructs pointwise lifts. The proof-only imports are plain imports. No unused original public import was removed, and the report's temporary-import pruning is consistent with the delivered file.

5. The node diff changes only `proof`, `proof_deps`, and `proof_origin`, with the
proof dependencies exactly the union of the proof steps' `uses`. The unit route is unchanged: this auxiliary node has no realization attachment in `sk-thm-br`; the proof does not alter the unit statement or steps. I found no Lean repair necessary. I corrected the pruning report to distinguish
the removed old proof dependency from the retained statement dependency.

The explicit scratch-copy `#print axioms Rep.locallyConstantCochains_degreewise_exact`
check returned only `propext`, `Classical.choice`, `Quot.sound`, and the documented
`sorryAx` from the open adjunction. Searches of Mathlib LocallyConstant APIs and
the representation modules found no shorter existing theorem for this statement.
The choice of a right adjoint stays inside a proposition proof; no definition
chooses arbitrary data from a holed existence theorem. The same valuewise lifts
work for degree zero, zero coefficient groups, and noncompact or nondiscrete G.
