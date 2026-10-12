## What changed
Split the localization bijectivity clause into a new theorem producing the same finite polynomial subalgebra data with a surjective localization map. The target theorem is completed by the standard injectivity theorem for localization maps induced by an injective subalgebra inclusion.

## Proved and sorry left
The target `Algebra.FiniteType.exists_finite_subalgebra_away` is proved from the split theorem and `IsLocalization.map_injective_of_injective`. The new theorem `Algebra.FiniteType.exists_finite_subalgebra_away_surjective` remains `sorry`; it contains the generic-fibre normalization, denominator clearing, and finite-integral-generator construction.

## No longer needed
No public imports were removed. The target proof no longer directly needs the former
construction dependencies (localization-at-prime, module-localization, finite-type algebra,
field normalization, MvPolynomial, finite module, integrality, integral closure, and integral
generators); those steps are delegated to the split node. The target node's `proof_deps` was
pruned accordingly to `new-noether-normalization-over-domain-surjective`.

## Where the brief, the DAG or earlier work was wrong
The original node's proof plan is substantially longer than can be completed in one delivery. The localization injectivity portion is elementary and can be discharged directly by Mathlib, so only surjectivity and the construction remain as the split theorem.

## New nodes
`new-noether-normalization-over-domain-surjective` — `Algebra.FiniteType.exists_finite_subalgebra_away_surjective`.

## Second reading by B4

1. **Visible changes and statements.** I compared both delivered modules with the repository
versions. The existing target theorem has the identical signature; its proof only imports the
new split module and combines its surjectivity with Mathlib's localization injectivity lemma.
The added theorem has the stated surjectivity conclusion and does not alter any existing
declaration.

2. **Compilation and axioms.** Both modules compile independently with `lcompile.py --all`.
The only remaining `sorry` is the named split theorem
`Algebra.FiniteType.exists_finite_subalgebra_away_surjective`; there is no `sorry` in a
definition, and no axiom/unsafe/opaque/extern declaration. The completed target is a direct
application of `IsLocalization.map_injective_of_injective` and the split theorem.

3. **New statement.** The split theorem is a strictly weaker, true consequence needed by the
target: it retains all the finite polynomial-subalgebra data and asks only for surjectivity of
the localization map. Its docstring records the generic-fibre normalization, denominator
clearing, integrality, and fraction-lifting proof from Stacks 07NA. The three Mathlib searches
were rerun and found no theorem with this domain-normalization statement.

4. **Pruning and dependencies.** The target node's proof dependencies now contain only the split
node, matching the actual Lean proof; the former construction nodes are no longer used directly
and remain reachable through the split node's documented source route. The proof-only import of
the split module is plain `import`.

5. **Unit route.** The unit's normalization route is retained: the split node is explicitly the
construction portion of the original Noether-normalization node, while the target closes the
canonical inclusion/injectivity step.

The second reading changed the split theorem's proof docstring, synchronized the target node's
`proof_deps` with its proof, and recorded the checks above.
