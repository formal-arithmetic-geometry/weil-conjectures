## What changed

Completed `AlgebraicGeometry.ml_cohomology_powers_ideal_kernel_bound` without changing
its signature. Constructed the short exact cokernel sequence, used the existing
cohomology delta-functor's middle exactness and exact restriction of scalars to
identify the kernel with an image, then transported the degree-zero image estimate
along the inclusion into F. The proof uses the image-only theorem and the proved
transition maps directly. Updated the node's proof, proof dependencies and origin.
Added proof-only imports of the transition and image modules, Mathlib's
ChangeOfRingsExact and Abelian.Exact. All public imports and visibility stay unchanged.

Local launcher compilation succeeds without warnings. The argument uses neither
positivity of n nor a degree p+1 estimate; in particular n=c has exponent zero and
poses no boundary issue. The unchanged theorem includes the required n>=1 condition.
The source proof was read in the launcher's local copy of coherent.tex, lines
5553-5611; that document is absent from this read-only clone's literature directory.
The item is not among its unit's realized statement or proof-step nodes, so the
unit route is preserved.

## Proved and sorry left

Closed: `AlgebraicGeometry.ml_cohomology_powers_ideal_kernel_bound`
(node `ml-cohomology-powers-ideal-kernel-bound`): 1 of 1 original holes.
No sorry remains in the item's module. No new theorem, node, definition, or hole
was added. This is a proof from existing stated dependencies, not a decomposition.
The existing dependency `AlgebraicGeometry.cohomology_powers_ideal_image_bound`
(node `lem-weil-pbc-cohomology-powers-ideal-application-image`) remains unproved
in its own module; this delivery does not alter it.

## No longer needed

Removed direct proof imports:
- `Sheaf.AlgebraicGeometry.CohomologyPowersIdealApplication`
  (node `lem-weil-pbc-cohomology-powers-ideal-application`): only its image portion
  is needed, now used directly through `CohomologyPowersIdealImageBound`.
- `Sheaf.AlgebraicGeometry.SchemeModulesEnoughInjectives`
  (node `lem-weil-pbc-scheme-modules-enough-injectives`): the already packaged
  cohomology delta-functor supplies the exactness used here.
- `Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor`
  (node `lem-weil-pbc-horseshoe-delta-functor`): no horseshoe construction or
  connecting-map naturality is needed in this proof.

Also not needed on this proof route: the kernel portion
`Sheaf.AlgebraicGeometry.CohomologyPowersIdealKernelBound`, node
`lem-weil-pbc-cohomology-powers-ideal-application-kernel`, previously imported
through the application module. No degree p+1 application, common maximum of
thresholds, or separate J^0 F isomorphism is needed. These are local proof-route
prunings; other targets or the image-stabilization sibling may still need them.
Public statement imports are retained. No blueprint unit is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The old plan included the common constant for parts
(1) and (3) of 02OB and a whole ladder of long exact sequences, although this
standalone part (1) only needs middle exactness and one degree-p image bound.
The transition factorization already suffices to transport the estimate into
H^p(F), without proving a separate equality of the degree-zero product with F.

## Second reading by E3

1. **Interface and accidental changes.** I compared the delivered module with the repository version. The theorem declaration and all existing definitions are byte-for-byte unchanged. Only proof-only imports, the theorem proof, and the node's proof metadata differ. No forced adaptation or statement change is present. Verdict: pass.

2. **Proof and axioms.** The module compiles with `lcompile.py` without errors or warnings. It contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`, and no definition contains a placeholder. A scratch `#print axioms` reports only the permitted foundational axioms together with `sorryAx` inherited from the still-open image-bound dependency; the delivered theorem itself introduces no new axiom or hole. Verdict: pass.

3. **Split statements and dependencies.** No theorem or node was split off. The proof uses the existing transition-map and image-bound declarations, the cohomology delta-functor exactness, and Mathlib exactness/image lemmas. The node's `proof`, `proof_deps`, and `proof_origin` agree with those uses, and the removed proof-only dependencies are listed above. Verdict: pass.

4. **Shortest route and pruning.** The kernel is identified directly as the image of the cohomology map from the ideal-power image inclusion, then bounded by transporting the degree-zero image estimate along the transition factorization. This avoids an unnecessary degree-​p+1 estimate, horseshoe construction, and separate identification of the zeroth ideal power. The unit `sk-thm-p1` route is not bypassed because this node is not one of that unit's realized statement or step nodes. Verdict: pass.

5. **Truth and strength.** The unchanged target retains its hypotheses and conclusion. The exactness argument applies to the cokernel quotient, restriction of scalars preserves the relevant exactness, and the final submodule calculation gives exactly `I ^ (n - c) • ⊤` under the original bounds `1 ≤ n` and `c ≤ n`. The image-bound dependency is used at target degree zero and no extra assumption is introduced. Verdict: pass.

Changed during second reading: added this review section only; no Lean code or DAG content required repair.
