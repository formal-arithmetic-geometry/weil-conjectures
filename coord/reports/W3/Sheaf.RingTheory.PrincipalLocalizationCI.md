## What changed

Proved `Algebra.principalLocalization_ci` in
`Sheaf.RingTheory.PrincipalLocalizationCI` without changing its signature or public imports.
Added proof-only imports of `Sheaf.RingTheory.PrincipalLocalizationAlgEquiv`,
`Sheaf.AlgebraicGeometry.GlobalCompleteIntersectionEquidimensional`, and Mathlib's
`RingTheory.TensorProduct.MvPolynomial`, `RingTheory.TensorProduct.Quotient`, and
`RingTheory.Localization.BaseChange`.
The private, fully proved helper `fibrePresentationEquiv` constructs scalar extension
of a polynomial quotient. The private, fully proved helper `principalOpen_dim` proves
dimension preservation by direct upper and lower bounds on the nonempty open range.
Updated `new-principal-localization-ci` to record this route and its dependencies.

## Proved and sorry left

Closed: `Algebra.principalLocalization_ci` (node `new-principal-localization-ci`),
the sole original hole. Both private helpers are completely proved.
Holes closed: 1. Holes added: 0. Sorries left in delivered modules: none.
The proof uses the existing named statement `Algebra.principalLocalization_algEquiv`
(node `new-principal-localization-alg-equiv`), whose proof remains an existing `sorry`
in its own module; this delivery neither moves nor adds that hole.
The equidimensionality theorem is already proved.
The item compiles without warnings. The dry-run delivery checks the declaration probe.

## No longer needed

No original imports were removed. The following steps of the ancestor's six-step plan
are unnecessary for this item's dimension argument:
`lem-weil-pbc-dimension-at-point-open-subspace`
(`WeilConjectures.Mathlib.Topology.KrullDimension`, declaration
`IsOpen.topologicalKrullDimAt_eq`) and
`lem-weil-pbc-dimension-supremum-local-dimensions`
(`Sheaf.Topology.DimensionSupremumLocalDimensions`).
Their modules are not added as proof dependencies for these results. The upstream
KrullDimension module is still transitively available and used for the local-dimension
definition and embedding dimension comparison. Pruning is specific to the named
results; this report does not claim the whole upstream module is unnecessary.
The direct argument bounds dimension below by the local dimension at a point in the
open range and above by the whole space's dimension.

## Where the brief, the DAG or earlier work was wrong

The item's DAG contained only a placeholder proof and no proof dependencies. The
ancestor's explicit six-step plan supplies the needed algebra and equidimensionality
results. Its final dimension step can be shortened as recorded above.
No statement, definition, or unit route required correction.
The zero-ring case is handled by restricting to nontrivial enlarged fibres; an algebra
map to their nontrivial localization forces the original fibre to be nontrivial.
Thus vacuous fibres, including localization at zero and presentations with c > n,
do not cause an extra hypothesis.

## Second reading by W3

1. PASS: compared the delivered module with the repository using `diff` and compared
   the original theorem header byte for byte. `Algebra.principalLocalization_ci`,
   its existing docstring, universe, namespace and three public imports are unchanged.
   There is no interface change or change record. The two new helpers are private.
2. PASS: independently compiled the module without errors or warnings. A scratch copy
   with `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound` for
   both private helpers; the main theorem additionally uses `sorryAx` from existing
   dependencies, notably `Algebra.principalLocalization_algEquiv`. There is no direct
   `sorry` or prohibited declaration in the delivered module. The helper definition
   constructs its equivalence from proved Mathlib equivalences; it chooses no data
   from an unproved existence theorem. The existing existential algebra equivalence
   is eliminated inside a theorem proof, not used to define an arbitrary object.
3. PASS: no statement was split off and no new hole or node was added. Read both
   helpers and the imported statements. The dimension helper's nontrivial domain
   supplies a point of its open range; its lower bound follows from the defining
   infimum, and its upper bound is subspace monotonicity. Checked the empty-fibre,
   zero-ring, localization-at-zero, `n = c`, and `c > n` cases: the proof applies
   `hrel` only after proving the original fibre nontrivial, so it never assumes
   a dimension or equation-count condition on empty fibres.
4. PASS: searched again with Loogle, LeanFinder and `rg`, using open-embedding and
   constant-local-dimension wording, and read the upstream local-dimension results.
   No shorter existing theorem replaces the argument; Mathlib supplies exactly the
   scalar-extension, quotient, base-change and dimension comparison operations used.
   Each added import supplies a proof dependency and is correctly a plain `import`.
   The old node had empty `proof_deps`, so no old dependency is missing from the
   pruning report. The two unused ancestor-plan results are correctly identified;
   no original module import is removed or claimed pruned. Read `sk-thm-p1` and its
   `realized` record: this shortening is below the unit's steps and preserves them.
5. PASS: read the node and every recorded proof dependency's Lean or Mathlib record.
   The node changes only `proof`, `proof_deps` and `proof_origin`; their steps follow
   the actual equivalences, nontriviality argument, equidimensionality and two
   dimension bounds in Lean. The dependency list equals the union of the steps'
   `uses`. The statement, statement dependencies and Lean signature stay unchanged.

Second reading changed only this report to record the independent checks. No repair
of the Lean module or node was necessary. Confirmed one local hole closed, zero
holes added; this remains a proof from an existing open dependency, not a claim
that the theorem's entire import closure is axiom-free.
