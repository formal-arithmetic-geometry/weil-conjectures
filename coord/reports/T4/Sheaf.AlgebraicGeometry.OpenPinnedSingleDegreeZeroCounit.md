## What changed

Constructed the target natural isomorphism in
`Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso` from the pinned underived
tensor adjunctions and composition comparisons. No data is chosen from a mere existence
statement. The same module constructs the corresponding homotopy tensor comparison.

The original theorem `AlgebraicGeometry.open_pinned_single_degree_zero_counit_square`
retains its signature and the original definition `openPinnedSingleDegreeZeroCounit`
retains its signature and body. Its proof specializes a homotopy counit restriction
identity to a single complex and combines it with two termwise single restriction
factor identities. The assembly uses counit naturality, functoriality and associativity.

## Proved and sorry left

Decomposition: closed the original hole in
`AlgebraicGeometry.open_pinned_single_degree_zero_counit_square` and added two lower holes:

- `AlgebraicGeometry.open_pinned_counit_homotopy_restriction`, at
  `lem-pc-open-pinned-counit-homotopy-restriction`: the derived counit equation at an
  arbitrary homotopy complex, before any single-complex comparison.
- `AlgebraicGeometry.open_pinned_single_tensor_restriction_factors`, at
  `lem-pc-open-pinned-single-tensor-restriction-factors`: the termwise restriction and
  tensor single identities, which involve no derived tensor counit.

The target-isomorphism construction contains no sorry. All remaining holes are in
named public theorems in separate new modules. This is a decomposition rather than a
sorry-free proof; the net number of holes in the import closure increases by one.

## No longer needed

None of the original planned ingredients is discarded. The original public imports
remain to preserve the existing module interface. The proof additionally needs the
named underived tensor composition comparison. It does not use the abandoned arbitrary
isomorphism compatibility statement or the earlier existential target-isomorphism hole;
neither is present in this delivery or recorded as a new node.

## Where the brief, the DAG or earlier work was wrong

The previous attempt stopped after searching for a direct coherence theorem. Its absence
is not a blocker: the missing derived tensor coherence and termwise single identities
are now stated separately, and the target combines them by a real Lean proof.

An exploratory draft asserted compatibility for an arbitrary target isomorphism. This
is too strong (rescaling an isomorphism can change the counit equation), so it was
removed. The delivered coherence statement uses only the explicitly constructed
underived and homotopy comparisons. Empty opens and zero modules are covered by the
same functor and localization constructions; no flatness hypothesis on M is introduced.

## New nodes

`def-pc-open-pinned-single-tensor-restriction-iso` records the four explicit comparison
constructions in `OpenPinnedSingleDegreeZeroCounitIso`. They use the existing pinned
tensor composition comparison and the canonical open pullback/restriction comparison.

`lem-pc-open-pinned-counit-homotopy-restriction` records the remaining derived counit
coherence step on arbitrary homotopy complexes. It imports the existing source
comparison data and uses the constructed homotopy tensor comparison.

`lem-pc-open-pinned-single-tensor-restriction-factors` records the remaining termwise
single restriction identities. These contain no left-derived counit and specialize
ordinary functor and complex comparisons.

The original node's proof, proof_deps and proof_origin are updated to match the Lean
assembly. No existing definition or statement changed; no change record is needed.

## Second reading by T4

1. I compared the delivered target module with the repository version. The target definition and theorem signatures are unchanged byte for byte; only proof imports and proof terms changed. Verdict: pass.

2. I compiled all sandbox modules with `lcompile.py --all`; the modules compile without errors. The remaining `sorry`s occur only in the two named public split-off theorems, each with a DAG node and proof docstring. No definitions contain `sorry`, and no forbidden declarations were added. Verdict: pass.

3. The split-off statements are strictly lower-level reductions: one is the arbitrary homotopy-complex counit restriction equation and the other consists of the two termwise single-complex factor identities. They are not restatements of the target, and the construction uses no arbitrary existential witness. Verdict: pass.

4. The target proof follows the planned route through the constructed underived, single-complex, and homotopy tensor comparisons, then assembles the square by categorical reassociation. Imports are limited to the target's public dependencies plus the two proof-only split-off modules. No planned dependency was removed. Verdict: pass.

5. The target node and the three new nodes agree with the declarations, proof dependencies, and proof origins in the sandbox. The unit route remains realized through the target and comparison construction. Verdict: pass.

I changed nothing during second reading; the delivered proof and decomposition are accepted as written.
