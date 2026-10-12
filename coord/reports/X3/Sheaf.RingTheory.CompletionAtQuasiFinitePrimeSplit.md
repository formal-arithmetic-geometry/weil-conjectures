## What changed

`Sheaf.RingTheory.CompletionAtQuasiFinitePrimeSplit` now proves
`Algebra.completion_split_of_finite_subalgebra_away` from finite-factor data,
with its original signature unchanged. It constructs the tensor map from the
levelwise compatibility hypothesis, proves denominator clearing by tensor induction,
identifies its kernel using the finite idempotent, and constructs the complementary
corner ring and the product equivalence. The two private, fully proved helpers are
`Algebra.tensor_clear_away` and `Algebra.split_factor_of_clear_denominators`.

The remaining finite-subalgebra/local-completion argument is stated in the new module
`Sheaf.RingTheory.FiniteCompletionFactorIdempotent`, as
`Algebra.finite_completion_factor_idempotent`. Its conclusion is data in the finite
tensor T: an idempotent e, an inverse on that factor, surjectivity of the finite-factor
map, and its kernel implication. It does not assert a splitting of the larger tensor U.
The main proof performs that transfer and constructs the required equivalence.

Proof imports added to the main module: `Mathlib.RingTheory.TensorProduct.Maps`,
`Mathlib.RingTheory.Idempotents`, `Mathlib.Tactic.Ring`, and the new module.
The direct `Sheaf.RingTheory.CompletionFiniteExtension` import is removed.
The new module imports only `Sheaf.RingTheory.CompletionFiniteExtensionDecomposition`,
which supplies exactly the product and compatibility data needed. The extra completed
tensor equivalence bundled by the full finite-extension theorem is not used.
All existing public imports, universe and scope commands, statements and definitions
are unchanged.
The original node's proof, proof_deps and proof_origin now follow this argument.

Both delivery modules compiled together using `lcompile.py --all`, with no errors or
warnings. The public theorem's proof has no sorry. The new theorem's proof is exactly
`:= by sorry`. There are no adaptations of other existing modules and no change records.

## Proved and sorry left

Closed the original hole in `Algebra.completion_split_of_finite_subalgebra_away`
(node `lem-weil-pbc-completion-finite-subalgebra-away-split`).

Added one hole: `Algebra.finite_completion_factor_idempotent`
(node `lem-weil-pbc-finite-completion-factor-idempotent`). It is the only sorry in
the delivery. This is a decomposition, not a completed proof from standard axioms:
one hole closed and one added, for net zero holes. Existing dependencies of the finite
completion theorem remain whatever they were in the library and are not newly stated here.

The new statement was checked on S'=S with g=1, a singleton finite product (e=1,
complementary corner zero), and a product with other factors. The supported-tuple
construction works in each case. A prime q excludes the zero ring S; the argument
otherwise does not impose nontriviality on completions or complementary factors.
The main denominator proof includes exponent zero and sums with different exponents.
The transfer helper was made polymorphic in separate universes for U and its factor C,
so a factor may live in a smaller universe than the tensor ring.

The corner ring B is a real construction with unit 1-j(e), not arbitrary data chosen
from an existence theorem. The supplied e is uniquely determined by the factor map:
it maps to 1 and kills its kernel; comparing two such idempotents gives ee'=e and
ee'=e', hence equality. Only the inverse of gamma on this corner is used; its
components outside the corner never enter the argument. No definition contains sorry.

## No longer needed

The proof does not need `lem-weil-pbc-localization-tensor-over-base`, the original
step identifying localized tensor products. Denominator clearing directly on tensors
replaces it. Its Mathlib localization/base-change module is not imported.

The proof also does not need injectivity of the tensor inclusion or a ring equivalence
between its two away localizations. Surjectivity of the away map supplies all the
numerators used in the transfer, and the specified finite factor map supplies its kernel.

Removed the main module's direct import of `Sheaf.RingTheory.CompletionFiniteExtension`.
This branch now uses its product-decomposition dependency directly, so
`lem-weil-pbc-completion-finite-extension` / `Sheaf.RingTheory.CompletionFiniteExtension`
and its unused tensor-equivalence step `lem-weil-pbc-completion-finite-extension-tensor` /
`Sheaf.RingTheory.CompletionFiniteExtensionTensor` are not needed by this route.
`lem-weil-pbc-completion-finite-extension-decomposition` and the localization,
completion, finiteness and Noetherian definitions remain needed by the new node. No blueprint-unit statement
or realized step is bypassed. Other branches may still reach the omitted modules; global closure pruning is for the
maintainer to measure.

The remaining old direct proof dependency `def-weil-finitely-generated-module`
is no longer used as a separate step of the main proof. Finiteness remains an
unchanged hypothesis and a statement dependency of the finite-factor node; this
is a dependency moved below the reduction, not a globally pruned definition.
Thus every old direct proof dependency absent from the new `proof_deps` is
accounted for: this definition, the full finite-extension theorem, and the
tensor-localization lemma.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found in the existing statement or its source. The original
plan proves more localization structure than the transfer needs: its tensor-localization
isomorphism and injectivity argument can be replaced by the explicit kernel comparison.

Read Stacks Tag 07NC at https://stacks.math.columbia.edu/tag/07NC, including the finite
product and the compatibility sanity check. The Stacks TeX directory is not populated
in this local clone; the official tag supplied the source text. Read the signatures of
the finite-extension theorem and its decomposition, and the existing quotient-completion
comparison `RingTheory.pair_henselization_completion_data` while investigating the local
comparison. The attempted full extraction encountered expensive elaboration of dependent
completion-factor algebra instances; the delivered finite-factor node leaves that work
explicit, with the source and full mathematical proof in its docstring.

Searches for a shorter route and for the new statement were run through msearch.py.
LeanSearch returned an Internal Server Error and is recorded as unavailable, not as an
absence result. LeanFinder found general idempotent product lemmas and an etale splitting
lemma, but no completion factor statement. The source grep found no exact match.
Blueprint searches for completion/local-completion/idempotent formulations and DAG/Lean
name searches found no duplicate of the new finite-factor statement. The ancestor script
returned None for this module-level item's node; the new node retains the original node's
recorded blueprint ancestor and adds the original node to its via chain.

## New nodes

`lem-weil-pbc-finite-completion-factor-idempotent`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-completion-factor-idempotent.json`,
states the finite tensor's selected-factor data and is implemented by
`Sheaf.RingTheory.FiniteCompletionFactorIdempotent`. Its proof plan follows Tag 07NC:
identify the local completions, apply the existing finite-extension product, compare
completed base maps coordinatewise, and pull back supported tuples. The statement is
strictly a part of the original argument and does not construct the larger tensor's
complementary ring or product equivalence. There are no change records.

## Earlier second reading (a previous round; superseded)

Pending the independent second worker required by the stage-3 process. The delivered
modules and the new node are ready for that reading; the next worker should compile the
original module against the changed dependency and check the unchanged signatures.

## Second reading by X3

1. **Interface: pass.** Read the full diff against the repository module and
   compared the existing theorem signature as raw text, from `theorem` through
   the conclusion before `:= by`: byte-identical. Universes, public imports and
   visibility are unchanged. There is no changed definition, target, or other
   existing declaration. The additional helpers are private proved theorems.
2. **Proof and axioms: pass, conditional on the reported hole.** Compiled both
   modules together with `lcompile.py --all`: 3.4 seconds for the finite-factor
   module and 10.1 seconds for the main module, no errors or warnings. Scratch
   copies with `#print axioms` show only `propext`, `Classical.choice`, `Quot.sound`
   for each private helper, and those axioms plus `sorryAx` for the main theorem
   and `finite_completion_factor_idempotent`. The main module has no sorry; the
   new module has precisely the reported named theorem with `:= by sorry`.
   No forbidden declarations or hollow definitions occur. The complementary
   corner is explicitly constructed. The proof does not define an arbitrary
   object by choosing a witness from an unproved mere-existence theorem.
3. **Split statement: pass.** Read the new signature and its complete proof
   docstring against the finite-extension decomposition signature and the
   official [Stacks Tag 07NC](https://stacks.math.columbia.edu/tag/07NC).
   Contracting q gives a prime over p; denominator clearing identifies the local
   rings and their completions; levelwise compatibility identifies the selected
   projection with phi j. Supported tuples give e, v, surjectivity and the kernel
   implication. For S'=S, g=1 and a single factor, e=v=1; with several factors,
   e is the characteristic tuple and v has the selected inverse coordinate.
   Zero complementary rings and exponent zero cause no exception. A prime q
   excludes S being the zero ring. This statement supplies finite-tensor data;
   it leaves the tensor-map construction, denominator transfer, kernel comparison
   and product equivalence to the fully proved main module, and is strictly part
   of the argument. Independent LeanFinder and Loogle searches used different
   queries (surjective maps to local completions; idempotent surjections).
   Results include `AdicCompletion.ofTensorProduct_surjective_of_finite` and
   localization/idempotent lemmas, but none supplies the selected factor and its
   compatibility. Read Mathlib's quotient-product idempotent theorem: using it
   would still require identifying the specified first component and its kernel.
   Grep of Sheaf and WeilConjectures found no duplicate; the existing
   `finite_over_complete_local_product` concerns a different complete-local-base
   statement. No split hole could be closed by a short application of these facts.
4. **Route and pruning: pass.** Read the tensor induction, the exponent-zero and
   successor cases, the kernel comparison and both directions of the product
   bijection. The direct argument avoids unnecessary tensor-localization
   equivalences. Proof-only imports are plain imports; the new module's public
   imports support its signature (including TensorProduct.map and idempotence).
   The finite decomposition is a plain proof import. Checked every old direct
   proof dependency against the new list and completed the pruning explanation
   above for the finiteness definition. Read `dag/units/sk-thm-p1.json`, including
   all `realized` entries: none of the omitted nodes realizes a unit step, and
   the unit route and its records remain unchanged.
5. **Nodes: pass.** Both node `lean.statement` strings exactly match their Lean
   signatures, and each `proof_deps` equals the union of its proof-step `uses`.
   The main proof and origin describe the actual denominator-and-corner argument.
   The new node has its source, self-contained statement, searches, creation
   record, blueprint ancestry, chapter, unit and Lean record. Its proof plan
   correctly uses the existing finite-decomposition declaration, not the unused
   tensor-equivalence theorem. Existing node interface fields are unchanged.

Second reading changed only this report: recorded the independent checks and
clarified the old finiteness proof dependency. No Lean repair was necessary.
This remains one original hole closed and one strictly smaller hole added,
a decomposition with net zero holes, not a proof from standard axioms alone.
