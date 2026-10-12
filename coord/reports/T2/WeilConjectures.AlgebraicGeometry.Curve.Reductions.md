## What changed

Completed the proof body of
`AlgebraicGeometry.exists_mono_lowerShriek_constantModSheaf_lowerStar` without changing its
signature. The proof constructs the morphism from the adjunction unit for the surjective
base change ν′, the constant-sheaf pullback isomorphism, and the finite/open comparison.
It proves that this morphism is mono using the existing unit-mono theorem, exactness of
extension by zero, and cancellation of isomorphisms. The cokernel properties are separated
into `Sheaf.AlgebraicGeometry.Curve.NormalizationMonoProperties`.

Added proof-only imports of that module and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective`; removed the direct proof import
of `WeilConjectures.SixFunctors.Finite.Exact`. Updated the normalization exact-sequence
node's proof and dependencies to describe the actual construction and remaining lemma.
No declaration signature, definition, or public import of the item changed.

The full sandbox compiles through lcompile.py. The construction is real Lean, rather than
an application of a restatement: only constructibility and dense-open vanishing of its
cokernel are deferred. The new lemma's docstring supplies the full argument and source.

## Proved and sorry left

Reduced 1 of the 2 original sorries:
`AlgebraicGeometry.exists_mono_lowerShriek_constantModSheaf_lowerStar`
(node `lemma-weil-pbc-normalization-exact-sequence`) now has a complete proof body.
It still depends on the new named cokernel theorem and any existing unfinished imports;
this is a stage-3 reduction, not a claim that its transitive axioms are sorry-free.

Original sorry left unchanged:
`AlgebraicGeometry.IsCurve.Assertions.lowerShriek_constantModSheaf_of_finite`
(node `lemma-weil-pbc-curve-normalization-constant`). The existing finite-pushforward
assertion API uses a `CurveCoefficientPair` of abelian sheaves with ULift ℤ coefficients,
whereas this theorem uses arbitrary Λ-module coefficients. Further work must bridge that
API and combine the finite-supported cokernel calculation with the low-degree long exact
sequence; the middle-term dévissage theorem alone does not prove the needed first term.

New sorry left:
`AlgebraicGeometry.normalization_mono_properties`
(node `lem-weil-pbc-normalization-mono-cokernel`, module
`Sheaf.AlgebraicGeometry.Curve.NormalizationMonoProperties`). This is a strictly smaller
part: it takes an actual mono α and proves its cokernel constructible and zero on V.
It has no existential morphism construction in its conclusion.

Edge cases checked mathematically: empty U gives two zero comparison terms; ν an
isomorphism or V=X gives finite equal-size stalks everywhere, so a mono is iso; the
zero coefficient quotient also gives zero terms. The arbitrary-mono generalization
uses the stated finiteness of Λ/ℓΛ: injectivity between equal finite stalks implies
surjectivity. Constructible cokernels require no Noetherianity assumption on Λ.

## No longer needed

Removed direct proof import `WeilConjectures.SixFunctors.Finite.Exact`; the completed
construction needs finite/open comparison and unit monicity, not derived finite
pushforward exactness. The normalization exact-sequence node no longer directly cites
`lemma-weil-pbc-finite-direct-image-exact`, `thm-sc-main`, or
`lemma-weil-pbc-eight-curve-devissage`. These nodes may still be needed elsewhere or
transitively; this is pruning of this node's argument only. Its old direct definition
edge `def-weil-pbc-extension-by-zero` is replaced by the exactness theorem used to map
the mono; that definition remains a statement dependency of the new cokernel node.

Removed the earlier uncommitted `NormalizationMonoExists.lean` and its
`new-normalization-mono-exists` node: the library's surjective-unit monicity and
finite/open comparison provide the construction directly. The old uncommitted
`new-normalization-mono-properties` node is replaced by the fully documented, validly
named `lem-weil-pbc-normalization-mono-cokernel` node. No committed node was deleted.
No other original import was removed; the other completed proofs still use their APIs.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's new node records had empty Lean signatures, no statement
reference dependencies, and no Mathlib searches. Their docstrings lacked complete
natural-language proofs and an explicit source. These are repaired. Its report did
not list the unchanged second normalization sorry; it is listed above.

The previous split deferred construction of the mono even though the source library
already proves `Etale.mono_unit_app_of_surjective`. That new statement is unnecessary.
The arbitrary-mono cokernel claim is true under the finite quotient hypothesis, but
its earlier diagonal-only proof sketch did not justify the arbitrary α binder. The
new docstring uses equal finite cardinalities and handles that binder explicitly.

The normalization exact-sequence prose includes field-extension and boundary-map
compatibilities absent from its existing Lean signature (already acknowledged by the
original docstring). This delivery preserves the signature and does not claim to add
those clauses. The unit's normalization route is preserved; no smooth calculation
or unit realization is bypassed. LeanSearch returned HTTP 500, recorded honestly as
unavailable; LeanFinder and local Mathlib grep were run successfully.

## New nodes

`lem-weil-pbc-normalization-mono-cokernel`, in
`dag/nodes/sec-proper-base-change/lem-weil-pbc-normalization-mono-cokernel.json`, records
exactly the new public theorem's signature, its source, self-contained hypotheses,
complete two-step proof, and actual search results. It separates the constructible
cokernel/support step from the now-formalized morphism construction. There are no
interface-change records because existing signatures, definitions and exports are
unchanged.

## Second reading by T2

1. Compared the delivered Reductions module with the repository using `diff -u`.
   The only differences are its normalization existential proof body and three
   proof-import changes. All existing declaration signatures, definitions, docstrings,
   and public imports are byte-for-byte unchanged. No interface change record is needed.
2. Both delivered modules compile with `lcompile.py --all`, without errors or warnings.
   Scratch copies with `#print axioms` for every declaration (including private helpers)
   compile: the only axioms are propext, Classical.choice, Quot.sound, and sorryAx from
   the explicitly open theorems/imports. The only local sorries are the unchanged
   normalization transfer theorem and normalization_mono_properties, both listed above.
   No forbidden axiom/unsafe/opaque/extern/implemented_by declaration or hollow definition
   occurs. The new mono proof constructs its map and verifies monicity; it does not
   merely apply a renamed existential statement.
3. Read the split theorem, its docstring, its node, and the upstream cokernel,
   extension-by-zero, and finite-pushforward APIs. The statement is true: empty U,
   empty X, zero R, ν an isomorphism, and V=X cause no failure. On U∩V a mono has
   equal finite source/target stalks, hence is surjective; outside U both vanish.
   Independent LeanFinder and local grep searches, and Loogle's
   `Finite _, Function.Injective _`, found no theorem stating the whole split.
   Loogle provides Finite.injective_iff_surjective_of_equiv for the elementary step;
   the proved upstream IsConstructibleSheaf.cokernel supplies the final constructibility
   closure step. Finite-pushforward constructibility is currently exposed for abelian
   sheaves in the finite-set sense, so closing the whole module-coefficient split needs
   comparison/structure transport rather than a short direct application.
4. Reviewed the adjunction-unit construction from the top down against the existing
   surjective-unit, constant-pullback, exact extension-by-zero, and finite/open
   comparison declarations. They give the construction directly; no shorter missing
   existential lemma is needed. The import changes are proof-only, and the three public
   imports of the new module provide its signature's curve, constant-coefficient,
   inverse-image and extension-by-zero notions. The No longer needed section lists
   every removed old direct proof dependency. Read sk-thm-p1.json, including realized:
   the normalization reduction remains within its curve-calculation step, and no unit
   statement or realized route is bypassed or changed.
5. Compared the old/new node dependencies with the actual proof. The existing node's
   two-step proof records the mono construction and the narrower cokernel split.
   The new node has its verbatim signature, source, statement dependencies, full
   proof plan, search records, creation/blueprint fields, and matching module/theorem.
   Corrected stale Lean metadata and completed its written proof-plan dependencies.

Second-reading changes: no Lean proof or existing signature was changed. Updated the
existing node's lean record to record its completed local proof and remaining transitive
sorryAx. Added finite exchange, exact inverse image, and constant-sheaf pullback to the
new node's proof dependencies, with citations in its proof step. Recorded independent
searches. Clarified the new theorem's docstring and node proof that its Λ-module operations
factor through the finite quotient ring R; this supplies the justification for transporting
finite-set constructibility to module constructibility when Λ itself is infinite.
