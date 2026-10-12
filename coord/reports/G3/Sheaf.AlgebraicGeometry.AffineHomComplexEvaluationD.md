## What changed

Closed the tracked hole `AlgebraicGeometry.affine_hom_complex_d_components` by
lifting the supplied underived affine Hom comparison to complexes, applying the natural
single-source Hom comparison, and taking degree components. All existing
signatures and public imports remain identical. The upper theorem
`AlgebraicGeometry.affine_hom_complex_d` retains its original proof.

Added two proof-only imports:
`Sheaf.AlgebraicGeometry.HomComplexSingleNaturality` and
`Sheaf.AlgebraicGeometry.UnderivedAffineHomCounit`. The latter is proved:
the restricted direct-image algebra unit is definitionally the pushed-forward
structure sheaf, so the supplied `iH` is already the required comparison. Its
evaluation identity follows from preservation of 1 and `h_eval`. The former isolates the missing naturality compatibility of the
single-source comparison; it is independent of the affine morphism, adjunction
and choice of evaluation isomorphism.

A proved private categorical helper `adjustComparison` handles the arbitrary
supplied `e`: compare it with canonical evaluation by a natural automorphism of
the identity and precompose with the inverse at the source. Naturality with
respect to the counit cancels the automorphism. The private definition
`unitHomIso` uses actual canonical unit-Hom isomorphisms; no definition chooses
arbitrary data from an unproved existence assertion. Existential witnesses in
the naturality lemma are unpacked only inside the theorem proof.

The component node's proof and proof dependencies now describe this route.
The unit record `sk-thm-picard-duality` has no realized statement or steps that
this reduction bypasses. No existing definition or interface is changed, and
no adaptation of another group's module is included.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.affine_hom_complex_d_components`, node
`lem-sc-affine-hom-complex-evaluation-d-components`.

Also proved the new declaration
`AlgebraicGeometry.underived_affine_hom_counit`, node
`lem-sc-underived-affine-hom-counit`.

The only sorry left in the delivery is the new public theorem
`AlgebraicGeometry.homComplex_single_precomposition_iso`, node
`lem-sc-hom-complex-single-naturality`, whose proof is exactly `:= by sorry`.
There is no sorry left in the item's module or the underived module.

This is a decomposition: one original hole closed, one lower hole added, net
zero holes before any further pruning. It is not claimed as a complete proof
free of sorry dependencies. The upper theorem was already proved and is not
counted as another closed hole.

## No longer needed

No original import, node or module is pruned: the Hom-complex and direct-image
algebra definitions remain necessary in the unchanged signatures. The two new
imports both contribute to the proof. The old immediate proof dependencies
`def-pur-hom-complex` and `def-sc-direct-image-algebra-derived-category` are
replaced by the two comparison nodes; both definition nodes remain necessary
transitively and in the existing signatures, so neither module is pruned.

The abandoned sandbox restatement `AffineHomComplexEvaluationDData` and redundant
public extensionality helper are not part of this delivery. The main proof does
not import `Sheaf.AlgebraicGeometry.HomComplexSingle` or its global additive
instance; instead the required additive instances follow from the comparison
isomorphisms. That existing module is not declared globally unnecessary: it
provides the related pointwise result. The new naturality node constructs its
comparisons directly from the Hom-complex product formulas; it does not apply
the pointwise existence theorem, so that node is not a proof dependency.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox combining proof was unvalidated and contained incorrect
associativity rewrites. These have been repaired, and the arbitrary-e adjustment
is now a proved generic categorical helper. A purely canonical evaluation
argument does not suffice for the unchanged statement with arbitrary `e`.

The underived comparison needs no new abstract isomorphism construction: the
objects are definitionally equal. It is proved directly, rather than left as a
second hole. Its docstring and node now describe the actual argument.

The existing `homComplex_single_iso` gives pointwise existence of complex
isomorphisms. During this session, `HomComplexSingleNatural` landed with the
name `homComplex_single_natural_iso` and naturality in the coefficient complex.
It does not state compatibility with a source morphism. Our distinct theorem
is named `homComplex_single_precomposition_iso`. The new naturality theorem
states precisely that additional step, with no affine or evaluation hypotheses.
Its product-projection proof applies to zero sheaves, unbounded complexes, the
empty scheme and zero section rings; it requires no exactness of infinite
products. Both statements are strictly smaller parts of the original argument.

Searches: LeanFinder returned generic Mathlib single-complex and evaluation
lemmas, not the internal sheaf Hom naturality comparison. Loogle did not find
`NatIso.mapHomologicalComplex` through its Mathlib service. Direct repository
and Mathlib searches found the proved pointwise comparison and canonical
unit-Hom evaluation, which are used above. LeanSearch was attempted for both
new statements and returned an Internal Server Error; it is recorded as
unavailable, with no negative search verdict inferred.

Sources read: Stacks [0BUZ](https://stacks.math.columbia.edu/tag/0BUZ),
[0BV0](https://stacks.math.columbia.edu/tag/0BV0),
[0AX3](https://stacks.math.columbia.edu/tag/0AX3), and the Hom-complex formulas in
[0A8X](https://stacks.math.columbia.edu/tag/0A8X). The project paths named in the
nodes are not materialized on this machine, so these primary-source pages were
read directly. The affine source's ring-map preservation of 1 and the
Hom-complex product and differential formulas support the two parts of the
reduction.

## New nodes

`lem-sc-hom-complex-single-naturality` is stated in
`lean/Sheaf/AlgebraicGeometry/HomComplexSingleNaturality.lean`. It gives natural
single-source comparison isomorphisms for two sheaves and compatibility with a
fixed source morphism. This is the one new work item still carrying sorry.

`lem-sc-underived-affine-hom-counit` is proved in
`lean/Sheaf/AlgebraicGeometry/UnderivedAffineHomCounit.lean`. It identifies the
underived comparison and proves its evaluation equality. It has no complexes
or arbitrary evaluation-isomorphism parameter. No change record is needed:
all pre-existing interfaces are preserved.


## Second reading by G3

1. PASS: Compared the complete item module against the repository with `diff`.
   Independently extracted both existing theorem signatures, including all
   universes, implicit binders, typeclasses, `iH`, `adj₀`, `h_eval`, the arbitrary
   `e`, and both conclusions: they are byte-for-byte identical. The upper proof
   is unchanged. The two helpers are private; no existing definition changes.
   Restored the existing component theorem's original docstring rather than
   changing its documentation as part of a proof edit.

2. PASS: Compiled all three delivered modules with the prescribed local wrapper.
   There were no errors or non-sorry warnings. Inspected all new proof bodies:
   `unitHomIso` is built from canonical `homObjUnitIso`, and `adjustComparison`
   proves the cancellation using naturality of the inverse automorphism at the
   counit, not an extra property of `e`. The two isomorphism witnesses of the
   open lemma are eliminated only in a theorem proof, not used to define data.
   The only direct hole is the whole proof of the public named theorem
   `homComplex_single_precomposition_iso`; it has its docstring and matching
   node. No forbidden declarations or options occur. Explicit scratch-copy
   `#print axioms` checks and the delivery probe verify the axiom closure;
   the main theorem retains `sorryAx` through the reported naturality hole.

3. PASS: Read [Stacks 0A8X](https://stacks.math.columbia.edu/tag/0A8X),
   its product formula and differential `d_I φ - (-1)^n φ d_P`, and the
   underived/derived affine Hom statements in
   [0BUZ](https://stacks.math.columbia.edu/tag/0BUZ),
   [0BV0](https://stacks.math.columbia.edu/tag/0BV0), and the evaluation map in
   [0AX3](https://stacks.math.columbia.edu/tag/0AX3).
   In the new naturality statement, source degree zero leaves just
   `Hom(P,I^n)`; the source differential vanishes. Projection commutes with
   postcomposition in I and with precomposition by the fixed `k:Q → P`,
   giving precisely the displayed equation, with its contravariant direction.
   Checked P=0, Q=0, k=0, k=identity, the empty scheme, zero section rings and
   unbounded I: no inverse of k, nonzero section, or product exactness is used.
   The additive binders supply exactly the structures needed for the degreewise
   functors and hold for internal sheaf Hom. The underived result assumes the
   supplied comparison and sectionwise evaluation equation; preservation of 1
   proves its conclusion without importing finiteness or Noetherian assumptions
   from the derived source. It is already proved, not another hole. Neither
   statement restates the item's existence-and-evaluation assertion.
   Repeated searches using `precomposition`, `single_natural`, and contravariant
   source maps through the prescribed grep, LeanFinder and Loogle tools, and
   searched repository and upstream sheaf modules. Found `homComplex_single_iso`
   and `homComplex_single_natural_iso`; the former is pointwise existence and
   the latter has no source-map compatibility. Neither closes this new hole.
   Formalizing canonical projections and their simultaneous naturality requires
   more than a short application of those results, so no speculative proof or
   additional holes were introduced.

4. PASS: Traced the main proof from its conclusion: the underived equality gives
   `hj`, lifting `iH` gives `d₀`, the fixed-source naturality equation gives `hc`,
   and the proved private adjustment handles arbitrary `e` before taking degree
   components. Both new imports are proof-only. Public imports are required by
   signatures, including `homObjUnitIso` in the underived theorem's conclusion.
   The two old immediate definition dependencies remain required transitively;
   the No longer needed section now names this replacement explicitly. Read
   `dag/units/sk-thm-picard-duality.json`: its realized statement is empty and
   its sole realized step is empty, and this below-unit reduction bypasses no
   realized node. No module is claimed pruned.

5. PASS after correction: Compared the existing node's JSON diff: only `proof`,
   `proof_deps` and `proof_origin` changed. Its three steps match the underived
   equality, single-source precomposition compatibility, and categorical
   adjustment actually used by the Lean proof. Both new nodes have source,
   proof, origin, recorded searches, creation/blueprint/unit/chapter fields and
   Lean records matching their modules and declarations. Removed the pointwise
   `lem-sc-hom-complex-single` from the new naturality node's planned proof uses
   and `proof_deps`: arbitrary pointwise witnesses cannot establish simultaneous
   naturality; its written proof instead constructs canonical product projections
   directly using `def-pur-hom-complex`. The pointwise node remains a statement
   dependency explaining the comparison notion. No statement was altered.

Second reading changed: restored the original existing docstring, corrected the
new naturality node's unused pointwise proof dependency, and clarified the
report's dependency replacement and decomposition accounting. No Lean proof
needed repair. One original hole is reduced to one strictly smaller open hole;
net zero, with no claimed complete proof independent of `sorryAx`.
