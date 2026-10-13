## What changed

Replaced the sorry in `AlgebraicGeometry.exists_ordinaryEvaluation_over_transport`
without changing its signature. The private helper `hom_quasiIso_over_transport`
uses the exact inverse, Hom naturality, two arrow isomorphisms and the complex
counit to transfer preservation of quasi-isomorphisms. The private helper
`kFlat_over_transport` pulls back an acyclic test complex and uses the actual total
tensor comparison, the counit and the dual isomorphism to transfer K-flatness.
`kInjective_over_transport` uses the already proved source-library instance for
additive equivalences. Ordinary algebra comparisons are isolated in two new
modules, `OrdinaryEvaluationOverComparisons` and `TotalTensorOverEquivIso`.

The second reader closed the total-tensor comparison using the already proved
`exists_localizedOpen_tensor_equivalence` and the existing bicomplex/totalization
isomorphisms. Its unused public KFlat import was removed. The remaining comparison
module now privately imports both proof dependencies its docstring uses.

The proof uses a local heartbeat allowance for elaborating the chosen Hom
functors and both site carriers; the single-file compile stays below 60 seconds.
No definition, existing signature or visibility changed. No other module is adapted.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.exists_ordinaryEvaluation_over_transport`
(node `lem-pc-ordinary-evaluation-over-transport`). Its proof is complete from the
new comparison statements. This is a decomposition, not an unconditional proof.
The private Hom quasi-isomorphism, K-flat and K-injective transport helpers are
completely proved.

The second reading also closed the initially split-off hole
`AlgebraicGeometry.exists_totalTensor_overEquiv_iso`, node
`lem-pc-total-tensor-over-equiv-iso`. Its axiom check contains only the three
standard axioms. It is a proved new lemma, not an added hole.

Added one remaining hole:

- `AlgebraicGeometry.exists_ordinaryEvaluation_over_comparisons`, node
  `lem-pc-ordinary-evaluation-over-comparisons`, in
  `Sheaf.AlgebraicGeometry.OrdinaryEvaluationOverComparisons`.

The remaining statement omits all three homological assumptions and conclusions
of the original theorem. It supplies only compatible ordinary algebra maps and
Hom naturality. The main module independently proves the homological consequences.
The delivery closes one original hole and adds one hole, hence is a decomposition
with net zero holes closed, not an unconditional proof of the original theorem.
The remaining hole is a whole public theorem proof with its source, complete proof
in words and matching node. No sorry is left in the item's module or in the new
total-tensor module. No hole is placed inside a definition.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.InternalHomOverEquiv`
from the item. Its node `lem-sc-internal-hom-over-equiv` is still needed by the
ordinary comparison construction, so it is not globally pruned.

The item's direct proof dependencies on `def-pc-kflat-complex`,
`def-pc-ordinary-evaluation-data`, `def-pc-scheme-ordinary-evaluation-formula`,
`def-pc-tensor-complex-sheaves`, `def-pur-kinjective-complex`,
`lem-sc-hom-complex-projections`, `lem-sc-internal-hom-over-equiv`, and
`lem-weil-pbc-module-restriction-open-immersion-colimits` are replaced by the two
comparison nodes. The definitions remain statement dependencies; the ordinary
comparison construction still needs the Hom projection and internal-Hom nodes.
The restriction-adjunction theorem in
`lem-weil-pbc-module-restriction-open-immersion-colimits` is not needed by either
new comparison proof: `overEquiv` preserves coproducts as an equivalence. Removed
that proof edge from the new total-tensor node and its misplaced statement edges
from both new nodes. The original item's legacy statement edge is retained,
since its statement and statement metadata are unchanged.
Removed the new total-tensor module's unused public import
`Sheaf.Algebra.Homology.KFlat`; its signature elaborates using the tensor
preadditivity supplied by its existing statement imports. No complete module is
claimed to leave the targets' import closure.

## Where the brief, the DAG or earlier work was wrong

The old proof plan omitted the Lean interfaces needed to lift termwise internal
Hom and tensor reindexing to compatible complex isomorphisms. Its termwise
internal-Hom dependency alone does not state these conclusions; the new nodes
make the missing ordinary algebra explicit. The homological consequences can be
proved independently from naturality, exactness and the counit, as this delivery
does. The old restriction-colimits node refers to `Modules.restrictFunctor` and its
adjunction, whereas this item uses `Modules.overEquiv`. General equivalence
instances suffice for the latter's colimits and exactness. The unit's route is unchanged; its realized arrays are empty and no unit
statement or step is bypassed.

Initially the local published build lacked `SchemeOrdinaryEvaluationFormula`.
It became available during the session; no dependency was copied or modified.
The official Stacks pages 08DL, 08DJ, 08DQ and 06YN were read. They supply the
ordinary Hom/tensor constructions and K-flat criterion, not a preexisting Lean
open-site comparison. LeanSearch returned an unavailable service; LeanFinder,
Loogle and local/blueprint searches initially supplied no exact comparison.
The second reader then found and used the existing termwise tensor theorem.
Zero complexes, the empty open, unbounded complexes and zero rings do not impose
extra hypotheses on either new statement: equivalence preserves all required
products/coproducts and their universal properties.

## New nodes

`lem-pc-total-tensor-over-equiv-iso` is the ordinary total tensor comparison
for arbitrary pairs of complexes; it is needed to transport the K-flat test
against every acyclic scheme complex, rather than only the given F.

`lem-pc-ordinary-evaluation-over-comparisons` is the compatible algebraic part
of the old plan, including naturality in every target complex and the comparison
of the ordinary dual. The main module proves all homological consequences from
these comparisons. The total comparison is now proved from
`lem-sc-localized-open-tensor-equivalence`; it does not repeat that termwise
statement. Both nodes inherit the parent's chapter and unit and preserve
the blueprint route. No change record is needed because existing interfaces stay
identical and the added imports are proof-only.

## Second reading by U4

1. Compared every delivered Lean module with the repository (the two comparison
modules are new). The existing theorem header, all hypotheses including the
K-injective instance, let-bindings, existential isomorphisms and all four conclusion
clauses are byte for byte unchanged. The existing module's two public imports
stay unchanged; new proof imports are private. No definition or other existing
module is changed, and no change record is needed. Verdict: unchanged interface.

2. Read the main proof and all three private transport helpers. Hom transport pulls
a through the exact inverse, applies hhom, then uses b's naturality and the counit
square to obtain the target arrow. K-flat transport tests an arbitrary acyclic A,
uses its inverse image, then the total comparison, tensor of the counit and tensor
of d in the correct orientations. The proved upstream additive-equivalence
K-injective instance supplies the last homological clause. The final map is exactly
t.inv;T(f);b.hom. Only the compatible ordinary comparison remains sorry; there is
no axiom, unsafe, opaque, external implementation or data definition with a hole.
The chosen MonoidalPreadditive instances are proof-valued, not arbitrary objects
chosen from an unproved existence theorem. All three delivered files compile
locally. Scratch-copy #print axioms checks show only propext, Classical.choice
and Quot.sound for the total theorem and all three private transport helpers;
the original theorem and the remaining comparison additionally use sorryAx,
as expected from the reported remaining hole. Verdict: genuine reduction.

3. Read the new statements against the component definitions and Stacks Tags
[08DL](https://stacks.math.columbia.edu/tag/08DL),
[08DJ](https://stacks.math.columbia.edu/tag/08DJ),
[08DQ](https://stacks.math.columbia.edu/tag/08DQ) and
[06YN](https://stacks.math.columbia.edu/tag/06YN). These tags give the ordinary
constructions used in the proof, rather than an exact Lean open-site comparison.
The two new statements assume arbitrary complexes, with no boundedness, perfectness
or homological hypotheses. For zero complexes, zero rings and the empty open,
reindexing preserves the same universal properties. In unbounded degrees it
preserves the full Hom product and tensor coproduct; no finite-total argument is
used. The remaining comparison is strictly the algebraic part: it asserts no
quasi-isomorphism preservation, K-flatness or K-injectivity. Its naturality is needed
by the main Hom helper and its dual comparison by the K-flat helper. The total
comparison must allow arbitrary test complexes, not only the given F. Independent
LeanFinder, Loogle and grep queries were run with totalization/strong-monoidal
terminology, followed by source and DAG searches. Found the proved
`exists_localizedOpen_tensor_equivalence`, and used its naturality to close the
total-tensor hole by lifting twice with isoOfComponents and then totalizing.
`openRestriction_totalTensor_iso` concerns overFunctor followed by overEquiv,
so does not itself state the new theorem. Verdict: true, needed smaller statements;
one initially split-off hole additionally closed.

4. Checked the old proof_deps against the report's complete removal list. The
termwise internal-Hom node remains in the remaining comparison's plan and is now
privately imported there. The proved total comparison replaces its unfinished
sectionwise tensor construction with the existing localized-open tensor theorem.
Its unused public KFlat import was removed. Read
`dag/units/sk-thm-picard-duality.json`: realized.statement is empty and the single
realized step is empty; no realized unit statement or step is removed. The same
finite-duality ancestry and ordinary evaluation route remain. No whole module is
claimed globally pruned. Verdict: route preserved; unnecessary import removed.

5. Compared the parent node to its baseline: only proof, proof_deps and proof_origin
change. Checked both new nodes' Lean signatures against the files, hypotheses and
clauses against their prose statements, dependency unions against their proof
steps, and chapter/unit/source/created/blueprint/search metadata. The parent uses
both comparison declarations; the total node now cites the proved localized-open
tensor theorem. Verdict: nodes reflect the actual reduction and completed tensor
proof.

Second-reading changes: closed exists_totalTensor_overEquiv_iso; removed its unused
public KFlat import; added private proof-dependency imports to the remaining
comparison; corrected its docstring's nonzero-degree case (the evaluation component,
not the entire source summand, is zero); updated total node and hole accounting.
