# Stage-1 report: lem-pur-rational-braiding-scalar-compatibility

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-integral-braiding-naturality.json` — statement-only lemma; Mathlib search found no exact match.
- `dag/nodes/sec-smooth-purity/lem-pur-rational-braiding-scalar-compatibility.json` — item split into three proof steps; no new Mathlib leaf.
- `citations.json` — verbatim statement excerpts for every cited node in every item step.

No archived attempt directory existed for this item. I copied the live item before editing it and retained its inherited search records. The item has no finished declaration in the read-only Lean source; the only matching text is in DAG records and the stage-2 source module, so this is not an attachment.

## Attachments

None.

## WANTED

None.

## Not duplicates

- `lem-pur-integral-braiding-naturality` vs `lem-sfb-braiding-naturality`: the existing node is the generic Mathlib braiding equation in an arbitrary monoidal category; the new node concerns the completed constructible integral tensor and its coherent-reduction-normalized Koszul braiding.
- `lem-pur-integral-braiding-naturality` vs `lem-coef-localized-tensor-braiding-naturality`: the existing node assumes integral braiding naturality and proves its rational localization; the new node supplies the missing integral naturality calculation.
- `lem-pur-integral-braiding-naturality` vs `lem-pur-finite-pullback-tensor-signed-representatives`: that node is a finite-coefficient pullback/tensor exchange on K-flat representatives, while this node is naturality of the integral coefficient braiding for arbitrary constructible integral arrows and has no pullback morphism.
- `lem-pur-integral-braiding-naturality` vs `lem-pur-rational-braiding-scalar-compatibility`: the new node is the integral prerequisite; the item is the rational naturality and scalar-extension square.
- `lem-pur-integral-braiding-naturality` vs `def-pur-ringed-site-signed-tensor-models`: the existing node defines signed tensor model data; the new node asserts naturality for the completed constructible integral braiding.
- `lem-pur-integral-braiding-naturality` vs `lem-pd-ringed-kflat-native-model-identification`: the existing node identifies a K-flat native model; the new node is a naturality equation for arbitrary constructible integral arrows.
- `lem-pur-integral-braiding-naturality` vs `lem-pd-total-oplax-conjugation-constraints`: the existing node concerns total oplax conjugation constraints; the new node concerns only integral Koszul braiding naturality.
- `lem-pur-integral-braiding-naturality` vs `lem-sfb-constant-module-ordinary-tensor-square`: the existing node is an ordinary constant-module tensor square; the new node is completed integral constructible tensor naturality.
- `lem-pur-integral-braiding-naturality` vs `lem-sfb-constant-module-tensor-square-descent`: the existing node descends a constant-module tensor square; the new node asserts naturality of the normalized integral Koszul swap.
- `lem-pur-integral-braiding-naturality` vs `lem-sfb-exact-derived-monoidal-construction`: the existing node constructs an exact derived monoidal operation; the new node uses the already fixed completed integral operation and proves its braiding naturality.
- `lem-pur-integral-braiding-naturality` vs `lem-sfb-exact-flat-tensor-derived-counit-comparison`: the existing node compares a derived counit with flat tensor; the new node has no counit or adjunction and proves a braiding square.
- `lem-pur-integral-braiding-naturality` vs `lem-sfb-exact-tensor-functor-derived-braiding`: the existing node treats a derived braiding for an exact tensor functor; the new node treats the specific coherent-reduction-normalized completed integral coefficient braiding.
- `lem-pur-integral-braiding-naturality` vs `lem-sfb-exact-tensor-functor-derived-normalization`: the existing node is normalization of an exact tensor functor; the new node is naturality of a fixed integral Koszul braiding.
- `lem-pur-integral-braiding-naturality` vs `lem-sfb-normalized-exact-tensor-square`: the existing node states a normalized exact tensor square; the new node states the integral braiding naturality equation for arbitrary arrows.
- `lem-pur-integral-braiding-naturality` vs `lem-sfb-termwise-strong-monoidal`: the existing node gives termwise strong monoidality; the new node gives naturality of the completed integral signed swap and has no strong-functor structure.


## What was checked and changed

The live item statement was read together with `def-sf-finite-rational-derived-operations`, `def-sf-rational-common-tensor-symmetries`, `def-pod-integral-tensor-constraints`, and `def-weil-rationalization-karoubi`. The statement's hypotheses and both conclusions were retained exactly: arbitrary scheme with invertible $\ell$, raw rational categories, the prescribed localized Koszul braiding, arbitrary localized arrows, every finite coefficient inclusion including ramified ones, and no perfectness or torsion-freeness assumptions. The item's existing Mathlib searches were read and reused; they correctly report only generic braided-category APIs and no project-specific normalized coefficient result.

The only hidden non-elementary fact needed by the item is naturality before rationalization. I created `lem-pur-integral-braiding-naturality` after searching the whole DAG and the latest blueprint. Its statement is strictly smaller than the item and cites the existing owner `def-pod-integral-tensor-constraints`. The search log for the new node contains LeanFinder, Loogle, grep, and LeanSearch records from 2026-10-28; none gives the specified completed coefficient theorem.

Step 1 invokes the new node and records that its reduction calculation is the signed exchange $(-1)^{ij}(b(y)\otimes a(x))$ on homogeneous terms. The source and target are the completed integral tensor objects, and the full-faithful coherent reduction hypothesis is the one built into the owner definition.

Step 2 uses the rational-operation definition and the rational-braiding definition. On pure localized tensors it applies the integral equation from Step 1 coefficientwise; additivity and the raw localization balancing relation extend it to arbitrary localized arrows. The cited statements say respectively that rational tensor maps are scalar-localized integral maps, that $\sigma^E$ is the localization of the integral braiding, and that rationalization has localized Hom modules.

Step 3 checks the scalar square directly on homogeneous pure tensors. The tensor scalar comparison is the localized prescribed integral comparison, so both routes preserve the coefficient generator and differ only by the same Koszul sign $(-1)^{ij}$. Bilinearity and balancing extend the equality to arbitrary objects and arrows. This calculation does not use unramifiedness, flatness, perfectness, or torsion-freeness, so identity and ramified extensions are included.

All citations are recorded in `citations.json` and each quote was checked as a verbatim substring of the cited node's statement. No statement correction or source error was found. No Lean file was written and no compiler or Lake command was run, as required for stage 1.

## Review by NA

I reread the live item and every cited owner node after writing the split. `def-sf-finite-rational-derived-operations` explicitly supplies the rationalized tensor and scalar comparisons; `def-sf-rational-common-tensor-symmetries` explicitly defines $\sigma^E$ as the localized integral braiding; `def-pod-integral-tensor-constraints` explicitly fixes the integral Koszul braiding by coherent reduction; and `def-weil-rationalization-karoubi` explicitly supplies the raw localized Hom modules and balancing relation. Thus Step 2 takes exactly the localization facts those nodes state, and Step 3 takes exactly the scalar-comparison and braiding-normalization facts they state. The new node states only the integral naturality calculation and does not repeat either clause of the item.

I checked the hypotheses at each step: $\ell$ is invertible on residue fields in the item and new node; $E\subset\Omega$ and $E\subset L$ are used only where the corresponding scalar comparisons are defined; arrows are arbitrary in the rational category; and no extra finite-field, perfectness, boundedness, or torsion-free condition entered. I tested the formulas on identity arrows, zero arrows, equal fields $E=L$, a ramified finite extension, homogeneous degrees $(0,0)$ and $(1,1)$, and the zero object; both sides agree in each case. The only correction to the imported item was replacing its empty proof with these three assembled steps and adding the strictly smaller integral-naturality node.
