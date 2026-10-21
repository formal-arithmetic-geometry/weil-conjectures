# Worker report: def-nagata-strict-transform-chart-ring

## Files written

- `dag/nodes/sec-nagata-compactification/def-nagata-strict-transform-chart-ring.json`: existing definition, now split; no exact Mathlib match for the whole chart construction.
- `citations.json`: empty list, because a definition has no proof steps. Its four dependencies are statement dependencies, audited below.
- `report.md`: this report. `searches.jsonl` is the unmodified output log of msearch.py.

New nodes: 0. New Mathlib leaves: 0. No unit record is changed: this definition is not the key statement of its unit. No Lean was written and no compiler or build was run.

## Attachments

None submitted, as the repair brief explicitly forbids answering ATTACH again. The previous absence finding is no longer true of the supplied live tree: `lean/WeilConjectures/Blowup/Affine/StrictTransformChart.lean` now exists and lines 48–65 contain the binders and `AlgebraicGeometry.AffineBlowup.BaseChangeChart`, `baseChangeChartTorsion`, and `StrictChart`; the last abbreviation is precisely the displayed quotient. I read those bodies and the supporting `Submodule.powTorsion` and `mem_powTorsion_iff` in `WeilConjectures/Mathlib/Algebra/Module/Torsion.lean:58–74`. This observation is evidence about the current source, not a renewed attachment request or a claim that a closure checker ran. I delivered the requested stage-1 dependency split.

## WANTED

None. The item and all notions used are present in the supplied blueprint, DAG and source trees.

## Statement corrected

STATEMENT-DISPUTED (standalone typing/context only): the imported statement starts with “Define” and a formula containing unbound A, B, I and a. Taken as a standalone definition, it supplies neither the ring-map data needed for the tensor product nor the element of the tensor product whose power torsion is taken. Its intended formula is correct. I restored the context explicitly from the adjacent source definition `def-nagata-strict-transform-basechange-chart-ring`: a homomorphism of commutative rings A to B, an ideal I of A and a in I. Commutativity is the ring convention required by A[I/a], the tensor-product algebra and the quotient ring. I named the structural image alpha in C, exactly as that adjacent source prescribes. The quotient is unchanged. No finiteness, flatness, injectivity, domain, nonzero-element or nonzero-ring assumption was added. Thus every existing use of the formula keeps its meaning.

The original two statement dependencies did not explicitly provide the fact making the denominator an ideal or the quotient-ring construction. I added the already existing `lemma-nagata-power-torsion-submodule` and `def-weil-pbc-algebra-hom-quotient`. The definition keeps empty proof/proof_deps and null proof_origin. Its data is the actual quotient, not data chosen from an existence theorem. I retained the import flags, blueprint update, notes, and other maintainer-owned fields.

## Searches and reuse

I searched the project Lean tree for the item tag, StrictChart, BaseChangeChart and power torsion, and searched the DAG and whole imported blueprint for strict-transform chart rings, strict transforms, power torsion and quotient rings. The exact chart-ring blueprint search finds the item itself; other strict-transform nodes concern gluing, geometric identification or closedness, not another definition of this same ring. In particular `lemma-nagata-strict-transform-chart-closed` consumes this definition and must not be a dependency of it. I read the existing submodule lemma instead of creating an ideal-closure lemma. A regular module submodule is an ideal, so a new lemma would duplicate an elementary specialization. I searched all definition nodes for quotient-ring titles, ids and Mathlib matches and reused `def-weil-pbc-algebra-hom-quotient`.

All Mathlib searches were run with msearch.py and recorded verbatim in searches.jsonl. Two LeanFinder phrasings and LeanSearch returned affine-image, quotient, adic-completion and related facts, not this particular chart definition. Loogle executed and reported unknown identifiers for `Submodule.powTorsion` and `Ideal.Quotient`; these errors are recorded as results, not represented as successful theorem matches. Source grep found no StrictChart, strict-transform or powTorsion declaration in Mathlib/RingTheory. A second grep and a precise quotient-instance grep found the generic quotient API. I read `Mathlib/RingTheory/Ideal/Quotient/Defs.lean:39–83` and `Operations.lean:354–382`, including `Ideal.instHasQuotient`, `Ideal.Quotient.commRing`, `Ideal.Quotient.algebra`, and `Ideal.Quotient.mkₐ`. They implement the generic quotient constructor but do not define the project-specific tensor-product chart or its power-torsion ideal. The quotient API is therefore reused through its existing Mathlib-leaf node, and the whole item remains a split definition.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to distinguish.

## Review by Q130

I read the chapter and unit records, the current main-20261015 item source and the adjacent base-change-chart and power-torsion source files. The current item has the same quotient formula as its blueprint_update. The unit's one proof paragraph explicitly asks for quotienting the pulled-back chart by a_i-power torsion. This definition realizes that construction directly and does not replace the unit's route. The item source has no proof: this is the introduction of a ring, not the theorem identifying its spectrum with a geometric strict transform. There are no numbered non-elementary proof steps, no hidden long steps and no new source lemmas requiring Stacks tags.

I opened and read the statement of every dependency, not just its metadata. For the chart-construction part, `def-nagata-strict-transform-basechange-chart-ring` states “Let $A\to B$ be a ring map, let $I\subseteq A$, and let $a\in I$” and defines $C_a=B\otimes_A A[I/a]$. It explicitly says to regard a through the structural map A to C_a. These are exactly the objects and map used here. The corrected statement supplies the same data and treats I as an ideal, as required by the blow-up-chart definition that this existing node uses.

For the torsion part, `def-nagata-power-torsion` defines Gamma as the elements killed by some nonnegative power. I apply it with R=M=C and element alpha. The existing `lemma-nagata-power-torsion-submodule` states exactly that this subset contains zero and is closed under addition and scalar multiplication. For the regular C-module, scalar multiplication is ring multiplication; closure under negatives follows by multiplying by -1. Thus its statement supplies precisely the ideal needed for this definition. Although the imported lemma says “ring” without a commutativity qualifier, this use is in a commutative C, so the commuting-scalar issue in the general noncommutative wording is not used. I do not infer anything about localization kernels, saturation, torsion-freeness, scheme-theoretic closure or blow-up comparison from this submodule statement.

For the quotient part, `def-weil-pbc-algebra-hom-quotient` states that for an ideal J of an R-algebra D the quotient ring D/J is an R-algebra through the quotient map. It therefore supplies the ordinary quotient-ring notion at D=C and J=T (R can be C itself, or A via the structural map). It does not assert the geometric strict-transform interpretation, and I have not taken that theorem from it. The denominator's ideal structure is supplied separately, so this use is not the error of citing a definition for an unprovided theorem. This off-unit node is already a Mathlib leaf and is used only as a generic notion; no off-unit proof route is involved.

I checked the definition on degenerate cases. If alpha=0, every c is killed by alpha^1, so T=C and C/T is the zero ring. This includes a=0 and I=0 (the chart A[I/0] lives in the zero localization). If alpha is a unit, alpha^n c=0 implies c=0, so T=0 and the quotient is C; in particular take I=A and a=1. If C is the zero ring, the formula remains a legitimate quotient. For nontrivial torsion, take A=Z, I=(2), a=2 and B=Z/4Z. Here A[I/2]=Z and C=Z/4Z; every element is killed by 2^2 and the quotient is zero. For A=Z, I=(2), a=2 and B=Z, C=Z has no nonzero 2-power torsion, so the quotient is Z. These checks confirm that no unjustified nonzerodivisor or injectivity condition is hidden in the construction.

Against delivery-errors B–E: no new unsplit node has acquired a proof sketch; no duplicate or elementary sublemma was created; every notion and the well-definedness theorem has its existing node; no proof clause was moved into a renamed node; no cycle through closedness or strict-transform-comparison nodes was introduced; no geometric theorem was silently added to this definition. The only correction is the explicit standalone context and structural image described above. The report and empty citations list reflect that definitions have no proof steps.

## Unfinished work

None for this one-level split. The independent mathematical review and any attachment/closure verification remain with the maintainer, as the brief specifies.
