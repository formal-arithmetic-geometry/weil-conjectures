# Q27 stage-1 delivery: lem-sfb-supported-image-torsion-reductions-cd

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-supported-image-torsion-reductions-cd.json`: item, statement; split in nine steps, original mathematical statement retained. Not a Mathlib leaf.
- `dag/nodes/sec-six-functors-basics/lem-sfb-supported-image-koszul-comparison-nonpositive.json`: new statement-only prerequisite; no Mathlib match. It states relative derived comparison nonpositivity for the explicit supported-image Koszul complex, independently of any numerical dimension bound.
- `citations.json`: exact statement witnesses for every step/node citation.
- `report.md`: this report. `searches.jsonl` retains the prescribed command's actual search records. Local extracted source texts and the writing script are sandbox working material, not delivery nodes.

There is one new node and zero Mathlib leaves. No unit realization fields change: the assigned item is a descendant auxiliary obligation, not the unit's key statement.

## Attachments

None. Searched `lean/WeilConjectures/` both for the blueprint item tag and for supported images, integral images, torsion reductions and comparison. There is no exact project declaration proving both clauses under the item's hypotheses without sorry. Existing integral/lisse results do not supply the arbitrary image estimate. The new relative comparison statement also has no attachment. No Lean was written and no compiler or build tool was run.

## WANTED

WANTED: an independent proof/reference for relative nonpositivity of the supported integral-image Koszul complex, for `lem-sfb-supported-image-koszul-comparison-nonpositive`, in the full arbitrary-affine-scheme/finite-scalar-local-model generality written in its statement. This is a precise local comparison obligation, not a result attributed to classical comparison. Hemo--Richarz--Scholbach, Section 8 (8.1) and Lemma 8.6, motivate the global bound but do not prove this relative input.

The missing reference is explicit in the new node's source. That node remains unsplit, as required for a one-level stage-1 split. Its future proof must address etale-local positive-degree effacement for the actual two-term complex. Passing to strict local schemes without proving the necessary continuity would leave a gap; merely noting that strict local schemes are weakly contractible does not supply that continuity.

## What was wrong and what changed

The original item had no proof. Its warning about arbitrary images was justified: Bhatt--Scholze Corollary 5.1.6 and Stacks 099W compare classical inputs; neither states that images between integral finite scalar local models have classical derived reductions. HRS Lemma 8.6 uses geometric hypotheses and a constructible reduction route. I did not insert any such geometric hypothesis into this item or invoke the heart/constructible identification outside its hypotheses.

The finite assertion now has a complete argument using existing nodes: finite scalar models are locally constant, their actual image is classical, support extensions preserve classicality, and affine classical comparison gives the bound. The integral assertion uses the actual image's principal-reduction cone, the distinct local comparison lemma, a scalar null-homotopy, the existing all-torsion inverse-limit bound, and a two-row etale hypercohomology spectral sequence. No image/reduction interchange, integral completeness, topological closure or rank stratification is used.

On rereading I corrected an initial working misreading of the dimension assumption: the actual item bounds **all locally torsion** abelian etale sheaves. Consequently `lem-sc-cd-affine-limit` applies exactly. A prospective primary-torsion limit node and a prospective reconstruction node were discarded before creation; the latter also already exists as `lem-sc-affine-limit-sheaf-reconstruction`. Those investigations' real search calls remain in searches.jsonl. The mathematical item statement has not changed and is not marked disputed.

## What remains

The stage-1 assembly is complete relative to its explicitly stated prerequisite. A proof of the new local comparison theorem is future DAG work, and its missing exact reference is recorded above. It is the only new non-elementary obligation. No assertion is made that the local comparison lemma has already been proved in HRS, Mathlib or the project.

## Not duplicates

lem-sfb-supported-image-koszul-comparison-nonpositive vs sk-prop-sf-comparison: the existing theorem assumes classical bounded-below inputs; the new theorem concerns a potentially nonclassical actual integral-image Koszul complex and states only positive relative-direct-image vanishing, with no global numerical bound.

lem-sfb-supported-image-koszul-comparison-nonpositive vs sk-thm-pe-direct-image-comparison: that theorem compares a qcqs scheme morphism's direct image of classical discrete-coefficient complexes, whereas the new theorem concerns the comparison of sites itself on continuous-integral image reductions.

lem-sfb-supported-image-koszul-comparison-nonpositive vs lem-sfb-integral-finite-scalar-perfect-model: that node supplies a scalar perfect resolution and tensor/projection comparison; it gives no relative comparison acyclicity for images.

lem-sfb-supported-image-koszul-comparison-nonpositive vs lem-sfb-qcqs-integral-finite-model-completeness: that node assumes the module/complex itself has finite scalar local models; the new theorem concerns its arbitrary morphism image and support extensions, and does not assert completeness or classicality.

lem-sfb-supported-image-koszul-comparison-nonpositive vs lem-sfb-supported-image-torsion-reductions-cd: the item is a global numerical cohomology bound under an all-torsion etale dimension assumption, including a separate finite-coefficient clause. The new node has neither a dimension parameter nor global-sections vanishing: it is a local relative direct-image-amplitude theorem. The item's scalar annihilator, affine-limit bound, spectral-sequence filtration, and finite branch are proved in its own steps. It does not simply apply a renamed global vanishing clause.

Before creating the node I searched the whole DAG by image/reduction, Koszul/image and comparison/effacement phrases, inspected the supported-image siblings and finite-model/continuous-matrix nodes, and searched the imported blueprint with `tools/blueprint_refs.py` for image/reduction, effacement, classical, comparison and dimension phrases. No existing node states the new theorem. The blueprint ancestry is `det-sf-comp-coherence-cocycle`, via the recorded descendant list, serving refinement proof (2)'s direct-sum/affine-heart obligation. The new local estimate is not itself stated in that paragraph. No Stacks tag is claimed for the new theorem.

## Review by Q27

I read HRS Section 8 around condition (8.1) and Lemma 8.6, Theorem 6.2 and Remark 6.4, and the continuous-integral matrix discussion in Theorem 6.12. I also read Bhatt--Scholze Lemma 5.1.4 and Corollary 5.1.6, Stacks proetale.tex `lemma-compare-cohomology` (099W), and etale-cohomology.tex `lemma-cd-limit` (0F0R), including the reconstruction/continuity argument (`lemma-linus-hamann`, 0EYN). These distinguish the classical finite part from the missing local integral-image theorem. I reread the newest blueprint cocycle/refinement proofs rather than an older snapshot. No SGA source is used.

For Step 1 I opened all five cited statements: the finite module equivalence and finite scalar-model node really identify the local models with constant finite modules; local classical descent applies to the underlying sets; classical full faithfulness descends the module operations; the weak-Serre statement supplies kernels and cokernels, and the displayed kernel-of-cokernel identity supplies the image. No node is cited merely because its title mentions a similar notion.

For Step 2 I checked the operations-transport statement for both j_! and ordinary direct image, the finite open-extension comparison for an arbitrary open immersion, and the qcqs direct-image comparison. A closed immersion is affine, hence qcqs, so that hypothesis is present. The exact open/closed localization node applies because the closed arrows have qc open complements. The classical equivalence detects the annihilator. The induction uses no missing finite-type or noetherian hypothesis. Step 3's comparison theorem explicitly includes the small affine inverse-limit presentation and says that cohomology is the filtered colimit. The cited ringed-site comparison identifies module-derived evaluation with the abelian-sheaf cohomology bounded in the assumption.

For Step 4 I checked that the principal-reduction cone theorem applies to arbitrary complexes of the actual continuous integral coefficient sheaf and to the actual quotient map. It is not a result about reducing the original morphism f. The module equivalence retains the underlying sheaf. The generic ringed-site evaluation/Leray statement explicitly allows arbitrary ring sheaves and no flatness assumption, so it applies to identity-site scalar forgetting and later to the integer-ring comparison morphism. No unsupported claim that forgetting scalars preserves injective objects is needed.

For Step 5 I compared every hypothesis of the new node with the item: same affine X, chain, coefficient topology, independently varying fp scalar models, actual abelian image, v and n. Its conclusion supplies just the upper relative bound. The cited truncation theorem supplies the lower bound because its first quadrant begins at b=-1. For Step 6 I checked the DVR theorem gives the integer power decomposition used; since ell has absolute value less than one, its pi-valuation is positive. The identity homotopy on the explicit two-term complex, multiplied by c, proves the common integer annihilator, including when the image has torsion.

For Step 7 I read the exact all-torsion limit-bound statement, rather than treating a definition as a continuity theorem. Every affine stage is qcqs, arrows between affine schemes are affine, and the small cofiltered index is part of the affine-pro-etale convention. The hypothesis is all locally torsion sheaves, so it is exactly strong enough. For Step 8 I verified the spectral-sequence theorem provides a finite exhaustive separated filtration, not only an E2 page. With b=-1,0 and p<=d, no surviving term has total degree >d. The ordinary derived Leray comparison and Step 4 identify the abutment with the requested B-module-derived section complex. Step 9 checks the empty and zero cases directly.

I tested the new local statement against a zero map, an isomorphism, multiplication by pi^s between rank-one coefficient modules, empty support and empty chain, and a separably closed point. None supplies a counterexample. The variable-valuation example of multiplication by ell^m on the isolated points of beta(N), tending to zero on its boundary, prevents replacing the actual image reduction with the image of a fixed finite reduction or assuming locally constant elementary divisors. The new statement deliberately retains that case. These tests do not substitute for the new lemma's future proof, which remains an explicit obligation.

I checked delivery-errors B--E individually: the new node is self-contained and statement-only, introduces its coefficient and support data, cites definition nodes, and contains no proof sketch; searches are actual command records with both semantic phrasings read and no false Mathlib leaf. There are no doubled TeX escapes, no tag-only definitions, and no route replacement. Every non-elementary step has the cited theorem statement, with a verbatim witness in citations.json. No item clause is replaced by a new global-vanishing node. All steps are shorter than 2000 characters (the longest is under 900), and the homotopy and zero-case arguments remain elementary steps. The generic off-unit tools are declared in split_report.tool_uses with their exact purpose; these do not change the blueprint route. The server dry run is the final mechanical check.
