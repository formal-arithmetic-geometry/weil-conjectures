## Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-parameter-root-boundary-data.json`: definition, split; no exact Mathlib match for the whole construction. Its six ingredients are existing definition nodes. Made the compatible-root presentation and evaluation formula explicit and added `def-weil-pbc-mv-polynomial-ring` to `stmt_deps`.
- `citations.json`: `[]`, because this is a definition with no numbered proof steps.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. No Lean files were written and no compiler was run. The sandbox contained no earlier node or report on arrival; existing search records in the repository item have been retained, and the actual new searches are recorded in `searches.jsonl` and appended to the item.

## Attachments

None. Searching `lean/WeilConjectures/` for the blueprint tag and parameter/root/boundary names found no declaration giving the package. I also read the existing `lean/Sheaf/Paper/ParameterRootBoundaryData.lean`: its elementary definitions match this item, but `roots_vanish`, `boundary_square`, and `test_boundary_square` contain `sorry`. This is not a finished upstream attachment. Its `lean` record, like all maintainer-owned fields, is preserved unchanged.

## WANTED

None for this elementary definition. The newest blueprint direct-image proof supplies context, not a proof of a new geometric theorem here.

## What was wrong or needed clarification

The existing statement referred to the compatible-root algebra through the strict-local tameness definition, whose geometric setting assumes prime p and regular strict-local parameters, although the actual algebra construction accepts arbitrary natural p and arbitrary parameters in a commutative ring. I retained the existing generality and wrote its quotient presentation explicitly. This clarifies the existing meaning rather than changing a hypothesis: positivity of the root orders, not primality of p, is what the zero-evaluation construction needs. The polynomial-ring definition now appears as an explicit statement dependency.

The source metadata points to the historical main-20261015 blueprint. As instructed, I read the newest `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), together with the newest unit section. That paragraph now reduces direct images to proper and open cases and contains no root calculation. The split report explicitly distinguishes that motivation from the agent-extracted returned step 2 that created this definition. I do not attribute the elementary formulas to a theorem in the newest blueprint, and preserve the maintainer-owned historical source and null blueprint ancestor. `blueprint_refs.py ancestor` confirms the ancestor is null. Searches for `root boundary`, `compatible roots`, and `profinite test` found no blueprint node stating this package; `same_as` remains empty.

## Construction and dependency audit

This item is a definition, so `proof` and `proof_deps` remain empty and `proof_origin` remains null. The following are checks of the construction, not additional claimed theorem nodes.

1. **Polynomial and quotient data.** I read the entire statements of `def-sfb-strict-local-kummer-tame-module`, `def-weil-pbc-mv-polynomial-ring`, and `def-weil-pbc-algebra-hom-quotient`. The first supplies exactly the relations x_(i,n)^n-t_i and x_(i,m)^(m/n)-x_(i,n); its geometric tameness conditions are not assumptions for forming that displayed algebra. The polynomial node supplies arbitrary variable sets, finite monomial sums, and evaluation; the quotient node supplies the coefficient quotient and its ring map. Thus N_p and the presentation specify actual data, with no chosen object from an unproved existence theorem.

2. **Well-defined zero evaluation.** Let e be polynomial evaluation at zero with coefficients reduced modulo I. For each i,n, e(x_(i,n)^n-t_i)=0^n-[t_i]=0 because n>0 and t_i is in I. For a transition relation, write m=nk. Since m,n are positive, k=m/n is positive, and e(x_(i,m)^k-x_(i,n))=0^k-0=0. Finite sums of polynomial multiples of these generators also evaluate to zero by additivity and multiplicativity. Therefore e(F)=e(G) whenever F-G belongs to J; the formula epsilon([F])=e(F) is independent of the representative and preserves addition, multiplication, zero and one. This is the elementary quotient construction, written out rather than hidden behind a new lemma. It uses no regularity, no field hypothesis, and no invertibility of p or of n. Restriction to constant polynomials is the original quotient map.

3. **Spectra and tests.** I read the full statements of `def-weil-affine-spectrum`, `def-sfb-profinite-test-objects`, and `def-pc-fibre-product`. The spectrum node explicitly includes contravariant functoriality for ring homomorphisms, so epsilon has precisely the orientation S to T. The test-object node defines the actual scheme Spec LC(P,Z) times X over Spec Z, as also confirmed in the newest blueprint `sec-proetale-coefficients/sk-prop-pe-condensed-point/def-sfb-profinite-test-objects.md`. For f:X to Y, the two components defining f[P] are the first projection to Spec LC(P,Z), and f after the second projection to X. Their composites to Spec Z agree since both are the structure morphism of X[P]. The fibre-product node explicitly supplies the unique lift for precisely such a compatible pair. Thus f[P] and q_P are actual morphisms with the stated domains and codomains. No exchange isomorphism, lisse property, integral projection theorem, or derived comparison is used.

## Small cases

For r=0 there are no variables or relations, A is canonically R, I=0, and epsilon is the quotient-by-zero identification. For p=0, coprimality leaves only order 1, and the relations x_(i,1)=t_i give the same zero evaluation modulo I. For p=1 all positive orders are allowed; all exponents used in the evaluation remain positive. For n=m the transition exponent is 1, never 0. For a zero parameter, its power relation evaluates to 0 immediately. If I is the unit ideal (for example, a parameter is a unit), the target ring is the zero ring and S is empty; the same homomorphism still exists. If R is the zero ring, all its polynomial and quotient rings are zero rings and all affine schemes in question are empty. For empty P, LC(P,Z) is the zero ring, so the actual test schemes are empty; the fibre-product lift still exists uniquely. None of these cases introduces a nonempty-stratum or nonzero-ring requirement.

## Not duplicates

No new nodes were created. The DAG search also located `def-sfb-full-parameter-root-tower`, which concerns prime p, deck characters and SNC strata, not this elementary arbitrary-p boundary/test package; `def-sfb-simultaneous-root-tower` defines finite-stage root diagrams and their colimits. The more elaborate `def-sfb-root-boundary-comparison` already cites this item and concerns derived comparisons. `lem-sfb-parameter-root-integral-nil-fibre` is the parent and asserts integral/nil-fibre properties, not prerequisites for defining the boundary. None is cited in a way that would make a dependency cycle. The existing root algebra is reused, not duplicated as a new node.

## Review by Q159

I checked the definition against the actual presentation in `StrictLocalKummerTameModule.lean` and the elementary data in `ParameterRootBoundaryData.lean`, reading the newest blueprint places named above for source intent. No new nodes need a separate source review. There are no numbered proof steps; the six statement dependencies were each opened and read in full, and the preceding construction audit identifies precisely what each supplies. In particular the fibre-product node states existence and uniqueness of the lift, not merely a name for the product, and the spectrum node states contravariance, so neither is a C4 substitution of an unstated theorem. Evaluation is provided by the polynomial definition, while representative independence is the explicit elementary calculation above, not a non-elementary fact hidden behind the quotient definition. No C1 theorem about flatness, integral morphisms, or cohomology is needed.

Against B–E: the item is self-contained and uses TeX with single escaping; there are no new unsplit nodes with concealed proof sketches, no restatement nodes, and no claimed Mathlib leaf. I ran LeanFinder with two different phrasings, Loogle, LeanSearch and two Mathlib grep patterns through the mandatory search command and read their hits. Polynomial quotient equivalences, single-root `AdjoinRoot.lift`/`evalEval`, and `Scheme.Hom.liftQuotient` are useful ingredients, not one-line matches for this compatible-root-and-test definition; the corresponding source declarations were read. The unrelated Lie zero-root hits were rejected. All actual new searches are faithfully appended to the node. I corrected the formerly implicit root presentation and the missing polynomial dependency, checked every positivity and type requirement, and tested the degenerate cases above. The definition has no proof step longer than 2000 characters. The unchanged empty proof is intentional for a definition, and `citations.json` is consequently empty. I have left the chapter, unit route, Lean ownership record and historical source fields unchanged.

## Unfinished work

None within this stage-1 definition. Existing sorried Lean theorems are later-stage proof obligations; this delivery neither compiles nor changes them.
