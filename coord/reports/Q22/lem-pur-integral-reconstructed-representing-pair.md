## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-integral-reconstructed-representing-pair.json`: statement item, now split into seven proof steps. The statement is unchanged. The current `literature/blueprint/latest/` proof replaces the historical snapshot path as the source. Inherited search records and metadata are retained; the five actual searches of this run are appended.
- `citations.json`: 21 verbatim statement excerpts, one for every citation in every step.
- `report.md`: this worker report and direct-delivery review.

There are **0 new nodes and 0 new Mathlib leaves**. Generic concentration, truncation normalization, strict-system cohomology, actual reconstruction maps and Brown comparisons already have nodes. Creating another recognition or integral-Hom lemma would repeat existing tools or merely relabel a clause of the item.

## Attachments

None. I searched the actual `lean/WeilConjectures/` library for the blueprint tag, reconstructed representing pairs, and representing-pair names, then read the related categories of existing DAG tools. There is no project declaration stating every clause of this item. Abstract Mathlib adjunction formulas cover only the categorical calculation, not the supplied ordinary derived-system recognition and exceptional counit.

## Wanted literature

None.

## Findings and changes

The imported item had an empty proof. Its existing source was an agent refinement, not a verbatim literature theorem. I retain that distinction: `proof_origin.by` is `agent`, and the steps give the argument rather than treating the source reference as a proof. I read the current latest integral-adjunction proof and bijection proof and the current purity-transport unit and proof. The supplied-input statement works for an arbitrary positive-characteristic field; the smooth morphism and algebraic-closure assumptions of `det-sp-integral-adjunction-bijection` do not apply here. That existing blueprint lemma is therefore not used to infer this more general assertion.

The blueprint ancestry helper prints `blueprint.from.node = None`, consistently with the live seed item's ancestry through the target. I preserve its `from` record and give the exact latest blueprint proof places in `split_report.blueprint`; this delivery does not invent a blueprint ancestor.

The proof expressly separates the equality of actual system maps from equality after evaluation. Only maps between complexes concentrated in one common degree are recognized componentwise; there the existing functorial good-truncation theorem identifies the maps with maps in the strict abelian system category. The formula for the integral trace is first proved using naturality and triangle identities in the actual system category and is then evaluated. It never assumes that evaluations are faithful on arbitrary derived-system Hom sets.

## Not duplicates

No new node was created. The whole-DAG and whole-blueprint searches found `lem-pur-good-truncation-exact-normalization`, `lem-pur-exact-derived-cohomology-coherence`, `lem-pur-normalized-actual-reconstruction-maps`, and `lem-pur-roos-intrinsic-completeness-equivalence`; these are reused. The single-complex full-faithfulness and concentrated-complex nodes were also read. The more specialized `lem-sp-strict-line-heart-assembly` requires a rank-one source and is not substituted for arbitrary concentrated cohomology systems. `det-sp-integral-adjunction-bijection` and `lem-sp-integral-reconstruction-comparisons` require smoothness over an algebraic closure of a finite field and assert a global restricted adjoint, whereas the current item represents a Hom functor at one supplied input over arbitrary k.

## Review by Q22

I read sections B through E of `coord/delivery-errors.md` in both the main and merged copies. I checked the proof against the actual statement of every node it cites, not against constructions found only inside another node's proof. No new statement-only node or source tag was fabricated. All seven proof steps are under 2000 characters, with explicit arguments where naturality or transport carries content.

For the item's source I read the current `latest/blueprint/sec-smooth-purity/sk-prop-sp-integral-adjunction/sk-prop-sp-integral-adjunction.proof.md`, its bijection statement/proof, and the current purity-transport chapter/unit/proof. The Hom chain follows the integral-adjunction display. I also read Stacks `derived.tex` Tags 06XS (`lemma-negative-exts`) and 08J5 (`remark-truncation-distinguished-triangle`), `homology.tex` Tag 0118 (`section-truncations`), and `algebraization.tex` Tag 0A0E (`lemma-derived-completion-koszul`). These justify the generic normalization route; the simultaneous system and completed-coefficient tools remain the explicitly stated existing DAG obligations. No SGA route is used.

Step 1 uses `lem-pur-integral-reduction-uniform-tor` exactly for finite-Tor constructibility, common bounds and etale-origin witnesses of integral reductions; `lem-pur-normalized-actual-reconstruction-maps` explicitly states that reductions are normalized; and `lem-pur-coefficient-system-derived-comparison` explicitly makes exactness and evaluations levelwise. The supplied common interval for M supplies the Brown output lower bound through the given finite exceptional identifications. Thus the bounded-below, normalized, etale-origin and finite-Tor input assumptions of `lem-pur-brown-tower-finite-site-comparison` are met. Its statement supplies the transported counit, the finite counit comparisons and the R-linear Hom bijections. The characteristic and coefficient hypotheses match: p and ell are distinct and the schemes are separated finite type over the specified field.

Step 2 uses the componentwise-exact system statement and the exact-derived-cohomology comparison for concentration. I checked that `lem-pur-good-truncation-exact-normalization` is stated for any abelian category, including the category of strict varying-coefficient systems, and includes representative independence, naturality for derived morphisms, a Hom bijection in degree zero and compatibility with every exact evaluation. Shifting by r reduces precisely to that degree-zero assertion. Taking H^r of the underlying semilinear transition squares produces a genuine map of strict cohomology systems, whose inverses commute by the same equations. Conjugating by the natural truncation identifications proves both the evaluations of theta and its square compatibility. This avoids wrongly applying the sheaf-only concentrated-complex lemma to a system, and avoids importing an assumption that a finite-level family automatically lifts in general.

Step 3 uses `lem-pur-roos-intrinsic-completeness-equivalence` to bridge the intrinsic completeness predicate in the integral category and the derived-complete predicate of `lem-pur-normalized-actual-reconstruction-maps`. I checked the latter's statement explicitly gives the actual unit on every derived-complete object and the actual counit on every normalized system, with no extra bounds. The compact-support realization puts P_RK back in the integral category. The reduction/limit calculus supplies the specified adjunction and triangle identities. The displayed inverse to reduction on Hom sets is calculated from those identities, not assumed from a definition of completeness.

Step 4 composes the actual reduction/limit adjunction, composition with theta, the transported Brown Hom bijection, and the compact-support comparison alpha. The first is an adjunction to the supplied M-system, so it needs no global integral exceptional right adjoint. The Brown Hom domain was established in Step 1. The final bijection is derived from Step 3 rather than from an unsupported claim about reconstructing levelwise morphisms. R-linearity follows from the R-module constructions and the explicitly R-linear Brown and compact-support statements. All Hom sets are those of full integral subcategories.

Step 5 cites only the reduction/limit calculus because its equality is the written naturality-and-triangle calculation. Invertibility of the relevant actual units was already established in Step 3. I checked the directions: z goes from reduction of P_RM to reduction of L, alpha_M goes toward F(reduction M), and the resulting identity is R_Y(t) alpha_M^{-1} = epsilon F(theta) F(e_M). Naturality in K shows the bijection is composition with this representing trace. No general faithfulness of evaluations is used.

Step 6 evaluates the already established equality. The Brown comparison statement explicitly preserves finite counits, compact-support realization explicitly describes evaluations of alpha, and the reduction/limit calculus explicitly describes e_M at each level as the scalar-extension adjoint of the specified limit projection. These are the canonical reduction identifications assumed in the statement, so t_n has the claimed finite formula.

Step 7 writes the input naturality calculation: theta' a = G(R b) theta and a e_M = e_M' R(m) imply the equation for the Brown transposes; the final equality of integral Hom images follows from the same natural units. Setting h to the identity gives the trace square. If both systems are concentrated in the same degree, Step 2 justifies substituting the weaker level-square condition. This is naturality only for the maps of supplied data stated in the item.

I checked zero systems, the empty scheme, an arbitrary common concentration degree r (including negative r), identity maps of data and f equal to an identity. All displayed composites remain typed and the zero-category assertions are permitted by the truncation statement. Neither flatness of A_n over R nor bounded-below/full faithfulness for arbitrary unbounded pro-etale systems is used. I checked the dependency closures of the chosen generic tools for a return to the item; none creates a cycle. Off-unit generic tools are declared in `split_report.tool_uses` with their exact role, leaving the purity-transport route intact. No changes to target statements, definitions, unit records, Lean sources or launcher scripts were made.

## Unfinished work

None in the stage-1 split. The cited unsplit mathematical obligations remain existing DAG nodes for their respective workers; this item is split by one level as requested. The independent maintainer review remains the next review stage after delivery.
