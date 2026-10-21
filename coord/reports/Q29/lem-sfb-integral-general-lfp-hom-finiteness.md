# Stage-1 delivery: lem-sfb-integral-general-lfp-hom-finiteness

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-integral-general-lfp-hom-finiteness.json`: existing statement, split into seven proof steps. No new nodes and no Mathlib leaves.
- `citations.json`: one verbatim statement quotation for each of the fifteen step/node citations.
- `report.md`: this report.

The sandbox also contains the actual search log `searches.jsonl` and a local text extraction of the supplied Bhatt–Scholze PDF. These are research material, not additional DAG nodes.

## Attachments

None. I searched the upstream `lean/WeilConjectures/` tree for the exact blueprint tag and for integral Hom, Hom reduction, completeness and bounded-constructible Hom. There is no declaration giving all clauses of this item. In particular `AlgebraicGeometry.ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible` in `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean:485` has a `sorry` body at line 488 and is not an attachment. The separate local-library integral Hom reduction and ringed Hom completeness declarations correspond to existing dependency nodes; neither states this whole witness assertion.

## WANTED

None. The needed Bhatt–Scholze paper and Stacks sources are supplied locally.

## Audit and changes

The mathematical statement is unchanged, including arbitrary local presentation matrices, lack of an input completeness assumption, integral torsion, arbitrary positive-characteristic ground field different from the coefficient characteristic, and the requirement about the specified evaluation-transpose reduction map. No statement dispute was found.

The item initially had no proof. Its parent already separates the residue witness from the subsequent application of the reverse cohomological adic criterion. This delivery respects that boundary: the forward criterion is applied to the two inputs only; the output is proved complete by the generic ringed-site Hom theorem, and its residue is handled by the finite-field Hom theorem. It never uses the parent preservation result or the reverse criterion on the output.

The imported ancestor pointer had `blueprint.from.node = null`. The current parent `lem-sfb-dc-hom-small-coefficients` explicitly names `lem-sfb-dc-hom-preserves` as its blueprint origin; I repaired the item's pointer to that ancestor and retained the parent in `via`. The ancestor command returns `None` here because following the parent's `created.item` reaches the stage-3 module name `Sheaf.Paper.BoundedConstructibleHomFiniteness`, rather than a node. The actual blueprint statement and proof at `main-20261015/blueprint/sec-six-functors-basics/sk-def-sfb-dc-restricted-functors/lem-sfb-dc-hom-preserves.{md,proof.md}` were read. No other node or its metadata was edited.

I searched the whole DAG and blueprint for internal Hom, derived completeness, Hom reduction and complete residue witnesses. Existing integral scalar-model comparison, cohomological adic criterion, generic local Hom completeness, integral Hom reduction, finite-field Hom finiteness, site comparison and constant-field Tor bounds cover every non-elementary ingredient. Thus there is no reason to create either an elementary node or a renamed clause of the item. Searches performed through `msearch.py` use two semantic phrasings, Loogle, LeanSearch and Mathlib grep; the hits concern underived presentations/closed structures, algebraic completion or scheme residue fields. None gives this integral sheaf-theoretic conjunction. Existing searches in the repository item were retained; new records are exactly the queries run in this sandbox.

## Not duplicates

No new nodes. All relevant matches were reused directly, especially `lem-sfb-integral-lfp-constant-model-comparison`, `lem-sfb-integral-cohomological-adic-criterion`, `lem-sf-ringed-rhom-derived-complete`, `lem-coef-integral-hom-reduction`, `lem-sfb-finite-field-internal-hom-finiteness`, `sk-thm-pe-constructible-comparison`, `lem-sfb-constant-field-tor-bounds` and `det-pe-finite-tor-comparison-noetherian`.

## Unfinished work

None in the requested one-level split. Its cited existing nodes keep their own existing proof/implementation status. There are no new statement-only obligations.

## Review by Q29

I read Bhatt–Scholze Definition 6.5.1, Lemma 3.4.11, Lemma 6.3.16, Lemma 6.7.13, Definition 6.8.10 and Proposition 6.8.11(3) in the provided PDF text. Definition 6.8.10 uses finite scalar local models, not arbitrary local matrices, so it would be incorrect to apply the paper's completeness criterion immediately to the hypothesis as written. Step 2 explicitly supplies the existing integral lfp/scalar-model comparison before applying that criterion. This is the main hypothesis issue of the item. I read the corresponding chapter and restricted-functor unit, the ancestor's integral proof paragraph, Stacks `morphisms.tex` Tag 01T6 (`lemma-finite-type-noetherian`), `algebraization.tex` Tags 0999/099A (`definition-derived-complete`, `lemma-derived-complete-internal-hom`), `proetale.tex` Tag 09AL (`lemma-compare-constructible-derived`), and the actual blueprint proofs of integral Hom reduction and Noetherian finite-Tor site comparison. There are no new nodes requiring additional source checks.

For step 1 I opened the statements of `lem-weil-pbc-finite-type-over-noetherian`, `lem-weil-pbc-locally-noetherian-quasi-separated`, `lem-weil-l-adic-extension-integers-dvr`, `det-prop-sfb-qlbar-colimit-x-integral-limit` and `lem-sf-module-object-ordinary-coefficient-equivalence`. They respectively give Noetherian permanence, quasi-separatedness, a DVR and finite residue field, the actual ring-sheaf limit identification, and the finite-discrete ring/module/tensor/local-model identification. No quasi-excellence, dimension bound or unproved geometric-point identification is being imported into this preparation. The characteristic calculation is written explicitly: the prime ell lies in the valuation maximal ideal, so the nonzero residue field has characteristic ell. The Noetherian field base has only the two ideals, as stated in the step.

For step 2 I read the entire statements of the integral lfp/constant-model comparison and the cohomological adic criterion. The first allows precisely the arbitrary local section matrices in the item and requires only a Noetherian scheme. It allows torsion scalar modules. The second is an equivalence for bounded scalar-model constructible cohomology and explicitly supplies local derived completeness together with the bounded constructible finite-Tor étale residue witness. Its (1) to (2) direction is used for K and L, not H. All coefficient sheaves and quotient maps are those identified in step 1. Only finitely many cohomology sheaves are nonzero; the original bounds are preserved in this conversion of predicates.

For step 3 the statement of `lem-sf-ringed-rhom-derived-complete` quantifies over all first arguments and complete second arguments on small ringed sites. Its local vanishing condition is verbatim the notion required in this item. Thus it takes completeness of L from step 2 and gives local completeness of H without a hidden passage from a Roos-complete notion or a site-perfect hypothesis. I deliberately use this node rather than the different completeness clause of the integral Hom reduction node.

For step 4 the statement of `lem-coef-integral-hom-reduction` explicitly says that its map is the transpose of reduced evaluation and is invertible for arbitrary K and L. I use exponent 1 (not the residue characteristic exponent and not an index shifted by one). Its completed coefficient B and quotient B_1 match step 1. Consequently no separate naturality, scalar-linearity or unspecified-isomorphism argument is being hidden. Its source proof uses the two-term finite-free resolution over the integral coefficient ring; it does not assert that one finite quotient is perfect over a larger finite quotient.

For step 5 the bounded constructible comparison node actually states a derived-category equivalence, not merely a fully faithful sheaf embedding. It therefore supplies the bounded constructible pro-étale predicates for the two input residues. The finite-field Hom node explicitly permits an arbitrary field k of positive characteristic different from ell, with no perfection or separable-closedness condition. Its inputs require bounded finite constant local models, which step 2 and the comparison provide. Its conclusion supplies bounded cohomology and finite constant local models for the actual ambient Hom. This is precisely the object identified in step 4. I rely on Bhatt–Scholze's finite-coefficient route and cite no SGA source.

For step 6 I checked essential surjectivity in `sk-thm-pe-constructible-comparison` and the full statement of `lem-sfb-bounded-representative`. The former yields an étale object with bounded constructible cohomology and the required isomorphism; the latter supplies an actual bounded complex if “bounded complex” is read termwise. Its hypotheses concern only an abelian category with a derived category and a finite cohomology interval. Finite-type modules over the residue field are finite-dimensional, with the same constructible locally closed strata.

For step 7 I checked that `lem-sfb-constant-field-tor-bounds` concerns ordinary sheaves over a constant field on the pro-étale site, not the rationalized adic category of a different field-Tor lemma. It gives the identical interval for tensor with every degree-zero module sheaf. The statement of `det-pe-finite-tor-comparison-noetherian` reflects that interval to the étale object D, for qcqs X and discrete Noetherian A. These hypotheses were established in step 1. This avoids asserting that boundedness alone over an arbitrary finite ring would imply finite Tor amplitude.

I tested the conclusions on X empty, K or L zero, finite free constant inputs, and on a geometric point with K=L=R/(t) in degree zero. In the last case Ext in degrees 0 and 1 and the derived residue of each torsion input are retained; no underived reduction or torsion-free argument is used. Shifting either input changes only finite bounds. The field-Tor argument would fail over a nonfield finite quotient such as Z/ell^2, but here A is specifically the residue field, as required. Every cited dependency was opened, and each citation in `citations.json` is copied verbatim from its statement, not from its proof. A dependency-closure traversal found no path back to the item for the major comparison, completeness, reduction or finite-field dependencies. Every non-elementary step is shorter than 2000 characters. All off-unit foundational tools are declared in `split_report.tool_uses` with the particular statement used; none changes the unit route.
