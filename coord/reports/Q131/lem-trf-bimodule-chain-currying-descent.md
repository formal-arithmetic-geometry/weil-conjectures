# Stage-1 report: lem-trf-bimodule-chain-currying-descent

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-bimodule-chain-currying-descent.json`: item now split, no full Mathlib match. Statement and provenance retained.
- `citations.json`: 27 verbatim citation entries covering all proof uses.
- `searches.jsonl`: actual results of five required-command searches made this session.

No new nodes or Mathlib leaves.

## Attachments

None. The project tag search returned no declaration. Concept searches found ordinary module/sheaf currying, abstract bimodule objects and tensor comparison lemmas, none stating this entire mixed-ring unbounded comparison and its descent.

## WANTED

None. All sources used are present in literature/stacks-project.

## Corrections and scope

No statement dispute or change. There was no earlier sandbox item/report and no live released repair note. The item was unsplit. I read its parent lem-trf-derived-bimodule-tensor-hom: the item supplies the actual chain comparison and derived naturality, without recreating the parent's full adjunction.

The main gap was the omitted proof of 09LN and the extra invariance needed for localization. In particular, changing a K-flat tensor factor while the other factor is arbitrary requires the existing tensor-invariance lemma, not merely the definition of K-flatness. The proof now distinguishes these facts. It proves B-linear K-injectivity of J(T,N) using its acyclic test, never preservation of K-injectivity under scalar restriction.

The current latest blueprint locality proof and sk-i-curve-zero unit, plus the recorded chapter/unit, were read. This remains the established algebraic auxiliary chain below locality; no chapter or unit route is changed. It is not the unit key node, so no unit realization fields were edited. The already specific blueprint.from.place is retained. Whole-blueprint searches for currying, 09LN, K-flat and Hom complex found no statement of the item; same_as remains empty.

## Mathlib searches

All original Q63 search records were retained. New queries were two LeanFinder phrasings, Loogle, LeanSearch and the Mathlib grep; all services answered. Their actual outputs are in searches.jsonl and appended to mathlib_searches. I read ModuleCat.monoidalClosedHomEquiv at Mathlib/Algebra/Category/ModuleCat/Monoidal/Closed.lean:29 and HomologicalComplex.tensorHom at Mathlib/Algebra/Homology/Monoidal.lean:60. They give ordinary single-ring module currying and tensoring chain maps respectively. The other hits concern Tor, single-functor maps, or bounded K-injective criteria. None gives this complete mixed-ring total-Hom isomorphism with resolving descent as a one-line specialization.

## Not duplicates

No new nodes. Full-DAG and blueprint searches found the tensor invariance, Hom invariance, homotopy calculus, and resolving localization facts already present. All are reused. I checked their dependency closures for a path back to the item; none reaches it.

## Review by Q131

I read dga.tex, Tag 09LN, lemma-tensor-hom-adjunction, including its omitted-proof hint. Steps 1–4 implement the balanced pairing argument explicitly. In step 1 the two cited definition statements supply total Hom and total tensor; balancing follows from f(ba)(t)=f(a)(bt), and the inverse is checked on pure tensors. No B-action on N is assumed. Step 2 uses the same definitions to reindex the product by all pairs (p,q), and maps out of the direct sum are families on summands. No illicit exchange of tensor with a product occurs. Step 3 expands both differentials and checks the p+n and n signs. Step 4 evaluates both naturality composites to gamma(f(alpha(a'))(beta(t'))). These steps are elementary expansions, not claims that the omitted source proof is already a lemma.

For step 5 I read more-algebra.tex, Tag 064L, lemma-derived-tor-quasi-isomorphism-other-side and the preceding K-flat quasi-isomorphism lemma. I opened lem-pc-kflat-tensor-quasi-iso: it permits an arbitrary other factor and requires both endpoints K-flat, exactly what beta satisfies. The fixed T' tensor invariance for alpha is expressly stated in def-pc-module-kflat-complex. The signed flip and its two exponent checks reconcile the factor order with the cited node. Restriction preserves cohomology because kernels, images and their quotients have the same additive groups. No flatness of B over S is used.

For step 6 I read sites-cohomology.tex, Tag 0A95, lemma-RHom-well-defined and opened lem-pur-rhom-well-defined. Its arbitrary source quasi-isomorphism and K-injective target hypotheses apply on the small one-object S-site to the restricted tensor map and gamma. It gives precisely the right vertical map; the chain isomorphisms conjugate it to the left vertical map. Its separate application to U beta gives the B-linear J comparison, whose precomposition action is checked. In step 7 the same node makes Hom from the acyclic restricted tensor acyclic. I read Tag 0A8Z, equation-global-cohomology-hom-complex and opened lem-pur-hom-complex-global-homotopy: on the one-object B-site its H^0 is B-linear chain maps modulo B-linear homotopy, without boundedness hypotheses. Together with the actual definition in def-pur-kinjective-complex, this proves K-injectivity over B, rather than just S-linear null-homotopy.

For step 8 I read more-algebra.tex, Tag 064I, lemma-derived-tor-homotopy and Tag 0GWP, lemma-symmetric-monoidal-homotopy-category. I opened lem-sfb-total-tensor-homotopy: it explicitly gives tensor on homotopy classes. Module tensor is additive and preserves colimits by its bilinear presentation, and modules have all colimits. I opened lem-sf-equivariant-hom-resolution-calculus: its stated signed source homotopy and target homotopy formulas apply to Hom_S on S-modules, which have countable products. I use only those formulas, not any unsupported quasi-isomorphism invariance. The latter is proved separately in step 6.

For step 9 I read sites-cohomology.tex, Tag 06YS, lemma-K-flat-resolution; the construction preceding Tag 06YU, definition-derived-tor; and Section 07A5. I opened lem-weil-pbc-site-derived-tensor-descent: its resolving equivalence assumes flat-term K-flat complexes on a small site. Accordingly I use that subcategory first on the one-object B-site, and cite lem-pc-kflat-resolution separately to compare every K-flat T with it. I read derived.tex, Tag 070I, lemma-K-injective, and opened lem-weil-pbc-kinjective-hom-derived, which supplies full faithfulness for K-injectives. Essential surjectivity comes separately from prop-pur-kinjective-resolutions-exist on the small one-object S-site. These results apply to unbounded complexes. None is inferred from a definition.

For step 10 I read categories.tex, Tag 04VG, lemma-properties-left-localization, and the complete statement of lem-weil-pbc-localization-universal-property. The node explicitly includes natural-transformation descent, uniqueness and compatibility with composition; bare functor factorization would be insufficient. Steps 6 and 9 verify the hypotheses for successive localizations in A and T with opposite variance, and the equivalence in N. The inverse-square identity is written out. This does not assert that arbitrary derived arrows already have raw chain representatives between the initially chosen complexes.

For step 11 I read sites-cohomology.tex, Section 08J7, section-internal-hom, and opened def-pur-derived-internal-hom. Its statement explicitly supplies the derived bifunctor and comparison with any K-injective target. Step 7 licenses its use over B on the left. I rechecked the tensor model clause of lem-weil-pbc-site-derived-tensor-descent; fixed-factor invariance and the between-K-flat tensor node justify the two comparison maps. Thus the stated canonical model identifications are actual consequences of the cited statements.

I checked delivery-errors B–E point by point: no new node hides a proof; every non-elementary fact is a cited statement; no fact is extracted from a cited proof or a mere definition; no cycle; no clause moved to a replacement node; and all smallness, flatness, K-injectivity and variance assumptions are explicit. Generic off-unit tools are declared in split_report.tool_uses with reasons; existing Mathlib leaves are already tools. Every step has fewer than 2000 characters. Edge cases checked: A=0, T=0 and N=0; complexes supported in one arbitrary degree; odd and negative p,n, where only parity matters; characteristic two; and infinitely many nonzero degrees, where cochains are unrestricted products but elements of tensor sums still have finite support. Zero rings cause no exception. No source error was found.

## Validation and unfinished work

Local JSON parsing, unchanged statement, exact proof-dependency union, all 27 verbatim quotes and step lengths were checked. The server review_split check passed with zero new nodes and only the pre-existing empty unit-realization notice. The required deliver.py dry run and push follow this report. No mathematical part of this one-level split is unfinished.
