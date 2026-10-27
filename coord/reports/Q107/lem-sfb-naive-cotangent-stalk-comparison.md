# Stage-1 report: lem-sfb-naive-cotangent-stalk-comparison

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-naive-cotangent-stalk-comparison.json: existing statement node, now split into four proof steps; no Mathlib match.
- citations.json: exact statement quotations for every cited node in every step.
- report.md: this report. searches.jsonl is the unedited msearch command log.

No new nodes; zero new Mathlib leaves. The statement, statement dependencies, inherited citations and inherited searches are retained. No Lean files were written or compiled.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag and for naive cotangent/stalk and sheaf-complex terminology found no declaration giving this statement. The cotangentSheaf construction in AlgebraicGeometry/TangentSpace.lean is about sheaves of differentials, not this two-term complex and its comparison.

## WANTED

None: all sources used are in literature/stacks-project.

## Findings and corrections

The imported item is correct. Stacks modules.tex Tag 0D09 reduces to pullback along the inclusion of the point. Instead of creating another pullback lemma, the proof reuses lem-sfb-topos-naive-cotangent-pullback, whose statement gives the canonical comparison of the standard complexes for an arbitrary geometric morphism (sites-modules.tex Tag 08TZ). This is a genuine specialization of an existing stronger node, not a new node restating the item.

The extra sectionwise germ compatibility is written explicitly, rather than inferred from the bare existence of an isomorphism in the derived category. Polynomial variables, conormal classes and differential tensors are tracked separately. No statement correction or source dispute was needed.

The current blueprint was searched with tools/blueprint_refs.py (naive cotangent, stalk comparison), and the current direct-images proof in literature/blueprint/latest was read. There is no blueprint node with the same statement. The inherited blueprint.from.node is null; blueprint_refs.py ancestor confirms None for this descendant chain. The inherited detailed place and via chain are preserved, rather than inventing an ancestor. Its historical wording mentions the alteration/moduli prerequisite chain; the present blueprint direct-image step is the compactification assembly. This supporting local-complex calculation changes no unit or chapter route.

Mathlib searches: all five new searches in searches.jsonl were run through msearch.py and their results read. Two semantic phrasings, Loogle, grep and LeanSearch found stalk/localization formulas, pullback adjunctions, free-module pullback, and presheaf differentials, but no theorem for the naive sheaf cotangent complex. I read the pullback/sheafification declarations in Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean; they do not state the item. The earlier Q87 searches remain in the item as inherited records and were not presented as new runs.

## Unfinished work

None for this one-level split. The already-existing general pullback node remains an unsplit dependency, as permitted by stage 1. This delivery supplies its specialization, not its proof.

## Not duplicates

No new nodes were created. Existing stronger and generic results were reused.

## Review by Q107

I read modules.tex section-netherlander, including the standard sheaf polynomial construction, the functorial square, lemma-pullback-NL and Tag 0D09. I also read sites-modules.tex lemma-pullback-NL (Tag 08TZ), which covers arbitrary geometric morphisms and makes the point inclusion a legitimate instance. I opened every node cited below and checked its statement, not its proof. All quotes in citations.json are verbatim substrings of those statements.

Step 1 uses lem-weil-pbc-sets-inverse-image-colimits-finite-products for the actual adjunction and finite-limit preservation: a definition of geometric morphism alone would not supply these facts. The inverse-image-stalk node states the ring and abelian-group isomorphisms and their unit/germ formula. The inverse-image-module definition specifies multiplication on representatives, and the module-stalk definition gives (rs)_t=r_t s_t. Thus the identification is linear with the correct stalk scalars. Evaluation on the only nonempty open identifies sheaves on a point with their underlying algebraic objects; the empty-open value is forced by the sheaf condition. The one-point site and the opens of T fit the item's chosen universe.

Step 2 cites the existing topos pullback statement. It explicitly concerns termwise inverse image of the standard two-term complex and the canonical polynomial, kernel, quotient and differential comparisons. These are precisely the facts taken from it. The rings are arbitrary commutative ring sheaves, as required, and no flatness, local finite presentation or separation assumption enters. This citation is in the item's own unit. The inverse-image-stalk lemma is a generic tool from another unit, recorded in split_report.tool_uses; it replaces no unit-level mathematical argument.

Step 3 checks the requested morphism, using the inverse-image unit formula, the canonical identifications in the topos comparison, the polynomial universal property, the universal derivation, and the explicit standard complex in the sheaf-polynomial node. Sending x_b to x_(b_t) commutes with evaluation and sends a kernel element to a kernel element; products of kernel elements map to products, so the quotient map is well-defined. The differential square is [h] -> 1 tensor dh -> 1 tensor d(h_t) on either path. This is an elementary verification from those statements, not a hidden comparison lemma. The tensor-factor order differs from the standard sheaf display only by the canonical symmetry of tensor products.

Step 4 checks naturality on coefficients, polynomial variables, quotient classes and generating differential tensors. The polynomial and derivation universal properties and tensor generators are explicitly available from the cited definition nodes. The module-stalk definition gives functorial germs. Equal chain maps have equal images under derived localization, as specified by def-weil-abstract-derived-category. The displayed map has semilinear coefficients before extension of scalars, exactly as the item's convention requires; no claim of a derived base-change tensor equivalence is introduced.

I checked B--E of delivery-errors.md: there is no clause moved to a new node, no circular dependency, no unsupported source tag used as a black box, and no application under stronger hypotheses. A traversal of the actual statement and proof dependencies of the pullback and stalk tools does not reach this item. All four proof steps are below 2000 characters. Small cases checked: for T a point the comparison is the identity standard complex; for A=B it still compares the actual standard presentations (not incorrectly the zero chain complex); zero rings are allowed; a non-T1 space causes no issue since the singleton inclusion is continuous even when the point is not closed. The empty space has no t and gives no instance. No finiteness of polynomial variables or kernels was used.
