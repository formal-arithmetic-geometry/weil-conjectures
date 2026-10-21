# Stage-1 worker report

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-free-completion-transport.json`: statement, split; seven proof steps; no exact Mathlib match. The statement and its hypotheses are unchanged.
- `citations.json`: verbatim statement excerpts for every cited node in every step.
- No new nodes, no new Mathlib leaves, and no unit/chapter changes.

## Attachments

None. Searches in the live `lean/WeilConjectures/` by the exact blueprint tag, the item id, finite-free completion terminology, Koszul, and derived completion found no declaration giving this full ringed-site statement without sorry. Existing completed-free-presentation and adic-operation declarations concern other statements. This delivery does not claim that the general ringed-site reflector has been proved in Lean: its node's current Lean metadata concerns a specialization. Its general mathematical statement is the input used here.

## WANTED

None. All literature used is present.

## What needed work

The item was an unsplit extraction of the retained scalar-extension steps 6–7. The strict-tower transport alone gives the parameter a(t), not the desired parameter v. Moreover a triangle comparison alone would not specify the unit or prove tower coherence. The split now supplies the augmented tower calculation, uses the existing unit-power completion comparison through the existing Cech–Koszul dual-limit theorem, and proves the coherence equations by the actual reflector Hom bijection. It never replaces total derived inverse limit by a termwise product cone on arbitrary sheaves.

The imported statement is sound: no STATEMENT-DISPUTED correction is needed. The proof does not require injectivity of t or v, Noetherian coefficients, bounded complexes, or exact countable products. In particular, the narrower finite-free completion exchange lemmas that assume regular parameters and exact products are not used.

## Unfinished work

None within this stage-1 item. The two principal inputs already exist as unsplit nodes; splitting or proving those is separate work. No Lean was written or compiled.

## Sources and searches

I read `literature/stacks-project/algebraization.tex`, Tag 099B (`lemma-derived-completion`), Tag 0A0E (`lemma-derived-completion-koszul`), and Tag 0999 (`definition-derived-complete`) with the following paragraph on the triangulated complete subcategory. I also read `more-algebra.tex`, Tag 0913 (`lemma-extended-alternating-Cech-is-colimit-koszul`), and `sites-cohomology.tex`, Tag 0A0A (`lemma-colim-and-lim-of-duals`). These explain the augmented Cech model and its Koszul dual-limit realization. The finite-free combination and coherence arguments are marked agent-written, rather than attributed verbatim to Stacks.

I read the current main-20261015 blueprint `prop-weil-pbc-scalar-extension.md`, the retained DAG scalar-extension steps 6–7, the chapter and unit records, and the whole statement of every cited node. Whole-DAG and whole-blueprint searches for finite-free completion, Koszul completion, scalar extension, and the relevant tags located the existing strict-tower, unit-power, dual-limit and exact-completion inputs. No blueprint node states this entire general statement in another form; `blueprint.same_as` remains empty. This is foundational scalar-extension work below the fixed proper-base-change route; no unit step is replaced.

All new Mathlib queries were executed through `msearch.py` and logged in `searches.jsonl`. LeanFinder was queried twice with different formulations; Loogle, LeanSearch, and Mathlib grep were also run. The services all returned answers. The hits concern free sheaves, ordinary finite-sum completion, or ordinary Noetherian completion. I read `Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean:328`: the equivalence assumes a Noetherian ring and finite ordinary module and does not state an unbounded derived sheaf-completion comparison with its unit. Original item search records are retained; this session's exact queries and outcomes are appended.

## Not duplicates

No new nodes are proposed. The general strict-tower transport is strictly broader in towers but says nothing about replacing a(t) by v or completion coherence. The unit-power lemma treats one coefficient ring and cannot supply finite-free scalar transport. Both are reused. The existing finite-free completion exchange/coherence lemmas have regularity and exact-product hypotheses absent here, so are not used as if they proved this statement.

## Review by NL

I checked sections B–E of `coord/delivery-errors.md` against the actual files and sources. There are no statement-only children to audit, no new claims to disguise as leaves, and no relabelling of the item's clauses. Every cited fact is taken from a node's statement, not from its proof or Lean metadata. The source is tagged, the blueprint ancestry is retained and made precise, and no SGA source is used.

Step 1 uses the finite-free strict-tower statement for exact termwise tensor and the derived-change-of-rings statement for its identification with C. I checked that both allow unbounded derived categories on the same small site. The tensor-complex definition supplies the two-copy total differential. The written balanced-tensor formula checks the differential, transition, and augmentation separately. The bounded two-term Koszul tensor is a cone of a map between two copies of P, so its invariance under quasi-isomorphisms is immediate; no flatness of P or exactness of products is inferred. This is an elementary calculation from the cited inputs.

Step 2 takes precisely the natural isomorphism and augmented-unit equation stated by finite-free strict-tower transport. The Koszul reflector statement supplies the two limit objects and the degree-zero unit. The required tower is strict and countable and uses transition (t,1); no mere isomorphism of unspecified Roos cones is substituted. This is the first substantive theorem application.

Step 3 takes the actual augmentation compatibility from the Cech–Koszul dual-limit node and the unit-preserving reflection isomorphism from `lem-pur-unit-power-completeness`. I checked its hypotheses: same ring S, s=a(t)=wv^e, globally invertible w, and positive e. The displayed inverse-localization formulas fix the degree-zero summand and are mutually inverse even when v is a zero divisor. The source supplies a genuine augmented comparison, not only equality of the complete subcategories. This is the second substantive theorem application.

Step 4 uses both directions of the reflector's unit criterion and its explicit Hom bijection. I checked the direction of the equation C(eta)=kappa inverse composed with eta and the types of its source and target. The cancellation argument is written out; the result is not assumed from an unspecified uniqueness principle. It proves preservation of complete objects and explains why choices of basis cannot affect the canonical comparison.

Step 5 uses exact derived scalar extension for c and the generic ringed-complete-triangulated statement for r and q, their unit compatibility, and completeness of the shifted target. The two composites have exactly the same source and target. I checked each reduction after precomposition, using naturality and the already proved unit equation. Step 4 supplies injectivity for that complete target. All integer shifts follow by composing this argument and its inverse.

Step 6 writes the tensor-unit map explicitly and checks its composite with C(eta), using naturality of the actual completion unit. Its target is a reflector value, so the same checked Hom-bijection argument applies. This proves the identity normalization, rather than selecting a convenient replacement comparison.

Step 7 verifies both hypotheses needed for direct transport: composite finite freeness and the formula ba(t)=b(w)u^e z^(ef). The latter has a unit coefficient and a positive exponent. Because the scalar functors are exact termwise, balanced derived associativity is the written ordinary map on any representative; its inverse is also written, so no separate general coherence lemma is hidden here. I checked the types of A and B, their common composite with C_b C_a(eta), and the use of naturality of alpha. The direct comparison makes this precomposition a completion unit up to the natural associator, which justifies cancellation. Induction and the explicitly associative pure-tensor formula handle longer finite towers.

I tested the statement at M=0, rank d=0 (then S is the zero ring sheaf and D(S) is trivial), t=v=0 (completion is the identity), invertible t and v (completion is zero), and e=1. A nilpotent or zero-divisor parameter is allowed and is handled by the Cech model; no quotient-by-parameter identification is used. The identity case is normalized by its actual unitor. All seven steps are below 2,000 characters; none contains an unrecorded standard comparison lemma.

The off-unit uses declared in `split_report.tool_uses` are the generic derived scalar functor, unit-power reflection comparison, and exact completion/shift theorem. Their statements apply to arbitrary small ringed sites and are used as tools, not as replacements for the unit's proper-base-change route. The other inputs are already in the item's proper-base-change unit.
