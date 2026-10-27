# Stage-1 delivery: lem-sfb-space-surjective-qcoh-limit

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-surjective-qcoh-limit.json: item, statement; split into seven steps, not a Mathlib leaf.
- dag/nodes/sec-six-functors-basics/lem-sfb-site-basis-inverse-limit-acyclic.json: one new statement-only node, unsplit; Stacks 0BKY; no Mathlib match.
- citations.json: a verbatim statement quote for each citation of each item step.

## Attachments

None. Searched WeilConjectures/ for the exact blueprint tag, surjective quasi-coherent limits, derived limits, and relevant notions. The generic Roos and scheme formal-completion declarations do not state all the item's algebraic-space and small-etale clauses. No compiler was used.

## WANTED

None. All sources needed are present under literature/stacks-project/.

## Problems found and corrections

The item had an empty proof. Its mathematical statement is true as written; no hypothesis or conclusion was changed. Added the existing inverse-limit and site-cohomology definition citations, and explicitly said that its natural map is computed from the right derived inverse limit of the strict tower. This pins the canonical comparison: def-weil-derived-limit alone specifies an arbitrary triangle and deliberately chooses no functor or canonical object. The new 0BKY node makes the same convention explicit, without demanding exact products in the category of module sheaves.

The inherited blueprint ancestry is broken: tools/blueprint_refs.py ancestor returns None. The existing from.place does identify the supporting 0D3E input below the deformation-theory part of the nodal-curve argument. Preserved this place and the computed null ancestor; the new node's via prepends the item. Read the current latest blueprint unit and its direct-image proof; the mathematical support here stays within that inherited argument and does not replace any unit or chapter route. The item is not the unit's key node, so no unit record was changed.

## Not duplicates

The new node has source Tag 0BKY, which has no existing DAG node or blueprint match. Whole-DAG statement searches for inverse limits together with basis, acyclicity and quasi-coherence found no general ringed-site criterion. Blueprint searches: 0BKY (zero), Rlim quasi coherent (zero), limit is derived (zero); inverse limit, acyclic, quasi-coherent and Mittag searches were also inspected. The closest Mittag blueprint node is about finite abelian groups, not ringed sites. The existing lem-per-mittag-leffler-derived-limit-acyclic and lem-pc-derived-limit-roos-abelian-groups are reused for their distinct group-level facts. The existing proetale-surjective-tower result assumes a replete proetale topos; it does not apply to this small etale site. The generic 0BKY node has no geometric hypothesis or affine conclusion: the item must prove its basis acyclicity and section-limit hypotheses, so the item is not an application to a renamed clause.

## Mathlib search evidence

Read every output in search-0.txt through search-9.txt and all records in searches.jsonl. Both the item and the new node were searched through leanfinder (two phrasings), loogle, leansearch and source grep using the required msearch.py command. Services answered. For the new node the first broad grep also matches parts of names such as UnderLimits; a second narrower real grep in CategoryTheory finds CofilteredSystem.lean's Mittag-Leffler systems of sets, not derived sheaf limits. Read Mathlib/Algebra/Category/ModuleCat/Sheaf/Limits.lean and CategoryTheory/CofilteredSystem.lean: createsLimit, evaluationPreservesLimit and hasLimit prove ordinary sectionwise limits only. IsQuasicoherent is a predicate and its local-presentation API, not the item's theorem. Scheme AffineTransitionLimit concerns geometric scheme limits, while coherent/condensed sequential-epi results concern other sites and no derived-section acyclicity. None is an exact or one-line generalized match. Retained all inherited item searches and added the actual new queries and results.

## Review by Q44

I read spaces-perfect.tex, lemma-Rlim-quasi-coherent (0D3E), including its preceding non-quasi-coherence warning and full proof. I followed its route: affine etale objects, their stage acyclicity and section surjectivity, then sites-cohomology.tex lemma-inverse-limit-is-derived-limit (0BKY). I read the whole latter statement and proof for the new node: the required hypotheses are a covering collection, positive cohomology zero at each stage, and vanishing R1 lim on its section groups. Its conclusion is both the derived comparison and acyclicity of the ordinary limit. The new node states only that theorem, with all objects, size, cohomology and comparison conventions introduced, and has no proof, proof dependencies or hidden proof sketch.

For step 1 I opened def-trf-algebraic-space, def-trf-space-quasi-coherent-module and lem-pur-site-restriction-module-adjunction-exact. Their statements supply the etale site, restriction interpretation, local presentations and exact restriction. The covering argument is written out with affine open covers of each scheme object. The slice identification is the object-and-covering description, not a claim that intersections of affine charts over Z are affine. No quasi-compactness or separatedness of Z is used.

For step 2 I read all four cited statements. The first is for arbitrary commutative ring sheaves on a small site, the second gives enough injectives for Grothendieck categories, and the two evaluation comparisons are for arbitrary ringed sites with enough injectives. Their hypotheses hold in the common small-skeleton universe. I checked sites-cohomology.tex Tags 03FD and 03F3; this corrects the potential C4 mistake of citing a constant-coefficient module comparison for the nonconstant structure sheaf. The step does not assume that forgetting modules preserves injectives.

For step 3 I read lem-trf-scheme-zariski-etale-quasi-coherent-equivalence, lem-sc-etale-zariski-qcoh-comparison and pqf-lem-affine-vanishing. The first gives exactly the essential image on the small etale site and identity on open sections; the second gives cohomology comparisons with the same sheaf; the third gives vanishing on the affine open U itself. Sources read: spaces-cohomology.tex section-higher-direct-image, descent.tex Proposition 03DW, and coherent.tex Lemma 01XB. These apply to any quasi-coherent module; no coherence or finite-generation assumption was inserted.

For step 4 I opened lem-trf-scheme-etale-quasi-coherent-kernel and lem-weil-pbc-derived-functor-long-exact. The first is specifically the small-etale module kernel on any scheme U and has the precise QCoh conclusion needed. The second applies to the left exact additive section functor, with enough injectives from step 2. I also read descent.tex 06VE's small-etale exactness clause. The displayed segment E(U) -> G(U) -> H1(U,K) and step 3's vanishing prove surjectivity on sections; surjectivity of sheaves alone was never treated as sectionwise surjectivity.

For step 5 I read lem-per-mittag-leffler-derived-limit-acyclic and more-algebra.tex lemma-compute-Rlim (07KW). The cited statement allows arbitrary abelian-group ML towers, not just finite ones. The text proves the ML hypothesis by surjective composites, and uses only its R1 lim vanishing. For step 6 I rechecked the new node's full statement and def-pur-sheaf-inverse-limit. The three 0BKY hypotheses are individually discharged by steps 1, 3 and 5, and the ordinary limit is the same sectionwise module sheaf. The slice cohomology comparisons in step 2 identify its last assertion with the exact formulation in the item.

For step 7 I read all six cited statements: spec-module-tilde-sections provides localizations and quasi-coherence; affine-tilde-gamma-adjunction provides colimit preservation (hence cokernels); the Zariski/etale equivalence preserves open sections and sends quasi-coherence back to Zariski; scheme-etale-module-exact-finiteness-comparison supplies exactness; quasi-coherent-affine-section-base-change supplies the localization formula; sheaf-inverse-limit supplies sectionwise limits. The k[t]/(t^n) example is an explicit agent verification of the source's warning. Compatible residues are precisely coefficient sequences; 1 is not killed by any t-power, so localization is nonzero although each quotient vanishes on D(t). No theorem about products being quasi-coherent is used.

Checked B--E against both node files: the new statement is self-contained with genuine notion dependencies; the Stacks tag/label is correct; no doubled TeX escaping, hollow definition, extra clause-node or unsplit proof; no SGA; actual search evidence only. Every non-elementary step cites statements, not their proofs; citations.json copies their statement text verbatim. All steps are less than 1000 characters, so none hides an argument exceeding the 2000-character review threshold. Generic off-unit statements are declared as tool uses in split_report, without writing maintainer-owned top-level tool_uses.

Small cases: zero tower and empty affine U give zero sections and cohomology; a constant QCoh tower satisfies the basis criterion; finite section groups are not required; non-quasi-compact Z is allowed since covers need not be finite. The general new node works for the empty site (trivial module category), a one-object point site (ordinary surjective/ML group computation), and an eventually constant tower with acyclic stages. Omitting its R1 lim assumption would already fail on the point site; no such omission was made. Nothing remains unfinished in this one-level split. The new general criterion remains statement-only for a later worker, as required.

## Validation

Server review_split passed. First complete dry run rejected the phrase “the item’s” in step 4 under the standalone-text check. Replaced it by “the assumed surjectivity of the transition morphism”; no mathematical change. The required complete dry run is repeated before push.
