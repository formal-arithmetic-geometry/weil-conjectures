# Stage-1 delivery: lem-trf-weak-spectral-completion-product

## Files written

- dag/nodes/sec-trace-formula/lem-trf-weak-spectral-completion-product.json: item, five-step split, statement unchanged.
- dag/nodes/sec-trace-formula/lem-trf-algebraic-spectral-norm-powers.json: statement, Mathlib leaf isPowMul_spectralNorm, Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean:632.
- dag/nodes/sec-trace-formula/lem-trf-power-multiplicative-algebra-norm-unique.json: statement, Mathlib leaf spectralNorm_unique, Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean:699.
- citations.json: verbatim statements for every citation in every proof step.
- searches.jsonl: actual msearch.py results. The item's historical searches are preserved separately in its existing mathlib_searches field.

## Attachments

None. Searched the live lean/WeilConjectures for the blueprint id, spectral norm, weakly cartesian, and the two Mathlib declaration names. No project declaration states the item or either new leaf. Mathlib declarations are recorded as leaves, not project attachments.

## WANTED

WANTED: Bosch–Güntzer–Remmert, Non-Archimedean Analysis, Proposition 3.6.2/3, printed p.158 (scan PDF p.166), for lem-trf-weak-spectral-completion-product. The archival book named by the item's source is absent from literature/. I did not download it or claim to read it. The item proof is explicitly agent-written, using the locally read Mathlib source and Stacks text.

## Faults found and corrections

No statement dispute. The item has no old proof or sandbox attempt to retain. Its accepted parent already identifies the intended route: complete the finite spectral vector space, prove reducedness, decompose as fields, and identify the norm. I supplied that argument with precise cited interfaces. In particular the existing incomplete-spectral-algebra-norm node does NOT assert power multiplicativity, and the existing complete-field spectral-norm node does NOT assert uniqueness among submultiplicative power-multiplicative algebra norms. Those missing assertions now have the two exact Mathlib leaves; neither is a completion or product clause of the item. The stronger field-multiplicativity of the completion was never asserted: the completion can be a product.

## Not duplicates

lem-trf-algebraic-spectral-norm-powers vs lem-trf-incomplete-spectral-algebra-norm: the existing statement gives submultiplicativity and the norm axioms, but does not state equality on positive integral powers. The new statement is exactly isPowMul_spectralNorm, with no complete-base hypothesis.

lem-trf-algebraic-spectral-norm-powers vs lem-trf-spectral-norm-algebraic-extension: the existing statement assumes a complete nontrivially valued base and gives multiplicativity; the new power identity holds over an arbitrary ultrametric base, including the incomplete F needed before completion.

lem-trf-power-multiplicative-algebra-norm-unique vs lem-trf-spectral-norm-algebraic-extension: the existing statement constructs the multiplicative spectral norm, but does not identify an arbitrary power-multiplicative algebra norm with it.

lem-trf-power-multiplicative-algebra-norm-unique vs lem-sfb-algebraic-absolute-value-unique: the existing statement compares multiplicative absolute values. The slot norm constructed in step 4 is initially only submultiplicative and power-multiplicative. The new Mathlib lemma applies at that exact point, without an unjustified multiplicativity inference.

lem-trf-weak-spectral-completion-product vs lem-trf-separable-valued-completion-factors: the existing node assumes a finite separable extension and includes integral closures and individually valued completions. The item permits inseparability and obtains reducedness from the coordinate comparison and power identity; it is not a specialization of that node.

DAG searches used statement/title keywords (spectral norm, reduced Artinian product, power-multiplicative), declaration names, and full statement inspection of the candidates above. Whole imported-blueprint searches via tools/blueprint_refs.py covered weak spectral completion product, power-multiplicative, spectral norm, spectralNorm_unique, isPowMul_spectralNorm, and spectral. None states the new facts. Neither new source has a Stacks tag; the Stacks algebraic decomposition facts are existing nodes and reused.

## Review by NZ

I read the worker brief, stage-1 contract, GOAL.md, the three SETUP levels, delivery-errors B–E in both copies, chapter sec-trace-formula, unit sk-i-curve-zero, the current latest/ proof of lem-trf-local-term-locality, the item's statement and accepted parent lem-trf-dense-weak-stability-transfer. The current blueprint uses contracting correspondences; this is an inherited auxiliary analytic input beneath that node, and does not change the chapter or unit proof. I did not edit the unit realization because this auxiliary item is not its key statement.

For the two new nodes I read SpectralNorm.lean at 375–382, 627–679 and 688–705. isPowMul_spectralNorm at 632 is in the algebraic-extension section over an ultrametric NormedField, before CompleteSpace and NontriviallyNormedField are introduced. Thus it really applies to incomplete F and does not require normality or separability. spectralNorm_unique at 699 assumes the complete, nontrivial, ultrametric base and an AlgebraNorm with IsPowMul. The displayed axioms in the new uniqueness statement supply AlgebraNorm directly, with negation invariance from scalar -1 and the ordinary triangle inequality from max≤sum. Evaluation of the resulting function equality and spectralAlgNorm_def at 673 gives exactly the new conclusion. All four required search tools actually ran for each leaf, and the query strings and resulting declarations are preserved in the search log. The item itself was also searched with two distinct semantic formulations; none of the hits covers its completion and product assertion.

Step 1 uses only the statement of lem-trf-incomplete-spectral-algebra-norm, read in full. That statement supplies precisely the definite ultrametric, scalar and submultiplicative norm estimates used to form Cauchy classes. I wrote the product Cauchy estimate and representative-independence argument, rather than citing an unavailable general Banach-algebra completion theorem. Norm limits and passage of ring identities through representatives are direct calculations, so the step is elementary relative to the cited norm axioms.

Step 2 uses the statement of lem-sfb-normed-field-completion, read in full, for H being a complete normed field and F mapping isometrically into it. It does not take density or a tensor-product comparison from that statement: the Cauchy-class model in the item's hypotheses supplies those, and the coordinates are constructed explicitly. The incomplete norm node supplies scalar homogeneity. Positivity of c and C is essential: c makes each coordinate Cauchy and detects zero differences; C constructs all classes and proves convergence of the coordinate limit. Representatives exist for every H-coordinate by H's stipulated model. There are finitely many coordinates; no exchange of infinite products with completion occurs. This proves the H^n model and exactly n-dimensionality without invoking a finite-dimensional norm-equivalence theorem.

Step 3 cites the new power leaf for the pre-completion identity, then proves its extension by termwise powers and real limits. Vanishing of a positive power forces vanishing of the norm and then of the element, proving reducedness explicitly. I read the statements of lem-weil-pbc-finite-dim-algebra-artinian and lem-sfb-reduced-artinian-residue-product in full. The former applies because step 2 supplies a commutative finite-dimensional H-algebra. The latter gives exactly the finite canonical residue-field product with its algebra structure, not merely a topological decomposition. I also read Stacks algebra.tex, lemma-finite-dimensional-algebra (00J6), lemma-artinian-finite-nr-max (00J7), lemma-artinian-finite-length (00JB), and Mathlib/RingTheory/Artinian/Module.lean:514–641, including equivPi at 633 and equivPi_apply at 638. Finiteness of each field quotient is elementary from images of the n basis vectors. H-algebra compatibility follows by composing the canonical quotient maps with H→A. The product basis proves the degree sum. Since N(1)=1, the empty product case allowed by the cited decomposition is excluded here. Both existing algebraic nodes are Mathlib leaves, so no off-unit tool approval is needed.

Step 4 cites only the new uniqueness leaf after explicitly constructing its candidate norm. I checked N(e_j)=1 using positive definiteness and the power identity: an idempotent has norm a positive solution of t²=t. The slot injection is nonunital into A but sends 1 to e_j, which is enough to normalize N_j(1)=1; calling it unital would have been wrong. It is multiplicative and H-linear, so all the uniqueness lemma's norm and scalar hypotheses hold. Each L_j/H is finite and therefore algebraic; H is complete and remains nontrivially valued by step 2. There is no separability hypothesis to verify. Thus C4 is satisfied at the precise strength needed, with no unsupported assumption that N_j is already multiplicative.

Step 5 uses only previous steps: the finite idempotent sum and submultiplicativity give both inequalities, so the isometry is an equality, not norm equivalence. The upper inequality uses the ultrametric bound on a finite sum; the reverse uses N(e_j)=1. No unquoted theorem about spectral radii is hidden here.

I checked B1–B10: both new files are statement-only Mathlib leaves, self-contained, with inline norm axioms or the exact defining spectral-norm node, single-escaped TeX, actual search records, verified declarations/files/lines, and filled blueprint ancestry. C1–C8: every non-elementary external fact is a cited statement, every uses entry has a verbatim quote, the proof-dependency union is exact, and there are no off-unit non-leaf uses or dependencies on descendants. D1–D5: the two new facts are genuinely general Mathlib tools rather than completion/product restatements; the item carries the Cauchy, coordinate, reducedness, idempotent and maximum arguments. E1–E7: all base completeness hypotheses are used only after passing to H; no separability, stability or local compactness is added; no inverse continuity or multiplicativity is assumed without proof. No non-elementary step exceeds 2000 characters (the longest step has 1202 characters).

Small cases checked: E=F and n=1 gives H with one factor and its original norm; a separable polynomial splitting over H can give multiple factors, so treating A as a field would fail, and the argument avoids that; a purely inseparable extension becoming nonreduced on scalar extension cannot satisfy the assumed coordinate lower bound, since the explicitly constructed completion would otherwise be both power-multiplicative and have a nonzero nilpotent. Nonzero nilpotents and zero idempotents are excluded at the correct places. The zero element and all-zero coordinates satisfy every formula, and r=0 is explicitly excluded by the nonzero unit. No SGA source was used, no Lean was written or compiled, and every write is in the sandbox.

## Unfinished work

No mathematical clause remains unsplit. The BGR archival source remains WANTED; the independent agent proof is complete at this DAG level. The maintainer's independent mathematical review remains part of the delivery process.
