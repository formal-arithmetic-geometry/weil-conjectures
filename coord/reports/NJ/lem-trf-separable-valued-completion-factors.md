# NJ: lem-trf-separable-valued-completion-factors

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-separable-valued-completion-factors.json`: statement item split into eleven proof steps; thirteen existing dependency nodes, zero new nodes, zero new Mathlib leaves.
- `citations.json`: a verbatim statement quotation for every step/dependency pair.
- `searches.jsonl`: actual msearch output log; existing upstream searches retained in the item, new searches appended with their actual queries and result metadata.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, separable/completion, henselian/valuation and spectral-norm names found no declaration giving this item's full statement. Existing partial DVR and curve-branch declarations do not cover arbitrary nondiscrete rank-one fields. No Lean was written and no compiler or build tool was run.

## WANTED

WANTED: `literature/temkin-stable-modification-arXiv-0707.3953v3.pdf`, §2.1 and Proposition 2.2.1, printed pp. 7 and 11–12, for lem-trf-separable-valued-completion-factors. This named PDF is absent from this read clone. I read the primary HTML at https://arxiv.org/html/0707.3953v3#S2.SS2, including the valuation background and the entire proof of Proposition 2.2.1. I did not download or write literature into the repository. The assembly is explicitly marked `proof_origin.by: agent` because the source asserts the completion decomposition as a standard input rather than proving its algebraic and topological identifications. The report records the missing PDF rather than pretending it was locally read.

## Audit findings and route

The item is true as stated; no statement correction or additional hypothesis was needed. The source's notation `F_i^circ = F_{m_i}` in the converse proof refers to localization of the integral closure, not localization of the abstract field; the item already uses the correct ring C. Nonarchimedean completeness is not maximal-ideal-adic completeness when the value group is nondiscrete. I therefore did not use an adic-completion henselianity theorem or any Noetherian normalization theorem. The Newton argument works directly with real absolute values.

The latest blueprint is `literature/blueprint/latest` (main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8). I read its `sk-i-curve-zero/_section.md` and `lem-trf-local-term-locality.md`, together with the chapter/unit records, GOAL, SETUP's three levels, worker brief, stage 1 and delivery-errors B–E. The ancestry is the existing specialization/nearby-cycle and semistable-alteration expansion underneath the contracting-local-term node; the imported higher route is preserved. This split handles only its rank-one valued decompletion input. The latest ancestor text does not contain a new independent completion lemma, and blueprint searches for completion, valuation, absolute value, spectral, multiplicative norm and root lifting produced no attachment or duplicate full statement. No SGA source is used.

Whole-DAG searches, including a parsed scan of titles and statements, found the spectral norm node, normalization/prolongation node, value-group torsion node and all other needed algebraic inputs. In particular, I discarded the plan to add a spectral-norm leaf when the existing `lem-trf-spectral-norm-algebraic-extension` was found. Its Mathlib source was opened at the definitions and the extension, ultrametric and multiplicativity declarations. Searches through msearch found `spectralMulAlgNorm`, `spectralNorm.normedField`, `spectralNorm_extends`, `isNonarchimedean_spectralNorm` and finite-completion facts; these prove existing component nodes, not the full item. The whole-item second phrasing found only completion embeddings and number-field special cases. No search not run was added; the inherited Q81 records are retained as provenance.

## Not duplicates

No new nodes. Every reusable component is cited under its existing id.

## Review by NJ

I reviewed the proof against the source and against every cited node's statement, not the proofs of those nodes. All eleven steps are below 2000 characters. The dependencies are algebraic or analytic input statements, rather than copies of clauses of the item. The two directions of the factor classification are written out, and no new unsplit node hides the conclusion.

Step 1 uses `lem-trf-valuation-value-group-torsion` exactly for z^n=au with u a valuation unit. Its statement permits arbitrary algebraic extensions and arbitrary valuation rank. The quotient is ordered so that z is in the ring exactly when its class is at most one. The common-power calculation makes the real normalization well-defined, multiplicative and order preserving; it recovers the given norm on F. Uniqueness follows because both a unit and its inverse have norm at most one. No stronger assertion about completion or henselianity is taken from that node.

Step 2 uses the full statement of `lem-per-valuation-normalization-localizations`: nonzero integral closure, fraction field E, nonempty maximal ideals, and the two-way localization/prolongation classification. Its hypotheses are a valuation ring and a finite algebraic extension, both supplied here. It does not assert finiteness of the maximal-ideal set, and this step does not assume it. Residue localization is written explicitly, including inversion of the nonzero denominator in C/m.

Step 3 uses `def-weil-vector-space-scalar-extension` for the basis and dimension after tensoring, `lem-weil-pbc-finite-separable-tensor-field-reduced` for reducedness (the separability hypothesis is checked), and `lem-weil-pbc-reduced-noetherian-total-ring-fractions` for the compatible product-of-fields map. I read the local Stacks proof at algebra.tex label lemma-total-ring-fractions-no-embedded-points, Tag 02LX. Noetherianity and Q(N)=N are proved by finite-dimensional linear algebra in the step. The zero-algebra case is excluded by d=[E:F] at least one. Thus every factor is a nonzero finite field extension of K.

Step 4 uses the existing Mathlib spectral norm node for an extending, multiplicative ultrametric norm. I opened Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean at spectralNorm_extends (573), isNonarchimedean_spectralNorm (645), spectralMulAlgNorm (841), normedField and normedSpace. `lem-per-finite-normed-space-complete` applies because K is complete and nontrivially normed and every factor is finite-dimensional; no local compactness is used. `lem-zl-finite-separable-tensor-primitive-presentation` gives a primitive element and an explicit tensor/quotient presentation. Its tensor order is reversed by the elementary exchange e tensor b maps to b tensor e. The coefficient approximation estimate proves density, and the limit on Cauchy classes gives the claimed completion isomorphism with its scalar compatibility.

Step 5 checks the converse without assuming the completion is finite in advance. A map from the finite product to the field completion selects exactly one idempotent; the induced field map is injective. Its image is finite-dimensional with the actual inherited norm, so the completeness node applies to that image. The argument that a complete subspace is closed is written as a sequence-limit argument. Dense E forces surjectivity. `lem-sfb-algebraic-absolute-value-unique` applies to the two norms on that finite field over the complete nontrivially normed K and identifies the pulled-back norm with the spectral one.

Step 6 uses only the previously established maps. Equal restrictions would identify the Cauchy completions by maps fixing E and K and therefore make distinct coordinate kernels equal; the coordinate idempotents explicitly rule this out. Together with Step 2 this proves finiteness and nonemptiness of all maximal ideals of C. The pure-tensor formula is retained through the construction; the result is the canonical map specified in the item.

Step 7 proves the simple-root condition by Newton iteration, including derivative units, quadratic error, a Cauchy bound and the correct residue of the limit. I read algebra.tex Definition 04GF and the statement/proof of 04GG (lemma-characterize-henselian); the existing `lem-weil-pbc-henselian-local-root-lifting` explicitly equates that root condition with the item's idempotent-lifting convention. The binomial expansions have integral coefficients of norm at most one, so they work in positive characteristic and in nondiscrete valuation rings. Completeness is metric completeness of K, with no assertion of maximal-ideal-adic completeness.

Step 8 uses the spectral existence and absolute-value uniqueness statements over K and the same normalization/prolongation statement for an arbitrary finite extension H/K. Separability is not required here: Step 1 and each cited statement have algebraic hypotheses. Every extending valuation ring has the same normalized norm, so the integral closure has exactly one maximal ideal and equals its localization. This proves its identification with the closed unit ball. Applying it to the completed factors is justified only after Steps 3–6 establish that they are finite over K.

Step 9 uses `lem-weil-pbc-valuation-ring-normal` to verify normality of A, and `lem-sfb-integral-minpoly-fraction-descent` with A contained in C and fraction fields F contained in E. I read algebra.tex Tag 00H7 (lemma-minimal-polynomial-normal-domain), statement and proof. Integrality is exactly x in C. The polynomial quotient node states the evaluation isomorphism onto F(x); polynomial division gives its basis and dimension. The scalar-extension node transfers that basis. Thus the projection to each completed factor really is generated by x_i, not merely algebraic over K.

Step 10 proves the distinct-factor product by division, irreducibility, distinct coordinate kernels and equality of degrees, rather than assuming that the completions were already indexed by irreducible factors. For integral coefficients of each f_i, the same 00H7 node applies to R contained in its actual integral closure D_i in L_i; the fraction field and normality hypotheses were checked. The claim is not inferred from an arbitrary polynomial factorization over a nonnormal ring.

Step 11 uses the polynomial quotient node for L_i=K(x_i) and evaluation at an arbitrary root in the algebraic closure. This constructs the field embedding explicitly. The uniqueness node then compares the two actual extending absolute values on L_i. No separability of the algebraic closure nor unproved claim about automorphism transitivity is used.

I tested E=F, x=0 when E=F, an already complete base (one factor), a nonhenselian valued base with several factors, a ramified extension, positive characteristic, purely inseparable H/K in Step 8, and nondiscrete value groups. No claim of [L:K]=ef, finite normalization, defectlessness, local compactness, DVR structure or finite residue field occurs. All citations have verbatim quotes in citations.json. No source or item statement was weakened. The statement dependencies were preserved; every proof use occurs in proof_deps. Generic off-unit tools are declared in split_report.tool_uses with their purposes, leaving the unit route unchanged.

## Unfinished work

No mathematical clause left unfinished in this one-level split. Existing unsplit dependencies remain their own items. The required server dry run and direct push are the final validation and delivery steps.
