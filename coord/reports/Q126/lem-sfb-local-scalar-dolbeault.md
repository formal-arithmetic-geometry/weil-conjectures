# Stage-1 report: lem-sfb-local-scalar-dolbeault

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-local-scalar-dolbeault.json`: item, statement retained exactly, split into six explicit steps; no Mathlib match for the whole assertion.
- `dag/nodes/sec-six-functors-basics/lem-sfb-cauchy-transform-parameters.json`: new statement, unsplit; no Mathlib match for the cutoff Cauchy transform's right-inverse equation with smooth parameters.
- `dag/nodes/sec-six-functors-basics/lem-sfb-real-derivative-complex-linear.json`: new statement, Mathlib leaf; `differentiableAt_iff_restrictScalars`, Mathlib/Analysis/Calculus/FDeriv/RestrictScalars.lean:112, with R as the base field and C as its extension.
- `citations.json`: one verbatim statement quotation per citation in steps 1, 2 and 5. The other steps cite no external result.
- `searches.jsonl`: actual msearch.py results. Additional sandbox-only `write_split.py` is a preparation script, not a project file.

## Attachments

None. Searches in `lean/WeilConjectures/` for the item's blueprint tag, Dolbeault, scalar Dolbeault, Wirtinger and the candidate derivative declarations gave no project declaration stating this result. Broader Cauchy hits concerned sequences, power series and Cauchy--Binet, not this theorem. The upstream sorry declarations are not used as finished proofs.

## Literature wanted

WANTED: Jean-Pierre Demailly, Complex Analytic and Differential Geometry, I §3.A Corollary (3.4), I §3.C formulas (3.14)--(3.17), I §3.E Lemma (3.29), and I §8 Exercise 8.5, for lem-sfb-local-scalar-dolbeault and lem-sfb-cauchy-transform-parameters. The expected local file `literature/demailly-complex-analytic-differential-geometry.pdf` is absent. I read these places online at https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf (21 June 2012 version). No document was downloaded or written to the repository. The item is marked agent-written because the source is absent locally and the exercise's induction is expanded here.

The new Mathlib leaf's source was read locally at lines 36--44 and 100--117 of FDeriv/RestrictScalars.lean. Its place and line are recorded. There is no Stacks tag for the analytic Cauchy transform in this route; I use the specified analytic textbook rather than substitute an unrelated algebraic Stacks tag.

## Audit of the starting item and route

No statement dispute: all clauses hold as written, including n=0 and q>n. The original item had no proof. No repair note existed and no earlier split/report was present in this sandbox.

I read the chapter record, the unit record, and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof. The unit record is an older statement than that current text; I change neither. This is a lower-level analytic prerequisite already on the item's inherited route through the Dolbeault acyclic resolution. No unit step is replaced. The ancestor command explicitly returns None for this created-node chain; the inherited `from.node: null` and via list are retained, and the new nodes extend that chain with exact supporting places. The proof follows Demailly's Exercise 8.5, which the paragraph before Lemma (3.29) explicitly offers as the alternative one-variable proof.

Two details needed particular care. First, the cutoff Cauchy integral is not a holomorphic-derivative primitive: the kernel solves the inhomogeneous antiholomorphic equation. Second, subsequent integrations must preserve the equations in coordinates already removed. The parameter derivative clauses of the new analytic node expressly supply this property; it is not inferred just from existence of a one-variable primitive. I put d-bar z_k at the front of the wedge decomposition, so there is no missing degree-dependent sign.

## Not duplicates

lem-sfb-cauchy-transform-parameters vs lem-sfb-local-scalar-dolbeault: the new node is a specific one-variable integral operator on arbitrary, not necessarily closed, smooth coefficient functions, with parameter derivatives and cutoff support; the item assembles these operators to prove local exactness in every positive form degree. Neither the multi-coordinate wedge induction nor the holomorphic-function criterion is delegated to this node.

lem-sfb-cauchy-transform-parameters vs lem-sfb-dolbeault-acyclic-resolution: the latter concerns exact sheaf resolutions and global acyclicity and depends on this item; it supplies no scalar integral operator, so it cannot be cited to prove this item.

lem-sfb-cauchy-transform-parameters vs lem-sfb-chart-exterior-derivative-square-zero: d squared zero gives closedness after subtracting a boundary, but provides neither a primitive nor a right-inverse operator. The existing Mathlib leaf is reused for exactly its square-zero assertion.

lem-sfb-real-derivative-complex-linear vs lem-sfb-complex-analytic-derivative-rules: the existing node assumes complex analyticity/differentiability and gives derivative formulas and analyticity; it does not recognize complex differentiability from an assumed real derivative. The new general scalar-restriction criterion supplies that missing implication and is already in Mathlib.

The whole DAG was searched for Cauchy--Green, Cauchy--Riemann, Wirtinger, mixed partials and the exact derivative declaration names, and relevant statements were read. The blueprint searches for Dolbeault, Cauchy, mixed partial, convolution, scalar restriction, Cauchy transform and complex linear gave no matching blueprint theorem. The convolution blueprint node concerns Fourier-transform sheaf kernels, not analytic convolution. No new Stacks tags overlap existing nodes.

## Mathlib search conclusions

Every search recorded for each new node was actually run using msearch.py and its hits were read. Both natural-language phrasings, Loogle and source grep are represented. The item also has fresh searches recorded, while its earlier records are preserved.

For the analytic node I read the relevant convolution signatures in Analysis/Calculus/ContDiff/Convolution.lean:141 and 281 onward, and the resolvent-transform documentation in MeasureTheory/Measure/ResolventTransform.lean:17--39. The convolution results can support joint smoothness and differentiation later; they do not state that 1/(pi z) is a fundamental solution of d-bar. The resolvent theorem is holomorphic away from a measure's support. The circle-transform and holomorphic-primitive results have different differential equations. Thus the new analytic node remains unsplit, rather than being falsely labeled a Mathlib specialization. Its future split can separate the fundamental-solution identity, cutoff existence, and generic convolution regularity.

For the derivative criterion, the first natural-language hits mostly had domain C; the second phrasing plus exact-name Loogle found the general normed-space statement. I read its complete signature and scalar-tower variables before marking the leaf. There is no finite-dimensionality or completeness hypothesis to omit.

## Review by Q126

I checked delivery-errors B through E against the node files and the sources, as follows.

Step 1 uses the entire assertion of `lem-sfb-chart-exterior-derivative-square-zero`: a real-chart smooth alternating form with values in C has d(d omega)=0 at a point. I read that statement, including its real scalar field and local smoothness hypothesis. A smooth coefficient on an open chart can be defined arbitrarily off the chart without changing its germ at an interior point, so the node applies pointwise. The type decomposition of the displayed real formula gives the (0,2) component d-bar squared; this is an elementary basis computation, not a use of the parent Dolbeault resolution or its proof. I checked Demailly I §3.C (3.14)--(3.17) for precisely this decomposition.

Step 2 uses the new derivative leaf's equivalence under the hypothesis of real Frechet differentiability, which holds for a smooth function at every point of the open set. I checked its quotation against the statement and its Mathlib signature. The finite real-basis calculation A(i e_j)=i A(e_j) is written out, including passage from i to every complex scalar. The converse follows from the same equivalence, so there is no missing direction of the holomorphic-function assertion. Holomorphic on an open coordinate domain is used in its usual sense of complex differentiable at every point, consistent with Demailly's criterion in I §3.C. No separate-holomorphic-to-joint-holomorphic theorem is assumed.

Step 3 has no external lemma: openness supplies a small product of discs containing a; an empty family of q-indices means zero when q>n. I checked n=0 separately, and wrote the exact shrinking domains P^k so that later parameter domains and restrictions are well defined.

Step 4 has no external lemma: every monomial has a unique decomposition depending on whether it contains k. The coefficient of d-bar z_j wedge d-bar z_J with j>k can only come from differentiating that coefficient in j, since no coefficient monomial contains j. Thus closedness gives exactly the vanishing in those parameter directions. I compared this with the highest-index decomposition in Exercise 8.5. This is not an unstated theorem about holomorphic dependence.

Step 5 uses the full statement of `lem-sfb-cauchy-transform-parameters`, and that full statement is quoted in citations.json. I read Demailly Corollary (3.4), including its kernel normalization 1/(pi z), and Exercise 8.5's cutoff partial convolution. In the new statement all variables and integration measure are introduced, the cutoff has compact support strictly inside the source disc, and parameters are smooth on an arbitrary open subset of R^m. The integral kernel is 1/(z-zeta), with planar measure; this is the positive-sign fundamental solution. The theorem includes the commutation with every real parameter derivative and complex-linearity. Consequently the two real derivatives combine to the required parameter d-bar derivative, including its i factor. At stage k the parameter domain is open in R^(2n-2); no support condition in the parameters is needed. The operator is applied only after the relevant source disc and smaller target disc are fixed. Joint smoothness is supplied by the cited statement and not assumed from a pointwise solution.

Step 6 is the explicit induction step and endpoint: the d-bar z_k part cancels with the chosen front-wedge convention, no removed coordinate is reintroduced because of step 5, and closedness uses step 1. Subtraction and restriction are coefficient operations, so they commute with d-bar by its formula. The finite sum of all corrections telescopes on the common final product. I checked q=1 (the corrections are functions), q=n (the first residual without the highest index is already zero when appropriate), n=1, q>n, and the q=0 criterion on C^0. The base gamma_n and final gamma_0 are stated explicitly; no induction hypothesis is borrowed from the theorem itself.

Both new files are statement-only, with no proof sketch or proof dependencies. Their notion field uses are declared and the remaining spaces, derivatives, discs, support and measure are introduced inline. They are distinct analytic/derivative inputs, rather than clauses relabeled from the item. All item steps are below 2000 characters and I checked that none hides an additional comparison lemma: the only analytic construction is isolated as the transform node, and the only derivative existence comparison is the Mathlib leaf. No SGA source is used. Repository, launcher and Lean sources were read only; no agent, compiler, Lake or local preflight tool was started.

## Unfinished work

Nothing in the requested one-level split remains unfinished. The new cutoff-transform node is intentionally unsplit, ready for its own stage-1 worker. Independent maintainer review is still required after this direct delivery.
