## Worker report

Files written:

- dag/nodes/sec-six-functors-basics/lem-sfb-compact-remainder-coercivity.json: existing statement, now split into five explicit elementary steps; no exact Mathlib match.
- citations.json: the empty list, because no proof step cites another node. The existing statement dependency def-weil-field is preserved.
- report.md: this report. The searches.jsonl log was written by the prescribed msearch.py commands.

New nodes: 0. New Mathlib leaves: 0.

Attachments: none. Searches of lean/WeilConjectures for the blueprint id, compact remainder, compact/kernel, Peetre, coercivity and bounded-below/orthogonal terminology found no declaration stating this lemma. I did not treat a Mathlib declaration or a sorry declaration as a project attachment.

WANTED: Demailly, Complex Analytic and Differential Geometry, VI §2, Corollary (2.4)(ii), printed pp.289–290, for lem-sfb-compact-remainder-coercivity. The source PDF is absent locally. I read these pages online at https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf by streaming the PDF through pdftotext without saving it or changing literature/. The web page reader timed out twice; the streaming read succeeded. The missing local copy is not treated as permission to write to the repository.

What was wrong or incomplete: the item was a statement-only prerequisite isolated by NU. Its statement is correct and is unchanged. Demailly proves closed Sobolev range using compactness and a finite family of functionals in (2.5); he does not state the present abstract kernel-complement assertion as a separately numbered theorem. The delivered normalized-sequence argument is therefore marked proof_origin.by = agent. It establishes precisely the abstract assertion needed by the existing parent, without claiming that Demailly's finite-codimension subspace is the orthogonal complement of the kernel.

Unfinished work: none for this stage-1 item. No Lean was written, compiled or built.

## Sources and route

I read AGENTS.md, the worker brief and role, stages/1-dag.md, the three blueprint levels and tool-lemma rule in SETUP.md, GOAL.md, delivery-errors B–E in both copies, and the relevant tools documentation. I read the chapter record and unit record. I then read the current latest blueprint (main-20261024) unit statement and proof, and the direct-images statement and proof, especially paragraph (3). The inherited analytic prerequisite chain supports that paragraph; I do not change the unit or chapter route.

I also read the parent's delivered node and NU's report, including the abstract normalized-sequence proof. This is source material, not an attachment or a proof citation. The current blueprint itself has no separate abstract coercivity node. blueprint_refs.py ancestor reports a null nearest blueprint ancestor for this already-created chain, so I preserve the inherited from.node, exact from.place and via list. Searches of the whole DAG statement/title fields for Cauchy sequences, complete metric spaces, normed spaces, orthogonal complements and compact remainders found no duplicate of this assertion. The whole-blueprint searches for Cauchy, compact remainder and coercivity were empty; the broader bounded-below search returned unrelated derived-category nodes.

## Mathlib searches

All eight new searches were made with the required msearch.py command; every service answered successfully. The existing NU search records are retained. I used LeanFinder and LeanSearch in two phrasings, Loogle for compact operators with kernel and bound terminology, and grep of Analysis/ and Analysis/Normed/Operator/. Queries and the actual returned log records are in mathlib_searches and searches.jsonl.

I opened the candidate sources. IsCoercive.bounded_below in Analysis/InnerProductSpace/LaxMilgram.lean:53 assumes a coercive bilinear form and gives the associated Riesz operator's lower bound; the remainder estimate is not that hypothesis. ContinuousLinearMap.orthogonal_ker in Analysis/InnerProductSpace/Adjoint.lean:191 only identifies the closure of an adjoint range, and would additionally require inner product structure on F. The compact bounded-image lemmas in Analysis/Normed/Operator/Compact/Basic.lean:146 and :151 give no lower bound for T. The Fredholm-alternative theorem in Analysis/Normed/Operator/Compact/FredholmAlternative.lean:54 is about a compact endomorphism minus a nonzero scalar identity, not arbitrary T and J. The Banach closed-range theorem at Analysis/Normed/Operator/Banach.lean:383 assumes the closed range and completeness of both spaces. It does not supply this estimate under this item's hypotheses. I also read the orthogonal-intersection result in Analysis/InnerProductSpace/Orthogonal.lean:109; the delivered proof instead expands a squared norm directly.

## Not duplicates

No new nodes are created, so there are no new/existing node pairs or shared-tag pairs to distinguish. In particular I did not turn completeness, the triangle inequality, normalization, or the orthogonal squared-norm calculation into nodes.

## Review by Q98

I checked the unchanged statement against the parent and against the source's compactness/norm-estimate mechanism. Demailly (2.2)–(2.5), printed pp.289–290, supplies the motivation; the present item's assumptions already include sequential compactness and the remainder estimate. There are no new nodes with separate sources to review. There is no appeal to SGA. I opened def-weil-field, the sole statement dependency: it defines a field and supplies no analytic theorem; I take no analytic fact from it.

Step 1 uses the negation of the actual conclusion, with D=n for each positive integer. The strict failed inequality forces a nonzero vector, so division by its norm is legal. Real scalar multiplication preserves K-perp directly from inner product bilinearity. Norm homogeneity gives norm one and the 1/n bound. These are computations from the statement, not an uncited coercivity theorem.

Step 2 applies exactly the sequential definition of compact J in the statement to the norm-one sequence. Thus the subsequence converges in Z even though Z is not assumed complete. A strictly increasing positive-integer sequence has n_j >= j, so the small T-images still tend to zero. No general equivalence between compact operators and compact closures is imported from Mathlib.

Step 3 applies the given estimate to a difference, which lies in E without any additional condition, and writes every triangle-inequality term. The choice epsilon/(4C) is valid because C>0. The displayed four-term bound proves the Cauchy condition directly. I verified the constants; neither injectivity of J nor bounded invertibility of T is assumed.

Step 4 invokes completeness only of E, which is already part of the Hilbert-space assumption and means that Cauchy sequences converge. The reverse triangle inequality follows by applying the stated triangle inequality in both directions. Boundedness of T means there is a uniform M>=0 with norm Th <= M norm h; the displayed estimate proves Tu=0 without any completeness assumption on F. In particular this step does not cite a closed-range theorem or assume that K-perp is closed.

Step 5 applies the stated definition of K-perp to the actual vector u now known to be in K. Symmetry and bilinearity expand norm(u_j-u)^2 into 1+1, because the cross term is zero. A convergent sequence must eventually have distance less than 1 from its limit. This direct contradiction uses no Cauchy–Schwarz inequality, continuity of the inner product, projection theorem, closed-orthogonal-complement theorem, or non-elementary hidden comparison. The positive constant D is obtained by contradiction to its exact negation, not by weakening the conclusion.

For delivery-errors B, all mathematical notation in the edited fields uses ordinary single TeX escapes, the statement is self-contained, provenance is filled and preserved, and there are no new statement-only or leaf records to mislabel. For C, each proof step follows from the hypotheses and definitions in a few lines, and uses is empty for that reason; proof_deps and citations.json are correspondingly empty. There is no quote invented for a node that does not say the needed fact. For D, all of the argument remains in these five steps; no conclusion clause is moved into a new node and no dependency cycle can be introduced. For E, I checked the objects and hypotheses in each preceding paragraph, the normalization denominators, the Cauchy constants and the quadratic identity. Every step is under 400 characters, so no long step hides an extracted lemma.

I tested E=0 and T=0 (K-perp=0), injective T (K=0), J=0 (the original estimate already gives D=C), zero-dimensional F or Z, and noninjective J. None invalidates the argument. I also checked why compactness is essential: on real ell2, take T(x_n)=(x_n/n) and J the identity. The remainder estimate holds with C=1 but no lower bound holds on K-perp=ell2; J is not compact. Thus that hypothesis has not been silently discarded. No statement dispute or correction was needed.
