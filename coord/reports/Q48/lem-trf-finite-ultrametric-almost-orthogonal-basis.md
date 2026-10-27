## Worker report

Files written:
- `dag/nodes/sec-trace-formula/lem-trf-finite-ultrametric-almost-orthogonal-basis.json`: item split, statement unchanged, five explicit steps. Mathlib searches found no theorem choosing an almost orthogonal basis for an arbitrary given ultrametric norm.
- `citations.json`: verbatim statement excerpts for the three node citations (two definitions in step 2 and closedness in step 3).
- `searches.jsonl`: actual Q48 search records. The item's pre-existing Q36 searches and results are retained in its JSON.

No new nodes. No attachments: searching `lean/WeilConjectures/` by the item tag and by almost-orthogonal, r-orthogonal and ultrametric concepts found no project declaration of this theorem.

WANTED: Bosch–Güntzer–Remmert, Non-Archimedean Analysis, 2.6.1/3, for lem-trf-finite-ultrametric-almost-orthogonal-basis. The book is not supplied in the local literature; its argument is not represented as having been read.
WANTED: local copy of Temkin, Stable modification of relative curves, arXiv:0707.3953v3, Lemma 6.3.3, printed p. 48, for this item. The referenced local PDF is absent on this machine; I read the author's PDF at https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf directly without downloading or changing literature.

The source invokes the basis-existence result rather than proving it. I supplied an agent-written dimension-induction argument and marked `proof_origin.by = agent`. There is no statement dispute or hypothesis change. No work remains unfinished in this one-level split.

## Searches and reuse

I searched the whole DAG by ultrametric, almost orthogonal, finite-dimensional closed subspaces, normed vector space and related concepts, and read the matching statements. `tools/blueprint_refs.py search` was run for orthogonal, normed and finite-dimensional, and `ancestor` confirmed lem-trf-local-term-locality. The latest blueprint proof of that ancestor and the chapter/unit records were read; no blueprint node states the auxiliary basis theorem. The inherited provenance describes the nearby-cycle/semistable-alteration branch; it is retained, with the exact basis-existence input stated in `split_report.blueprint`.

The useful existing node is `lem-sfb-finite-dimensional-subspace-closed`, already a Mathlib leaf. Its statement allows any complete nontrivially normed field, not merely finite extensions of the l-adic field used as its example. I read its statement and Mathlib/Topology/Algebra/Module/FiniteDimension.lean:530, with the ambient hypotheses at 95–99 and completeness in scope. The other candidate, `lem-weil-pbc-finite-dimensional-linear-homeomorphism`, is unnecessary. Reusing the closedness leaf avoids a duplicate node and terminates that proof branch at Mathlib; no off-unit non-leaf tool is used.

Actual Q48 searches used two natural-language phrasings, Loogle `Module.Basis, IsUltrametricDist`, LeanSearch, and greps of Analysis/Normed and Analysis/Normed/Unbundled. I read Module.Basis.norm and norm_isNonarchimedean in Unbundled/FiniteExtension.lean:58 and 96 and the Schauder biorthogonality structure in Module/Bases.lean:98–108. The former puts a new coefficient norm on an already chosen basis, and the latter concerns coordinate functionals; neither gives the item for its prescribed norm. Inner-product orthonormal-basis hits require real/complex inner products, absent here. Completeness and closed-subspace hits supply the reused leaf, not the full basis conclusion. All queries stored in this delivery came from the search command; none was invented. The existing Q36 records were read and retained, not claimed as Q48 calls.

## Not duplicates

No new nodes were created. The existing finite-dimensional closed-subspace leaf is cited directly.

## Review by Q48

I read Temkin's Lemma 6.3.3 on printed page 48 and its reference to BGR 2.6.1/3. The displayed notion there is the same weighted maximum inequality as the item. Temkin applies it to a finite field extension; the item's general finite-dimensional vector-space formulation is the standard basis-existence input, proved here without using a multiplication on V. Completeness and nontriviality of the base field are retained. The manuscript does not supply an induction proof at that place, so I have not attributed my proof to BGR's unread argument. There are no new-node source statements to review.

For step 1 I checked the metric is separated by the zero-norm axiom, norm of negation follows from |-1|=1, and the displayed two-variable bound proves joint continuity of scalar multiplication, including at a zero vector or zero scalar. These are direct consequences of the inline norm axioms. This explicitly supplies the topological-vector-space hypotheses of the closedness leaf rather than treating them as automatic unexplained input.

Step 2 cites exactly `def-weil-finite-dimensional-subspace` for finite spanning and `def-weil-vector-space-dimension` for dimension by the cardinality of a basis. I opened both statements: neither is misused as a topological theorem. The finite-spanning-family deletion argument is written out, so no uncited basis-existence theorem is needed. Taking all but the last basis vector gives W of dimension n-1 and z outside W. The induction is quantified over every parameter in (0,1); this is why it may be invoked with s rather than r. The arithmetic identity s²-r=(1-r)²/4 checks the later loss of two factors.

In step 3 I opened `lem-sfb-finite-dimensional-subspace-closed` and copied its relevant statement into citations.json. It really asserts closedness for the complete nontrivially valued field and finite-dimensional subspace at hand. W is finite-dimensional by its displayed basis; the ambient space satisfies the continuity and Hausdorff hypotheses by step 1. Since z lies outside this closed set, an open ball separates it, giving a positive lower bound for distances. The nonempty distance set (0 belongs to W) has a real infimum. The choice is strictly above that infimum, so existence of w0 follows directly from the definition; there is no assertion that the infimum is attained.

Steps 4 and 5 cite no additional results: they are the explicit ultrametric inequalities and real inequalities written there. I checked the sign in w0-a^(-1)w, so that w+ae=a(z-(w0-a^(-1)w)). It is in W. In the unequal-norm case, the reverse ultrametric inequality forces equality, and in the other case the distance bound controls the maximum. The case a=0 is separate. Combining with the inductive lower bound gives s max(sM,B) >= s² max(M,B) >= r max(M,B). Subtracting w0 from the last basis vector preserves spanning and independence, as the direct-sum statement shows.

For the B–E checks I verified self-contained hypotheses and unchanged TeX statement; there are no new statement-only nodes to carry accidental proofs, hidden item clauses, fake Mathlib matches or duplicate tags. All non-elementary input is the cited closedness leaf; basic metric openness, real infimum properties, finite basis elimination and the displayed norm arithmetic are the elementary steps. No step exceeds 2000 characters (the maximum is under 600), and the entire proof is under 3000 characters. Tests included n=0 with the specified empty maximum; n=1 with W=0; all coefficients zero; only the last coefficient nonzero; equal summand norms where cancellation can occur; and r arbitrarily close to 1, where s<1 still leaves room for approximate minimization. The field is never assumed locally compact, discretely valued or spherically complete. No correction to the imported statement was needed. I corrected the initially tempting nearest-point formulation before writing the split, replacing it by an approximate minimizer.
