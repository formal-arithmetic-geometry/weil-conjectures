## Worker report

Files written under dag/nodes/sec-picard-framework/:

- lem-pc-finite-potent-trace-calculus.json: item, statement unchanged, now split into seven proof steps.
- lem-pc-finite-dimensional-trace-exact.json: statement, no Mathlib match; existing project declaration recorded for attachment. It has no proof steps and remains unsplit pending the attachment audit.
- lem-pc-finite-dimensional-nilpotent-trace.json: statement, Mathlib leaf via LinearMap.isNilpotent_trace_of_isNilpotent, Mathlib/LinearAlgebra/Trace.lean:351; specialize to a field and take .eq_zero.
- lem-pc-finite-dimensional-trace-cyclic.json: statement, Mathlib leaf via LinearMap.trace_comp_comm', Mathlib/LinearAlgebra/Trace.lean:265.

Also wrote citations.json, with one entry per cited node per proof step. Searches are preserved in searches.jsonl. No Lean was written or compiled. No repository or launcher file was written.

## Attachments

LinearMap.trace_eq_add_of_exact belongs to lem-pc-finite-dimensional-trace-exact, lean/WeilConjectures/RingTheory/TateResidue/FinitePotent.lean:39 (statement through line 46, proof through line 66). It states the exact finite-dimensional short-exact-sequence formula, including injectivity, surjectivity, exactness and both intertwining equations. I read the entire proof: it contains no sorry and uses only Mathlib. The new node records this existing declaration in lean_candidates, the stage-1 attachment field; I leave the closure audit to the maintainer.

The parent item cannot be attached as an exact complete statement to the existing collection of tateTrace theorems: their conclusions give the scalar identities but do not explicitly assert finite potency of the restriction, quotient, reversed composition or family sum. Its proof here supplies these witnesses. In particular, tateTrace_comp_comm states only the trace identity, tateTrace_eq_add_of_exact states only trace additivity, and tateTrace_sum states only the sum identity. IsFinitePotent.of_range_le is a generic sufficient condition, not the item's complete statement.

## WANTED

None. Tate's paper is present and was read locally.

## Problems found and changes

The item had no proof. Its imported searches already correctly distinguished ordinary Mathlib trace from finite-potent trace; those entries are retained, and actual searches under Q136 were added. No mathematical error in the statement was found. As in Tate, the assertions about one T are read with T finite-potent. The sum hypothesis includes the diagonal products T_i T_i; this is used, not silently added.

The Lean file labels its sum theorem (T3) and its exact-sequence theorem (T1), but Tate's paper labels these (T4) and (T2), respectively. All new source references use the paper's numbering: ordinary trace (T1), exact additivity (T2), nilpotents (T3), finite-potent-family linearity (T4), and cyclicity (T5).

The parent uses the canonical scalar supplied by its own construction and comparison steps; no definition with unspecified data is introduced. The proof never applies ordinary trace directly on the original infinite-dimensional space. No general additivity for arbitrary finite-potent operators is asserted.

## Not duplicates

No shared Stacks tags occur: the source is Tate §1, not a Stacks lemma. Before creating the three nodes I searched the whole DAG by the exact declaration names, trace/nilpotent/cyclic/exact-sequence concepts and statements, and searched all imported blueprint nodes with blueprint_refs.py (including trace, nilpotent, finite-potent, invariant, trace.*exact, trace.*nilpotent, trace_comp_comm and cyclicity). No existing node states any of the three ordinary linear-algebra lemmas. The broad 'cyclicity' query also matches 'acyclicity'; those matches concern sheaf cohomology, not linear trace.

- lem-pc-finite-dimensional-trace-exact vs prop-trf-trace-formal-laws: the latter fixes finite-field coefficient conventions and derived perfect complexes and restricts filtered additivity to a specified filtered origin; the new node is the ordinary exact-sequence theorem over an arbitrary field, including all intertwining maps. It also binds an existing project declaration.
- lem-pc-finite-dimensional-nilpotent-trace vs p-linear-triangular: the existing node is a full invariant-flag assertion, not the trace-zero statement for nilpotent endomorphisms over arbitrary fields.
- lem-pc-finite-dimensional-trace-cyclic vs prop-trf-trace-formal-laws: the existing conjugacy and derived trace laws do not state rectangular cyclicity for two finite-dimensional vector spaces over an arbitrary field.
- Each new node vs lem-pc-finite-potent-trace-calculus: the new nodes concern ordinary trace on finite-dimensional spaces only; none restates the infinite-dimensional choice-independence, stable-subspace additivity or family linearity clauses. The parent proves those by constructing explicit finite-dimensional spaces.

## Review by Q136

I read Tate, Residues of differentials on curves, the locally available PDF, printed pp. 149–150 (§1, (T1)–(T5) and the paragraph characterizing trace). I also read the current main-20261015 Serre-duality unit statement, its DAG unit record and chapter record. The blueprint ancestor's sentence using Tate's residue, through lem-pc-tate-dvr-residue-calculus, is the place this proof serves; no unit or chapter route is replaced. There is no SGA citation.

For the exact-sequence support node I read Tate's (T1),(T2) and the whole project theorem at FinitePotent.lean:39–66. All three spaces are finite-dimensional over the same arbitrary field, the injection and surjection are explicit, exactness is equality of image and kernel, and the two commuting equations match the node exactly. The Mathlib searches returned direct-sum identities, which are insufficient as an exact match: a chosen complement need not be invariant under the endomorphism. This is why I did not label this support node a Mathlib leaf. It is independently already proved in the project and is reported for attachment instead of being split further.

For the nilpotent support node I read Tate's (T3) and Mathlib/LinearAlgebra/Trace.lean:351–361. The Mathlib conclusion is that the scalar trace is nilpotent, and over a field a scalar whose positive power is zero is zero. This is the advertised one-line specialization, with no characteristic-zero assumption. For cyclicity I read Tate's (T5) and Mathlib/LinearAlgebra/Trace.lean:265–269 with its surrounding finite/free hypotheses: finite-dimensional vector spaces over a field satisfy both. Neither lemma assumes equal dimensions or an invertible operator.

I opened and read both existing definition-node statements. def-weil-finite-dimensional-subspace means finite spanning, and def-weil-endomorphism-trace defines the basis-independent sum of diagonal entries. Their citations below are for those notions and direct computations, not for unstated exactness or nilpotent trace theorems.

Step 1 uses those two definitions: the chosen power image is finite-dimensional by the hypothesis, and stability follows from the displayed commuting identity. Its candidate is an ordinary trace on that actual finite-dimensional image.

Step 2 uses exactly the two new statements for exact-sequence additivity and nilpotent trace zero. I checked that R lies in each comparison space, that all maps are restrictions or quotients of T, and that the displayed m-th power is zero on each quotient. Each exact sequence is finite-dimensional and its commuting conditions are automatic on vectors. Thus both applications satisfy every stated hypothesis. This proves the independence assertion rather than delegating it to a new restatement of the item.

Step 3 uses only the trace definition and step 2: take the whole space in the finite-dimensional case and zero in the nilpotent case. The zero-space trace is an empty sum, not an imported nilpotent theorem about an infinite-dimensional space.

Step 4 uses finite-dimensionality and the exact-sequence support statement. The spaces are U_0 intersect L and q(U_0), not T^n(L) identified with an intersection (those need not coincide). I verified the inclusions of the power images separately, the actual kernel and image of the restricted q, and its equivariance. The equality Tbar^n(V/L)=q(T^n V) uses the surjectivity of the quotient map. These witnesses prove finite potency before step 2 is used to identify the traces.

Step 5 takes linearity directly from summing the diagonal entries in a common basis, as the cited trace definition permits. The identity (cT)^n=c^n T^n gives the required power-image containment even when c=0.

Step 6 cites the ordinary cyclicity statement, which explicitly allows different finite-dimensional spaces. I checked a(A) lies in B and b(B) lies in A, so both restricted maps are well typed. The formula (ab)^(n+1)=a(ba)^n b gives a power of ab with finite-dimensional image, and the two compositions on A and B are precisely the restrictions whose traces are computed. No unsupported assertion that a and b are inverse maps is used.

Step 7 uses finite spanning and the matrix definition of trace. I checked stability term by term: T_l(T_i T_j x) lies in the image of T_l T_i, which is one of the assumed finite-rank products. This does not require the operators to commute. The witnesses T_i^2(V) and S^2(V) give finite potency, after which a common basis of U proves additivity by the diagonal sums. This is a short direct construction, so no extra lemma node is hidden in it.

I tested the statements and construction on the zero vector space, zero and nilpotent maps, c=0, L=0, L=V, maps between spaces of unequal dimensions, and the empty family r=0. The intersection/image proof works for an infinite-dimensional L. All arguments are valid in positive characteristic. Every cited statement is quoted verbatim in citations.json. The proof-dependency list is the union of the step uses. All seven steps are shorter than 2000 characters. The new non-leaf has a statement only; the two Mathlib leaves have no proofs. No new node is a clause of the item in disguise.

## Unfinished work

None in the one-level split. The maintainer's attachment audit is requested for the existing project proof of ordinary exact-sequence trace; no Lean compilation was run or claimed.

## Validation

The server dry run passed after adding explicit mathlib_match.line fields (351 and 265) to the two Mathlib leaves. The interrupted dry run completed successfully and saved its durable receipt at 1283acd4075. Before pushing I moved the ordinary exact-sequence attachment metadata from the maintainer-owned lean field to the permitted lean_candidates field so that delivery preserves it, and reran preflight.
