# Stage-1 worker report: cor-coef-integral-internal-hom

1. Files written: `dag/nodes/sec-six-functors/cor-coef-integral-internal-hom.json` (existing statement, split; not a Mathlib leaf), `citations.json`, and this report. No new nodes and no unit changes. The wrapper-generated `searches.jsonl` records the actual Mathlib searches.
2. Attachments: none. `AlgebraicGeometry.Etale.boundedConstructibleIntegral_derivedHom` is at `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/SixFunctors/Etale/Derived/IntegralCoefficients.lean:271`; its body at lines 294–295 contains two `sorry`s and invokes the sorried reduction theorem at lines 197–204. It is not finished. The source file explicitly realizes integral coefficients as discrete coefficient sheaves on the small etale site (lines 35–43), whereas this DAG's integral category uses the completed coefficient sheaf on the pro-etale site. Even the sorry-free `AlgebraicGeometry.Etale.derivedComplete_derivedHom` at line 211 supplies only one clause, in that different setting. Neither is an attachment for this item. Searches by blueprint id and by internal-Hom/coefficient keywords found no complete matching project declaration. The exact upstream master was searched read-only and supplies no attachment evidence.
3. WANTED: none. The repository does not contain the untracked blueprint files locally, but the same literature is available read-only in `/home/ubuntu/weil-launcher-nt/literature/`; all blueprint passages cited below were read there. No download was made.
4. The imported item had no statement dependencies and one compressed proof paragraph. I made its implicit global conventions explicit using the chapter, its biduality unit, the completed-integral and constructibility definitions, and the original blueprint. The resulting statement retains the integral pro-etale category, the canonical reduction assertion, and exactly `[c-b-2d,e-a+2d]`. The statement's separated finite-type scheme context is that of the unit and chapter, not an added perfectness or smoothness condition. Tor intervals are measured over each finite quotient, not after restricting scalars to R. There is no established statement dispute against the source's context. The Lean declaration's different coefficient category is reported rather than silently identified with it.

   The expansion also makes explicit two inferences hidden by “remaining conditions”: a dimension bound exists even before one is supplied for the quantitative assertion, and a uniform finite-level Tor interval bounds the ordinary cohomological supports. Both use existing statements or an explicit tensor-unit calculation. The original residue-Tor / Hom reduction / finite-Hom route is retained; the biduality unit and chapter are not changed.
5. Unfinished: none at this split level. The original three mathematical inputs remain cited DAG nodes, rather than being re-proved here. No Lean code was written and no compiler or Lake command was run.

## Sources and searches

Read the master blueprint item in full, its chapter and `sk-prop-sf-biduality-general/_section.md`, and the original source files of `lem-coef-integral-hom-reduction`, `lem-coef-integral-residue-tor`, `cor-weil-finite-constructible-hom`, and `def-weil-derived-complete-integral-detailed`. Also read `lem-kun-dimension-finite-type.md` and the current DAG statements of every cited definition. The dimension lemma's current split, rather than the less careful original proof, is the black box here. The item's proof is marked agent-authored because its route follows the agent-written blueprint.

Whole-blueprint searches for “integral internal Hom”, “constructible internal Hom”, “integral Hom”, and “Hom reductions”, plus whole-DAG searches by the item id, coefficient notions and dimension notions, found the original inputs and existing dimension lemma. No existing imported node was found stating this entire result in another form, so `blueprint.same_as=[]`. As this is itself an imported node, its `blueprint.from` correctly remains null. No duplicate node is created.

The required wrapper ran LeanFinder twice with distinct mathematical phrasings, Loogle twice, whole-Mathlib grep and a second homological-algebra grep, and LeanSearch once. The hits concern abstract derived-category truncation and localization, local cohomology, condensed-module structure, or constructible topological subsets. They supply no constructible integral pro-etale internal-Hom theorem or dimension-dependent reduction interval. LeanSearch returned an Internal Server Error, recorded as unavailable. The exact tool names and query texts, including the second phrasings, are copied from the wrapper log; no unrun search is recorded.

## Review by Q05

I read delivery-errors B–E in full and compared the revised JSON with the sources and current cited statements. This is the author's self-check, to be followed by the required independent second reader.

Step 1 uses the definition of the actual integral category to obtain derived completeness and bounded constructible residue reductions, and uses `lem-coef-integral-residue-tor` for exactly its asserted implication from residue cohomological bounds to one Tor interval at every finite level. I checked that the valuation ring is that of a finite extension of Q_l, that the site is pro-etale, that reductions are over the completed coefficient sheaf, and that l is invertible on X. No ordinary finite-stage constructible complex is asserted to have finite Tor dimension merely because it is constructible. The intervals are chosen separately for the two integral objects and are independent of n.

Step 2 uses precisely the two clauses of `lem-coef-integral-hom-reduction`: the evaluation-defined canonical comparison for arbitrary ambient complexes and completeness when the second input is complete. Its statement explicitly excludes a site-perfectness requirement. The lemma's source proof specifies that the comparison is A_n-linear, and its displayed statement identifies the actual reductions with finite-coefficient internal Homs. I did not use the sorried discrete-etale Lean analogue as a pro-etale theorem and did not need an evaluation-compatibility assertion beyond the cited comparison.

Step 3 uses `lem-kun-dimension-finite-type`, whose entire statement is that a finite-type scheme over a field has finite Krull dimension. I checked that the source's `kundim` is the same chain-of-irreducible-closed-subsets dimension, using `def-kun-topological-krull-dimension` and the dimension definition. Passing from a finite nonnegative dimension to an integer upper bound is elementary. The empty scheme has dimension minus infinity and permits d_0=0. This generic geometry theorem is declared as an off-unit tool in `split_report.tool_uses`; no lemma of the biduality unit states dimension finiteness. It neither replaces the unit route nor introduces any coefficient hypothesis.

Step 4 uses the current full statement of `cor-weil-finite-constructible-hom`, including its pro-etale clause and the precise Tor interval. I checked every hypothesis: the global algebraic closure of the finite field, the separated finite-type scheme, the finite quotient A_{E,n} for positive n, l different from p, the finite-level input constructibility, both finite Tor intervals, and the fixed dimension upper bound. Its conclusion states both bounded constructibility and the uniform formula, so there is no use of an argument hidden in its proof. Substituting alpha,beta,gamma,epsilon,d_0 establishes membership, while substituting arbitrary a,b,c,e,d proves the quantitative clause, without confusing a chosen existential interval with the claimed one. The reduction isomorphisms in step 2 identify the outputs in the same A_n-module category.

Step 5 is the elementary assembly, using the actual Tor-amplitude definition, the K-flat definition of derived tensor, and the integral category definition. I wrote both directions of the degreewise tensor-unit isomorphism and checked their compatibility with the differential. Thus taking the module sheaf A_n in the Tor test really bounds H_n itself. This is a two-line computation from the cited definitions, not an unmentioned preservation theorem or a new node. Completeness, finite-level constructibility, and one n-independent cohomological interval are exactly all the integral definition's conditions. The inequality u<=v follows from alpha<=beta, gamma<=epsilon and d_0>=0.

For C4, `citations.json` has one entry for every (step, cited node) pair, with quotes copied verbatim from the node statements. Whole statements are quoted when multiple clauses or hypotheses are used, so no formula was invented to make a citation fit. For C1 and D, every substantive input is one of the three original cited lemmas or the existing dimension theorem; the few remaining inferences are stated explicitly. No auxiliary node restates the item, a clause of it, or a short elementary computation. A read-only dependency traversal found no path from any of those four theorem inputs back to this item; the delivery preflight also checks cycles and the route.

I tested the empty scheme, either input zero, a geometric point (d=0), shifts of the coefficient unit, and the torsion input R/(varpi). At a point and for shifts K=R[-r], L=R[-s], the formula gives [s-r,s-r], as it should. For K=R/(varpi), its derived finite reductions occupy degrees [-1,0], so using [0,0] would be invalid: the output estimate correctly permits degree 1 for RHom_R(R/(varpi),R). This test checks that no underived dual or site-perfectness assumption was substituted. Enlarging an input interval or d only enlarges the output bound. The zero and empty cases require no nonempty-support assumption. All n in the statement are positive; no zero quotient level is used.

No new nodes exist, so B's new-node layout, Stacks-tag provenance, Mathlib-leaf line-number and duplicate-pair obligations are vacuous. The existing item's JSON keeps the import metadata and uses ordinary single-escaped TeX. The source references retain the exact blueprint document and proof sentence served. No human target, definition, unit realization or live file was edited.

## Second reading by Q05

Step 1 checked against `def-weil-derived-complete-integral-detailed` and
`lem-coef-integral-residue-tor`: the derived-complete hypotheses, residue
cohomology intervals, invertibility of `ell`, and finite-level Tor conclusion
match; verdict pass.

Step 2 checked against `lem-coef-integral-hom-reduction` and the completed
coefficient/reduction definitions: it uses exactly derived completeness and the
evaluation-defined reduction isomorphism, with no site-perfectness assumption;
verdict pass.

Step 3 checked against `lem-kun-dimension-finite-type` and
`def-kun-topological-krull-dimension`: finite-type dimension, the empty-scheme
case, and the nonnegative integer bound are handled; verdict pass.

Step 4 checked against `cor-weil-finite-constructible-hom`: the pro-etale,
finite-type, coefficient, Tor-interval, and dimension hypotheses are all in
force, and the supplied quantitative intervals are substituted literally;
verdict pass.

Step 5 checked against `def-weil-proetale-tor-amplitude`,
`def-weil-derived-tensor`, and `def-weil-derived-complete-integral-detailed`:
the tensor-unit calculation gives the required cohomological interval and the
three defining integral conditions are assembled; verdict pass.

No new nodes were introduced, so there are no new-node statements to review.
The statement was compared clause by clause with the master blueprint's
`sec-six-functors/sk-prop-sf-biduality-general/cor-coef-integral-internal-hom.md`,
its unit `_section.md`, and the completed-integral definition in
`sec-smooth-purity/sk-def-sf-operations/def-weil-derived-complete-integral-detailed.md`.
The separated finite-type context is the unit's context; the reduction is in the
finite-coefficient category and the Tor interval is exactly the source's.
I also opened the three original lemma/corollary blueprint files and the dimension
lemma's source. These sources are blueprint passages, not Stacks-tagged new
lemmas; the cached copies under `/home/ubuntu/weil-launcher-nt/literature/` were
read without modification.

All nine citation records equal the entire current cited statements verbatim.
An independent traversal of statement and proof dependencies from the four
non-definition inputs reaches no path back to this item. On the empty scheme,
all objects are zero and `d_0=0` works. With either input zero, any enclosing
interval works. At a geometric point, coefficient units concentrated in degrees
`r` and `s` give internal Hom in degree `s-r`, agreeing with the interval formula
when `d=0`. For the torsion input `R/(varpi)`, its derived residue has degrees
`[-1,0]`, so the possible degree-one dual is included. Level `n=1` is valid and
`n=0` is excluded consistently with all definitions.

Changes: corrected the first worker's Lean-body line reference from 297–298 to
294–295 after reading the actual source; no mathematical or citation content
needed repair. Added this independent second-reading record. The literal trailing
`.` in the requested delivery command is rejected by this launcher's argument
parser, so the same required tool is invoked with its documented two positional
arguments and `--no-push`, then without that flag for delivery.
