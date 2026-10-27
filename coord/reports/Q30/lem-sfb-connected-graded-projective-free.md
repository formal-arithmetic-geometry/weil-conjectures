# Stage-1 delivery: lem-sfb-connected-graded-projective-free

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-connected-graded-projective-free.json`: existing item, statement unchanged, five proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-graded-nakayama-connected.json`: one new statement-only lemma, no Mathlib match, status unsplit.
- `citations.json`: a verbatim statement quotation for each citation in steps 2, 3 and 4.

There are one new node and zero Mathlib leaves. The earlier unpublished graded-splitting node was removed after self-review: it was unnecessary because an ungraded section gives the required finite-kernel calculation directly.

## Attachments

None. Searches by item tag and by connected/graded/projective/homogeneous-basis concepts found no project declaration stating the general item. I read the live declarations `MvPolynomial.graded_nakayama_free`, `MvPolynomial.graded_nakayama_generation`, and `MvPolynomial.exists_graded_free_cover`: they concern the two-variable polynomial ring and do not establish the item for an arbitrary connected graded algebra. The new prerequisite likewise has no declaration for arbitrary A. No sorry declaration is treated as a finished proof.

## WANTED

None. Both source passages are present in `literature/stacks-project/algebra.tex`.

## Statement and blueprint audit

The item statement and its statement dependencies are preserved. It is a genuine consequence of the cited results and needs neither Noetherianity nor finite type of A. Its only immediate parent, `lem-sfb-polynomial-graded-hilbert-syzygy`, needs exactly this homogeneous basis for its terminal finite projective syzygy; that use remains valid.

I read GOAL.md, the three levels in SETUP.md, the worker brief, the chapter and unit records, and the newest blueprint at `literature/blueprint/latest/`, including `sk-thm-sf-ctf-stability/_section.md` and the direct-images proof. The item's existing provenance records the inherited GAGA/Kodaira/Hilbert-syzygy supporting branch of direct-images proof (3); it is not a literal lemma of that blueprint. The ancestor command reports `blueprint.from.node = None` for a node created for this item, matching the item's inherited null ancestor. The new node keeps that ancestor and prepends the item to the inherited via list. Its precise place identifies the two uses of Tag 0EKB. Blueprint searches for `0EKB`, `Nakayama`, `homogeneous basis`, `graded projective`, and the combined graded-splitting terms gave no blueprint node stating this prerequisite. The Nakayama hits concern derived completion, not graded modules.

## Not duplicates

lem-sfb-graded-nakayama-connected vs lem-sfb-connected-graded-projective-free: the new lemma asserts generation from a positive-ideal quotient and vanishing when that quotient is zero for any finite graded module; it assumes no projectivity and concludes no homogeneous basis. The item proves freeness of finite ungraded-projective graded modules by applying these two clauses around the explicit split-kernel calculation.

lem-sfb-graded-nakayama-connected vs lem-sfb-polynomial-graded-hilbert-syzygy: both source records cite 0EKB, but the existing statement is a bounded finite shifted-free resolution over a polynomial ring. It neither states nor implies the new assertion for an arbitrary connected graded algebra.

lem-sfb-graded-nakayama-connected vs lem-sc-p1-graded-nakayama-generation: the existing statement is restricted to k[x_0,x_1] with its standard grading; the new one allows any nonnegative connected graded algebra, including non-Noetherian algebras and algebras with relations or generators in higher degrees.

lem-sfb-graded-nakayama-connected vs lem-sc-p1-graded-nakayama-free: the existing lemma concerns Tor_1 vanishing and homogeneous freeness over k[x_0,x_1]. The new lemma concerns generation and vanishing for arbitrary finite graded modules over arbitrary connected graded algebras, with no Tor or projectivity assumption.

## Review by Q30

I read Stacks `algebra.tex`, section-graded and `lemma-graded-NAK`, in full. The tags table identifies it as 0EKB. Its parts (4) and (1) give exactly the new node's generation and zero-module clauses. The connected hypothesis identifies quotient scalars with k (and the zero algebra, if allowed, has only the zero unital module). I also read `definition-projective` and `lemma-characterize-projective`, the latter identified in the tags table as 05CF. The proof obtains a section of a free surjection by projectivity. The existing definition node `def-weil-pbc-projective-module`, which I read in full, explicitly states the lift-along-every-surjection formulation, so step 3 may use it directly. This is not a theorem being inferred from an unrelated definition.

Step 1 is an explicit finite construction: replace finitely many module generators by their finitely many homogeneous components; reduce coefficients modulo the positive-degree ideal; then retain a vector of the resulting finite spanning list precisely when it is outside the preceding span. This gives independent homogeneous residue classes still spanning the quotient and gives their homogeneous representatives. No general homogeneous-basis theorem is hidden here. The zero module is handled first. For P nonzero the algebra is nonzero, and k embeds in it, so the degree-zero scalar identification used next is valid.

Step 2 applies clause (1) of the new node to those lifts. Its finite-generation and grading hypotheses are exactly those of the item. The source free module is constructed coefficientwise as the finite direct sum of A(-e_r), so its grading and scalar compatibility follow from those of A. I wrote out the quotient injectivity calculation: q(sum a_r u_r) in IP forces every degree-zero coefficient (a_r)_0 to vanish by the independence of the residue basis. Thus q^{-1}(IP)=IF, and there is no appeal to an uncited tensor-exactness theorem.

Step 3 takes the lifting clause stated in `def-weil-pbc-projective-module`, lifts the identity along q, and defines h=1-sq. The equations qh=0 and h|K=1 give finite kernel generators h(u_r) directly. No finite-kernel theorem over a Noetherian ring is used. Separately, degree preservation of q and internality of P show that every homogeneous component of a kernel element remains in the kernel, so K inherits the internal grading and the scalar compatibility needed by the next step. Neither the section nor h needs to preserve degrees.

Step 4 proves K=IK before invoking clause (2) of the new node: each x in K lies in IF by step 2, so applying h to an expression x=sum a_n f_n with a_n in I gives x=sum a_n h(f_n) in IK. The reverse inclusion follows from K being a submodule. Step 3 supplies both finite generation and the compatible internal grading of K. The new node therefore says exactly what this use requires; citations.json quotes its zero-module clause verbatim.

Step 5 proves the inverse is graded, rather than merely asserting it: decompose a preimage of a homogeneous target element; all components in other degrees have zero image, hence vanish by injectivity. It verifies the shift sign A(-e)_b=A_{b-e}, the homogeneous basis, and the empty-family case. Each non-elementary step is shorter than 2000 characters and all its non-elementary facts are cited. The proof-dependency list is exactly the union of the uses lists; the new node has no proof steps or proof dependencies, so no cycle is introduced.

I checked small cases explicitly. For A=k with arbitrary finite integer-graded P, the construction is the ordinary degreewise vector-space basis. For P=A(-e), including negative e, the single basis vector is in degree e and the displayed shift sign agrees. P=0 gives the empty family. For A=k[t]/(t^2), P=A works although A is nonregular; the module k is not projective, as a section of A to k would require an element congruent to 1 annihilated by t, which does not exist. For the new lemma, M=k with t acting by zero and lifts of its scalar basis satisfies its first clause without any projectivity. The infinite polynomial algebra k[t_1,t_2,...] with positive degrees is also covered; the finite-retraction argument never assumes its ideals or arbitrary submodules are finite. Dropping finite generation would break the new lemma: k[t,t^{-1}] over k[t] is a nonzero graded module with tM=M, and is correctly excluded.

I checked the new node against delivery-errors B1-B10: it introduces its objects and grading explicitly, uses inline descriptions and the field/finiteness definitions, has statement-only status, correct TeX, the verified Stacks label and tag, a searched blueprint reference, and actual logged searches. I read the Mathlib candidates in `RingTheory/GradedAlgebra/FiniteType.lean`, `RingTheory/GradedAlgebra/Homogeneous/Ideal.lean`, and `RingTheory/Nakayama.lean`. The first supplies homogeneous algebra generators, not module generation from a quotient; the second supplies the irrelevant ideal, not graded Nakayama; ordinary Nakayama requires a Jacobson-radical hypothesis which the item does not have (for example (t) in k[t]). They are not matches. I ran a second semantic phrasing of the graded-vanishing question, valid Loogle name-pattern searches, and both focused and whole-Mathlib grep searches. The exact wrapper records are in the item's searches.jsonl and the new node's mathlib_searches. The initial draft's searches under the wrong item ID were rerun under the delivery item; only correctly logged queries are recorded in the final new node. No service failure is recorded as absence.

Against C1-C8, D1-D5 and E1-E7, I verified the actual statement quotations and hypotheses step by step as above, avoided a redundant graded-splitting lemma, retained a real proof of the item, and checked the kernel argument over non-Noetherian and nonregular examples. The new lemma is a smaller general tool, not a clause of projective freeness. No source error or statement dispute was found, no target statement was weakened, and no SGA source is cited. The only off-unit proof citation is the existing definition of projectivity, so no off-unit theorem tool use is needed.

## What remains

Nothing required for the stage-1 split remains beyond the required dry run and push. The new graded Nakayama lemma is intentionally unsplit for a later worker. No Lean file was written and no compiler, Lake or build command was run.
