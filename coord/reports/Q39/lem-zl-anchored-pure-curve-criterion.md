# Stage-1 delivery: lem-zl-anchored-pure-curve-criterion

## Files written

- dag/nodes/sec-deligne-laumon-general/lem-zl-anchored-pure-curve-criterion.json: item, statement, split into seven proof steps; no Mathlib match for the whole sheaf criterion.
- citations.json: a verbatim statement quotation for each of the 17 step/node citations.
- report.md and searches.jsonl: review and actual searches. No new nodes; no new Mathlib leaves.

## Attachments

None. I searched the live WeilConjectures source for the exact blueprint id, anchor, logb, purity on curves, nonzero fibres and uniqueness of a pure weight. RealCurve.lean proves a mixedness assertion on curves, and DetWeights.lean discusses determinant weights on curves. Neither states this criterion for a prescribed arbitrary family and all its uniqueness clauses. The existing Sheaf theorem of the parent node is not an attachment for this item, and its sorry proof is not evidence of completion.

## WANTED

None. The item's own source is present. No SGA route is used.

## Corrections and scope

The statement is retained verbatim. The only statement-dependency addition is def-wf-positive-real-logarithm for the already present logarithmic formula. The item was unsplit, with no saved sandbox node, report or search log when this continuation began. There was no active deliver.py process. The prior searches in the repository node are retained; actual searches in this session are additionally logged and recorded. The two semantic phrasings, Loogle and grep found no Mathlib theorem for this geometric assertion. The grep hits on logb_rpow/logb_pow are analytic primitives, covered by existing real-power/logarithm nodes and insufficient for attaching the whole item.

The blueprint paragraphs suppress nonemptiness of the anchor spectrum, nonvanishing and the cancellation of the residue degrees. These are now explicit. I did not duplicate an analytic normalization lemma or a lisse positive-rank lemma: the existing coefficient-field fibre equivalence reflects the zero object, the existing eigenvalue leaf produces an eigenvalue, and the logarithmic cancellation is a written elementary step. I did not cite the parent two-point criterion, which would be circular.

## Unfinished

None for this one-level stage-1 split. All proof citations exist. No Lean was written or compiled, and no repository or launcher file was changed.

## Not duplicates

No new nodes. I searched DAG statements for constant/positive rank, nonzero stalks and eigenvalues, logarithmic weights and power injectivity, and the whole blueprint via blueprint_refs.py search for purity, logarithm, eigenvalue and fixed. The generic eigenvalue and logarithm facts were already present and are reused.

## Review by Q39

I read the current main-20261015 thm-zl-real-mixed-by-curves.proof.md paragraphs 3-4, the chapter and sk-i-dl-general-real unit route, and the parent's criterion interface. The item is precisely the anchor comparison used there. Its hypotheses already assume the two-point coverage and exact local eigenvalue powers, so this proof does not need Bertini or a new Frobenius-comparison theorem. No source error or statement dispute was found.

For step 1 I opened each of def-pc-geometrically-irreducible, lem-pod-separated-finite-type-base-change, lem-weil-pbc-finite-type-over-noetherian, cor-galois-lisse-representations, lem-zl-alg-closed-endomorphism-eigenvalue and def-weil-local-frobenius-trace. The first makes the geometric fibre connected. The next two ensure the geometric fibre is separated and Noetherian, with the base field Noetherian because its only ideals are 0 and 1. The invertibility of ell follows from ell different from the characteristic. Thus clause (2) of the fibre equivalence really applies to the classical lisse Qlb sheaf on that fibre. An equivalence reflects zero, so the nonzero sheaf has a nonzero finite-dimensional anchor fibre. I checked the eigenvalue leaf states existence for an arbitrary endomorphism of just such a vector space, without an irreducibility assumption. Invertibility of the local Frobenius operator is read from its specified composite of isomorphisms, and applying its inverse rules out eigenvalue zero. This avoids assuming that a definition supplies a separate rank theorem.

For step 2 I opened lem-kun-closed-point-field: its part (a) gives finiteness of the residue field over k_0 at every closed point in question. A finite basis gives a bijection with a finite Cartesian power of k_0; 0 and 1 are distinct, so q_x is at least 2. The separate logarithm node says log(q_x)>0 for q_x>1. These verify every denominator before it is cancelled.

For step 3 I opened the full statements of def-weil-punctual-weights, def-weil-complex-absolute-value, def-weil-real-power and def-wf-positive-real-logarithm. Purity gives precisely the displayed modulus equality at z; hypothesis (iii) supplies the powered eigenvalue, not an unrelated pullback theorem. Multiplicativity of the norm and the field embedding gives a^f; the real-power node supplies positivity and the exponential formula, and the logarithm node explicitly says log(exp s)=s. Consequently log(b^t)=t log b is a direct substitution in those statements. Cancelling f and log q_x uses f>=1 and step 2. All uses are statements, not content of their proofs.

Steps 4 and 5 instantiate that calculation: coverage with x=x_* supplies a first curve and avoids an empty-family loophole; every anchor eigenvalue gets the same formula on that one curve; the single chosen anchor eigenvalue compares all other supplied or further curves. No claim that different powered eigenvalues remain distinct is used. These steps cite no new facts.

Step 6 uses the statements of lem-a1-real-logarithm-power and def-weil-punctual-weights, both opened: the former says b^(log_b a)=a for b>1,a>0, exactly the inequalities proved in steps 2-3, and the latter requires all closed-point eigenvalues. The curve through x and x_* has weight w by step 5. Step 7 uses the same definition and the real-power and logarithm identities to prove uniqueness from the existing anchor eigenvalue; it does not assume every sheaf has a unique weight, which would fail for zero sheaves.

I checked delivery-errors B-E against the files. The statements and definitions are self-contained; citations.json quotes the actual portions used. No new statement-only nodes or unrun searches are present. No step hides the criterion in a renamed lemma, and every non-elementary assertion is a cited node. The two off-unit generic tools cor-galois-lisse-representations and lem-kun-closed-point-field are explained in split_report.tool_uses; they do not replace any curve argument of the unit. The remaining off-unit results are Mathlib leaves or definitions. The longest step is 980 characters, so no non-elementary step exceeds 2000 characters.

Small cases checked: rank one; several anchor eigenvalues of equal modulus; coinciding eigenvalues after powering; e and f greater than 1; x=x_*; additional curves outside the collection; and nonsimple lisse sheaves. No semisimplicity, irreducibility or equality of residue degrees is assumed. If S were zero the claimed uniqueness would be false, which explains and uses the stated nonzero hypothesis. If the geometric fibre were disconnected that same issue could occur on an anchor component, which is why the connected-fibre equivalence is applied only after geometric connectedness. A zero-dimensional nonempty X_0 cannot contain the required closed curve through the anchor, so hypothesis (i) is unsatisfiable there and creates no counterexample. The empty family is ruled out by (i) at x_*. The smallest possible residue size 2 still has positive logarithm. I preserved all source/import/creation metadata and wrote only in this sandbox.
