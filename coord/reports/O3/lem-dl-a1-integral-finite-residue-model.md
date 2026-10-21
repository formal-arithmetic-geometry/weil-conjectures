# O3 stage-1 delivery: lem-dl-a1-integral-finite-residue-model

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-integral-finite-residue-model.json`: existing statement, now split into seven proof steps; not a Mathlib leaf. The statement and original metadata/searches are retained verbatim. Five actual searches from this run are appended, including a second semantic phrasing.
- `citations.json`: six entries, one for each step-node citation, quoting the actual existing statements verbatim.
- `report.md`: this report. `write_split.py` is a sandbox-only preparation script; `searches.jsonl` is the search command's unmodified log.

New nodes: 0. New Mathlib leaves: 0. All six proof dependencies are existing Mathlib leaves. No unit record is changed: the item is not the unit's key statement.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag, the item ID, integral-model/finite-residue terminology, and combinations of subalgebra, residue and prime separation found no project declaration stating the item. Unrelated integral models and finite-residue lemmas do not provide all clauses. No Lean file was written and no compiler, Lake or build command was run.

## WANTED

None. All sources read are already in the shared repository.

## Problems and changes

The imported item has no false assertion or missing hypothesis. Its proof was empty. The source's first proof of Tag 0BSR first localizes the base and uses Chinese remainders to obtain simultaneous residue representatives. The item's source explicitly asks for the numerator/denominator variant, so the delivery writes that variant fully: representatives for a finite spanning family of each supplied field, together with pairwise prime-separating elements. This keeps the original base ring and realizes exactly the same finite-intermediate-algebra reduction. Separability of the supplied fields is a legitimate unused hypothesis of this slightly more general elementary construction; it is retained.

No statement was weakened or changed. No new node merely restates a conclusion. The statement's existing pure-inseparability definition dependency is retained. Finiteness and fraction notation have their usual algebraic meanings as in the source; the proof explicitly gives the generators, quotient injections, fraction maps and finite spans.

## Not duplicates

No new nodes were created, hence there are no new/existing tag pairs to distinguish. Whole-DAG searches found and reused `lem-sc-finite-generated-integral-subring` rather than creating another finite-integral-adjoin lemma; `lem-weil-pbc-finite-of-integral-generators` is another available form. The two existing incomparability nodes are equivalent; the delivery cites the fully stated `lem-weil-pbc-integral-incomparability`. Existing finite-subalgebra fraction-field nodes impose different bases/field extensions and do not replace this item's finite fibre assertion.

Blueprint searches with `tools/blueprint_refs.py search` for finite subalgebra, residue subfields, separating primes, incomparability and integral generators found no blueprint node stating this whole item. The incomparability search found `pqf-lem-incomparability`, confirming the already existing tool. `ancestor` gives `rem-dl-a1-conventions`, as already recorded in the item. I read the current `main-20261015` convention node, the chapter record and the `sk-d-dl-a1-setup` unit. The tool lies below their boundary-inertia reduction and changes no chapter or unit route.

## Mathlib searches and source reads

The pre-existing six search records came with the repository item and have been retained. The unmodified sandbox log records five fresh searches, all actually executed: LeanFinder twice with different full-item descriptions, Loogle `Algebra.IsIntegral, Subalgebra, Module.Finite`, LeanSearch with the full intermediate-algebra question, and grep `finite.*adjoin|exists.*subalgebra|residue.*[Ss]eparab` in `RingTheory/IntegralClosure`. All services answered. None supplies the item in one line: finite adjoin supplies only one construction property, and quasi-finite residue fields supply only a field-degree assertion; universal etale factorization changes the base.

I read the finite-adjoin theorem at `Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean:226`, the finite-dimensional-domain field construction at `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean:496` and `:525`, incomparability at `Mathlib/RingTheory/Ideal/GoingUp.lean:221`, and lying over at `Mathlib/RingTheory/Spectrum/Prime/Topology.lean:1226`. Their statements agree with the existing leaf statements used here. Related integral-over-a-field source was also inspected; it is not passed off as an exact whole-item match.

## Review by O3

I read the item against `literature/stacks-project/more-morphisms.tex`, Tag 0BSR (`lemma-etale-makes-integral-split`), the entire first proof. Its finite intermediate algebra must retain both distinct fibre primes and the separable residue subfields. The new steps carry those arguments, rather than putting the conclusion into an unsplit helper. I also read Algebra Tags 00GM (`lemma-characterize-integral`), 02JJ (`lemma-characterize-finite-in-terms-of-integral`), 00GT (`lemma-integral-no-inclusion`), 00GQ (`lemma-integral-overring-surjective`), and 00GS (`lemma-integral-over-field`, including its first assertion and proof). No new nodes need independent source justification. No prohibited SGA source is used.

For step 1 I opened `lem-weil-pbc-integral-incomparability` and checked the exact incomparable-primes conclusion. It applies to the given integral map without injectivity or Noetherianity; each pair consists of distinct primes with exactly the same contraction. The chosen witness lies in the first prime and outside the second, which will distinguish contractions in the generated ring.

For step 2 I opened `def-weil-finite-dimensional-subspace`: it defines a finite spanning family, precisely what is chosen. Each family element is already in the stated fraction field, so its numerator and nonzero denominator lift from the quotient by definition. There is no lifting of a residue tuple or of an idempotent, and no primitive-element theorem or Chinese remainder theorem is hidden here. The step is elementary and spells out the construction.

For step 3 I opened `lem-sc-finite-generated-integral-subring`, whose statement supplies the finiteness of the algebra generated by a finite set of integral elements. Its hypotheses are the commutative A-algebra D, the actual finite union T, and integrality of every chosen element, all provided. This gives the required finite A-module directly; no faithful A-action is assumed. The empty generating set is included in the theorem and gives image(A).

Step 4 has no black-box citation: each original monic relation still has its coefficients in C, so D is integral over C. The argument for primality of contraction is stated, and the pairwise witnesses remain inside C. This is a direct application of definitions, not an appeal to transitivity or to a theorem about a different map.

For step 5 I opened `lem-weil-pbc-integral-injective-lying-over`. Its required injectivity is that of the actual subring inclusion C into D, never that of A into D. Its integrality comes from step 4. Composing contractions shows that the lifted prime is on the complete given list. This establishes all primes of C over p, and the separate distinction proves injectivity. If the list is empty, the same argument rules out any C-prime over p.

For step 6 I opened `lem-weil-pbc-finite-dimensional-domain-is-field`. The step constructs the finite-dimensional k-algebra to which it is applied: the k-span of images of finite A-module generators in E_i. It contains 1 and all images of C; products of generators remain in the span because C is an A-module generated by those elements. It is nonzero and a domain as a subring of E_i. Thus the cited node really gives it a field structure, not just algebraicity. The step writes both inclusions identifying this field with Frac(C/s_i), after checking the quotient and fraction injections and the injective map A/p into C/s_i. No non-elementary base-change or residue-degree theorem is left uncited.

For step 7 I opened `def-weil-pbc-finite-purely-inseparable-extension`; despite its ID its statement defines pure inseparability without requiring finiteness. The actual quotient denominators are nonzero at s_i, so the spanning elements lie in L_i and all of F_i follows by k-linearity. In positive characteristic the same power used for F_i lies in L_i; in characteristic zero E_i=F_i forces E_i=L_i. This is the definition with an explicit containment argument and warrants an elementary step.

I checked B through E of `coord/delivery-errors.md` against the files. The six citation quotes are copied from the statements, never their proofs, so C4 can be independently checked by the delivery gate. Every non-elementary input has a node, including finite-dimensional-domain-is-field and lying over, addressing C1. There is no self-reference or dependency on the parent split. All proof tools are pre-existing Mathlib leaves, so no off-unit unsplit tool needs a route exception. Every step is below 2000 characters (maximum 1159), and none hides a comparison or identification behind “clear denominators”.

Small cases checked: t=0, including D=0 and the case where the kernel of A to D excludes p from the image of Spec(D); t=1 with no separators; A a field with D a finite product of extensions; noninjective A to D; characteristic zero, where E_i/F_i is equality; positive characteristic with infinite purely inseparable E_i/F_i; and trivial F_i=k. None requires D finite, reduced, a domain, or Noetherian. In the nonempty fibre, the quotient C/s_i is a domain but C need not be. The characteristic and dimension assumptions are used on the stated fields, not on the whole rings. No corrections to the imported statement were needed.

## Unfinished work

None at stage 1. Validation and delivery results follow below once the required remote commands finish.
